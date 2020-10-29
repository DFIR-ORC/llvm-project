//===--- StronglyTypeHRESULTCheck.cpp - clang-tidy
//-----------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

//#define VERBOSE

#include <iostream>

#include "StronglyTypeHRESULTCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Support/ConvertUTF.h"
#include "llvm/Support/raw_ostream.h"

#include <assert.h>
#include <regex>

using namespace clang::ast_matchers;

namespace {

#ifndef VERBOSE

template <typename T> void Dump(const T *t, std::string msg = "") { return; }

#else

template <typename T> void Dump(const T *t, std::string msg = "") {
  if (msg.size()) {
    msg.append(" - ");
  }

  if (t == nullptr) {
    std::cerr << "[I] " << msg << typeid(t).name() << "IS NULL" << std::endl;
    std::cerr << std::endl;
    return;
  }

  std::cerr << "[I] " << msg << typeid(t).name() << std::endl;
  t->dump();
  std::cerr << std::endl;
}

#endif // VERBOSE

std::string ReplaceAll(std::string s, const std::string &oldSub,
                       const std::string &newSub) {
  std::string::size_type n = 0;

  while ((n = s.find(oldSub, n)) != std::string::npos) {
    s.replace(n, oldSub.size(), newSub);
    n += newSub.size();
  }

  return s;
}

const clang::DeclRefExpr *GetFirst_DeclRefExprClass(const clang::Stmt *stmt) {
  if (stmt == nullptr) {
    return nullptr;
  }

  if (stmt->getStmtClass() == clang::Stmt::DeclRefExprClass) {
    return llvm::dyn_cast<clang::DeclRefExpr>(stmt);
  }

  for (auto child = stmt->child_begin(); child != stmt->child_end(); ++child) {
    return GetFirst_DeclRefExprClass(*child);
  }

  return nullptr;
}

uint64_t GetTupleElementIndex(const clang::CallExpr *callExpr) {
  auto templateSpecializationType =
      llvm::dyn_cast<clang::TemplateSpecializationType>(callExpr->getType());
  Dump(templateSpecializationType,
       "templateSpecializationType [callExpr->getType()]");

  auto templateName = templateSpecializationType->getTemplateName();
  auto templateDecl = templateName.getAsTemplateDecl();
  if (templateDecl->getName() != "tuple_element_t")
    return {};

  const auto &template_argument = templateSpecializationType->getArg(0);
  Dump(&template_argument, "template_argument");

  auto constantExpr =
      llvm::dyn_cast<clang::ConstantExpr>(template_argument.getAsExpr());
  Dump(constantExpr, "constantExpr");

  auto value = constantExpr->getAPValueResult();
  Dump(&value, "value");

  return *value.getInt().getRawData();
}

std::string GetTemplateParameterAsString(
    size_t index,
    const clang::TemplateSpecializationType *templateSpecializationType) {
  const auto &arg = templateSpecializationType->getArg(index);
  Dump(&arg, "arg");

  auto typedefType = llvm::dyn_cast<clang::TypedefType>(arg.getAsType());
  Dump(typedefType, "arg");

  if (!typedefType) {
    return {};
  }

  return typedefType->getDecl()->getNameAsString();
}

std::string GetUnderlyingTypeAsString(const clang::DeclRefExpr *declRefExpr) {
  std::string type;
  auto refDeclOfCallee = declRefExpr->getReferencedDeclOfCallee();
  Dump(refDeclOfCallee, "[I] refDeclOfCallee");

  if (!refDeclOfCallee) {
    return {};
  }

#ifdef VERBOSE
  std::cerr << "[I] refDeclOfCallee" << std::endl;
  refDeclOfCallee->dump();
#endif

  // Handle HRESULT when a HRESULT variable has been declared
  auto varDecl = llvm::dyn_cast<clang::VarDecl>(refDeclOfCallee);
  if (varDecl) {
    auto exprInit = varDecl->getInit();
    if (!exprInit) {
      return {};
    }

    return exprInit->getType().getAsString();
  }

  // Handle HRESULT when declared has 'auto hr = Foobar()'
  auto functionDecl = llvm::dyn_cast<clang::FunctionDecl>(refDeclOfCallee);
  if (functionDecl) {
    return functionDecl->getReturnType().getAsString();
  }

  // Handle expressions like 'auto [hr, foo] = ...' and lambdas
  //   - get integral value N from 'tuple_element_t<N, T>'
  //   - get template parameter type for item N
  auto bindingDecl = llvm::dyn_cast<clang::BindingDecl>(refDeclOfCallee);
  if (bindingDecl) {
    Dump(bindingDecl, "bindingDecl [cast of refDeclOfCallee])");

    auto varDecl = bindingDecl->getHoldingVar();
    Dump(varDecl, "varDecl [bindingDecl->getHoldingVar()]");

    auto callExpr = llvm::dyn_cast<clang::CallExpr>(varDecl->getInit());
    Dump(callExpr, "callExpr [varDecl->getInit()]");

    // clang-format off
    /*
      [I] callExpr [varDecl->getInit()] - class clang::CallExpr const * __ptr64
      CallExpr 0x262538db788 'tuple_element_t<
        1ULL,
        std::pair<class std::shared_ptr<class Orc::TableOutput::IWriter>, long>
    */
    // clang-format on

    if (!callExpr) {
      return {};
    }

    // look for a tuple_element_t specialization and extract the index of the
    // parameter of interest
    const auto tupleIndex = GetTupleElementIndex(callExpr);

    auto decompositionDecl = llvm::dyn_cast<clang::DecompositionDecl>(
        bindingDecl->getDecomposedDecl());
    Dump(decompositionDecl,
         "decompositionDecl [bindingDecl->getDecomposedDecl()]");

    // now look for the HRESULT string in the declaration as it is erased from
    // callExpr (replaced by buildin type 'long')
    auto expr = decompositionDecl->getInit();
    Dump(expr, "expr [decompositionDecl->getInit()]");
    if (!expr) {
      return {};
    }

    auto elaboratedType =
        llvm::dyn_cast<clang::ElaboratedType>(expr->getType());
    Dump(elaboratedType, "ElaboratedType");

    if (!elaboratedType) {
      return {};
    }

    auto templateSpecializationType =
        llvm::dyn_cast<clang::TemplateSpecializationType>(
            elaboratedType->desugar());
    Dump(templateSpecializationType, "TemplateSpecializationType");
    if (!templateSpecializationType) {
      return {};
    }

    return GetTemplateParameterAsString(tupleIndex, templateSpecializationType);
  }

  return {};
}

std::string Escape(const std::string& s) {
  std::string escaped;
  for (auto c : s) {
    if (c == '%') {
      escaped += c;
    }

    escaped += c;
  }

  return escaped;
}

} // namespace

namespace clang {
namespace tidy {
namespace misc {

void StronglyTypeHRESULTCheck::registerMatchers(MatchFinder *Finder) {
  Finder->addMatcher(
      callExpr(callee(functionDecl(hasName("::Orc::Log::Trace")))).bind("x"),
      this);
  Finder->addMatcher(
      callExpr(callee(functionDecl(hasName("::Orc::Log::Debug")))).bind("x"),
      this);
  Finder->addMatcher(
      callExpr(callee(functionDecl(hasName("::Orc::Log::Info")))).bind("x"),
      this);
  Finder->addMatcher(
      callExpr(callee(functionDecl(hasName("::Orc::Log::Warn")))).bind("x"),
      this);
  Finder->addMatcher(
      callExpr(callee(functionDecl(hasName("::Orc::Log::Error")))).bind("x"),
      this);
  Finder->addMatcher(
      callExpr(callee(functionDecl(hasName("::Orc::Log::Critical")))).bind("x"),
      this);
}

void StronglyTypeHRESULTCheck::check(const MatchFinder::MatchResult &result) {
  const auto *callExpr = result.Nodes.getNodeAs<CallExpr>("x");
  if (callExpr == nullptr) {
    std::cerr << "[E] Unexpected node type (expected CallExpr)" << std::endl;
    return;
  }

  if (callExpr->getNumArgs() < 1) {
    std::cerr << "[W] Unexpected argument count" << std::endl;
    callExpr->dump(llvm::outs(), *result.Context);
    return;
  }

  auto arg0 = callExpr->getArg(0);
  if (arg0->getStmtClass() != Stmt::StringLiteralClass) {
    std::cerr << "[W] Unexpected arg0 type (expected 'StringLiteralClass'"
              << std::endl;
    callExpr->dump(llvm::outs(), *result.Context);
    return;
  }

  // replace strings like '(code: {:#x})' with '{}'
  bool hasFoundCodeString = ReplaceCodeStringLiteral(
      llvm::dyn_cast<StringLiteral>(arg0), result.Context);

  // wrap all HRESULTs in a SystemError() call to strongly type them within an
  // std::error_code
  bool hasFoundHR = WrapHRESULT(callExpr, result.Context);

  if (hasFoundCodeString && !hasFoundHR) {
    std::cerr << "[W] Message with code string but no 'hr' (stderr)"
              << std::endl;
    callExpr->dump(llvm::outs(), *result.Context);

    // Add a marker when error code seems missing
    diag(callExpr->getBeginLoc(), "Add comment marker 'CHECK_MISSING_HR'")
        << FixItHint::CreateInsertion(callExpr->getSourceRange().getEnd(),
                                      " CHECK_MISSING_HR");
  }
}

bool StronglyTypeHRESULTCheck::ReplaceCodeStringLiteral(
    const StringLiteral *literal, ASTContext *context) {
  auto &SM = context->getSourceManager();
  auto &LO = context->getLangOpts();

  std::string message;
  if (literal->isWide()) {
    std::wstring messageW(
        reinterpret_cast<const wchar_t *>(literal->getBytes().data()),
        literal->getLength());
    if (!llvm::convertWideToUTF8(messageW, message)) {
      std::cerr << "[E] Failed 'convertWideToUTF8'" << std::endl;
      return false;
    }

    message.insert(0, "L\"");
    message.append("\"");
  } else {
    message = (std::string)literal->getString();
    message.insert(0, "\"");
    message.append("\"");
  }

  // IDEA: could count '{}' if necessary but beware of cases like 'format("foo
  // {{}}", bar, bar2);'
  const std::string initialMessage = message;
  message = ::ReplaceAll(message, "(code: {:#x})", "[{}]");
  message = ::ReplaceAll(message, "(code {:#x})", "[{}]");
  message = ::ReplaceAll(message, "code: {:#x}", "[{}]");
  message = ::ReplaceAll(message, "code {:#x}", "[{}]");

  if (initialMessage == message) {
    return false;
  }

  CharSourceRange CharRange = Lexer::makeFileCharRange(
      CharSourceRange::getTokenRange(literal->getSourceRange()), SM, LO);

  const auto status =
      std::string("Replace: '") + initialMessage + "' with: '" + message + "'";
  diag(literal->getBeginLoc(), ::Escape(status))
      << FixItHint::CreateReplacement(CharRange, message);

  return true;
}

bool StronglyTypeHRESULTCheck::WrapHRESULT(const CallExpr *callExpr,
                                           ASTContext *context) {
  auto &SM = context->getSourceManager();
  auto &LO = context->getLangOpts();

  bool hasFoundHR = false;
  for (size_t i = 1; i < callExpr->getNumArgs(); ++i) {
    const auto arg = callExpr->getArg(i);

#ifdef VERBOSE
    std::cerr << "[I] Argument #" << i << std::endl;
    arg->dump(llvm::outs(), *context);
#endif

    auto argDeclRefExpr =
        ::GetFirst_DeclRefExprClass(llvm::dyn_cast<clang::Stmt>(arg));
    if (argDeclRefExpr == nullptr) {
      continue;
    }

    // Disabled: this was not enough to cover all cases ('auto', ...) so use
    // 'GetUnderlyingTypeAsString' instead.
    // auto type = QualType::getAsString(declRefExpr->getType().split(), LO);

    auto type = ::GetUnderlyingTypeAsString(argDeclRefExpr);
    if (type != "HRESULT") {
      if (type == "std::error_code") {
        hasFoundHR = true;
        return hasFoundHR;
      }

      if (type.size()) {
        std::cerr << "[I] type: " << type << std::endl;
        arg->dump(llvm::outs(), *context);
      }

      continue;
    }

    hasFoundHR = true;

    std::string oldString =
        (std::string)argDeclRefExpr->getNameInfo().getAsString();
    std::string newString = "SystemError(" + oldString + ")";

    CharSourceRange CharRange = Lexer::makeFileCharRange(
        CharSourceRange::getTokenRange(argDeclRefExpr->getSourceRange()), SM,
        LO);

    const auto status =
        std::string("Replace: '") + oldString + "' with: '" + newString + "'";
    diag(argDeclRefExpr->getBeginLoc(), status)
        << FixItHint::CreateReplacement(CharRange, newString);
  }

  return hasFoundHR;
}

} // namespace misc
} // namespace tidy
} // namespace clang
