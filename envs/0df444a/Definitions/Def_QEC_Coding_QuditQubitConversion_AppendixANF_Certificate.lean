-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Certificate
-- name    : QEC_Coding_QuditQubitConversion_AppendixANF_Certificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:20:21.525414+00:00
-- url     : https://prove2.me/theorems/35b9823f-757b-428d-8d23-82a3b824d07f
-- title:
--   Certificate
-- statement:
--   Definitions and structural lemmas for Certificate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Certificate.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_BooleanANF
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
abbrev Word := Fin 10 → ZMod 2
abbrev ANF := Why24BooleanANF.Polynomial 10
abbrev ANFWord := Fin 10 → ANF
def alphaReduction : Matrix (Fin 19) (Fin 10) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 1;
     1, 0, 0, 1, 0, 0, 0, 1, 0, 0;
     0, 1, 0, 0, 1, 0, 0, 0, 1, 0]
def wordMul (left right : Word) : Word :=
  fun coordinate =>
    ∑ first : Fin 10, ∑ second : Fin 10,
      (left first * right second) *
        alphaReduction
          ⟨(first : Nat) + (second : Nat), by omega⟩ coordinate
def anfWordMul (left right : ANFWord) : ANFWord :=
  fun coordinate =>
    ∑ first : Fin 10, ∑ second : Fin 10,
      alphaReduction
          ⟨(first : Nat) + (second : Nat), by omega⟩ coordinate •
        (left first * right second)
def selectedBasisWord (selected : Fin 10) : Word :=
  fun power => f1024SelectedSelfDualP power selected
def selectedBasisSquareWord (selected : Fin 10) : Word :=
  wordMul (selectedBasisWord selected) (selectedBasisWord selected)
def selectedBasisFourthWord (selected : Fin 10) : Word :=
  wordMul (selectedBasisSquareWord selected) (selectedBasisSquareWord selected)
def linearANFWord (basisWords : Fin 10 → Word) : ANFWord :=
  fun power =>
    ∑ selected : Fin 10,
      basisWords selected power • generator selected
def selectedANFWord : ANFWord :=
  linearANFWord selectedBasisWord
def selectedSquareANFWord : ANFWord :=
  linearANFWord selectedBasisSquareWord
def selectedFourthANFWord : ANFWord :=
  linearANFWord selectedBasisFourthWord
def traceTensor (first second third : Fin 10) : ZMod 2 :=
  wordMul
    (wordMul (selectedBasisWord first) (selectedBasisSquareWord second))
    (selectedBasisFourthWord third) 7
def sourcePhasePolynomial : ANF :=
  ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    traceTensor first second third •
      (generator first * generator second * generator third)
def tripleSupport (first second third : Fin 10) : Finset (Fin 10) :=
  {first, second, third}
def sourceCoefficient (support : Finset (Fin 10)) : ZMod 2 :=
  ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
    if tripleSupport first second third = support then
      traceTensor first second third
    else 0
def singletonMonomial (coordinate : Fin 10) : Monomial 10 :=
  ⟨{coordinate}⟩
end QEC.Coding.Why24AppendixANF


