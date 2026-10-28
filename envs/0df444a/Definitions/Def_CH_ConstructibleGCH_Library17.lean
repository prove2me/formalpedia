-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library17
-- name    : CH_ConstructibleGCH_Library17
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:59:49.873807+00:00
-- url     : https://prove2.me/theorems/a5ec4f45-4141-444b-ad7e-22a6135c9723
-- title:
--   The five branches of the textbook E step
-- statement:
--   A single textbook E step handles its finite collection of elementary cases through coded inputs and outputs. This library supplies the branch formulas and their evaluation interfaces for use in local solutions and definability enumeration.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEStep.lean#L1

import Definitions.Def_CH_ConstructibleAC_Library15
import Definitions.Def_CH_Constructible
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Sum.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.Basic

import Definitions.Def_CH_ConstructibleGCH_Library16
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookEStep -/
section GCHSource_Work_CUGCH_TextbookEStep
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/










/-!
# The recursion functional for the textbook enumeration `E`

This file implements exactly the five clauses in Wang Fangting,
*Axiomatic Set Theory*, Section 6.4.  The recursion key is the actual
Kuratowski pair `<m,n>` in `omega x omega`, and a constructor code is
`2 ^ i * 3 ^ j * 5 ^ tag`.  In particular, `j` remains part of the complete
code in the complement and projection clauses even though those two values
do not otherwise depend on it.

The history argument is an arbitrary set-coded relation.  Every read from
it uses the total, absolute operation `uniqueGraphLookupZF`; no external
Lean function is silently substituted for an internal graph.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## The total metatheoretic functional -/

/-- The five-clause functional used in the simultaneous recursion for
`E(a,n,m)`.  Inputs outside `omega x omega`, malformed constructor codes,
and the two guarded atomic clauses with illegal indices all return the empty
set, exactly as in the textbook's final "otherwise" clause. -/
noncomputable def textbookEStep
    (a key history : ZFSet.{u}) : ZFSet.{u} :=
  match textbookEKeyDecode key with
  | none => ∅
  | some (m, n) =>
      match textbookEDecode m with
      | some (i, j, 0) =>
          if i < n ∧ j < n then
            textbookDInCodeZF a (natCode n) (natCode i) (natCode j)
          else ∅
      | some (i, j, 1) =>
          if i < n ∧ j < n then
            textbookDEqCodeZF a (natCode n) (natCode i) (natCode j)
          else ∅
      | some (i, _j, 2) =>
          relativeDifferenceZF (ZFSet.funs (natCode n) a)
            (uniqueGraphLookupZF history
              (ZFSet.pair (natCode i) (natCode n)))
      | some (i, j, 3) =>
          intersectionZF
            (uniqueGraphLookupZF history
              (ZFSet.pair (natCode i) (natCode n)))
            (uniqueGraphLookupZF history
              (ZFSet.pair (natCode j) (natCode n)))
      | some (i, _j, 4) =>
          textbookExistsProjCodeZF a (natCode n)
            (uniqueGraphLookupZF history
              (ZFSet.pair (natCode i) (natCode (n + 1))))
      | _ => ∅

/-! ## The five displayed textbook equations -/

@[simp]
theorem textbookEStep_code_zero
    (a history : ZFSet.{u}) (n i j : Nat)
    (hi : i < n) (hj : j < n) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 0)) (natCode n)) history =
      textbookDInCodeZF a (natCode n) (natCode i) (natCode j) := by
  simp [textbookEStep, hi, hj]

@[simp]
theorem textbookEStep_code_one
    (a history : ZFSet.{u}) (n i j : Nat)
    (hi : i < n) (hj : j < n) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 1)) (natCode n)) history =
      textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) := by
  simp [textbookEStep, hi, hj]

@[simp]
theorem textbookEStep_code_two
    (a history : ZFSet.{u}) (n i j : Nat) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 2)) (natCode n)) history =
      relativeDifferenceZF (ZFSet.funs (natCode n) a)
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode n))) := by
  simp [textbookEStep]

@[simp]
theorem textbookEStep_code_three
    (a history : ZFSet.{u}) (n i j : Nat) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 3)) (natCode n)) history =
      intersectionZF
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode n)))
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode j) (natCode n))) := by
  simp [textbookEStep]

@[simp]
theorem textbookEStep_code_four
    (a history : ZFSet.{u}) (n i j : Nat) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 4)) (natCode n)) history =
      textbookExistsProjCodeZF a (natCode n)
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
  simp [textbookEStep]

@[simp]
theorem textbookEStep_code_zero_eq_empty_of_not_lt_left
    (a history : ZFSet.{u}) (n i j : Nat) (hi : ¬ i < n) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 0)) (natCode n)) history = ∅ := by
  simp [textbookEStep, hi]

@[simp]
theorem textbookEStep_code_zero_eq_empty_of_not_lt_right
    (a history : ZFSet.{u}) (n i j : Nat) (hj : ¬ j < n) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 0)) (natCode n)) history = ∅ := by
  simp [textbookEStep, hj]

@[simp]
theorem textbookEStep_code_one_eq_empty_of_not_lt_left
    (a history : ZFSet.{u}) (n i j : Nat) (hi : ¬ i < n) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 1)) (natCode n)) history = ∅ := by
  simp [textbookEStep, hi]

@[simp]
theorem textbookEStep_code_one_eq_empty_of_not_lt_right
    (a history : ZFSet.{u}) (n i j : Nat) (hj : ¬ j < n) :
    textbookEStep a
        (ZFSet.pair (natCode (textbookECode i j 1)) (natCode n)) history = ∅ := by
  simp [textbookEStep, hj]

/-! ## The pure membership-language graph formula -/

namespace TextbookEFormula

/-- Embed a ternary graph formula at three designated coordinates. -/
def formula3At {n : Nat} (formula : FOFormula 3)
    (x y z : Fin n) : FOFormula n :=
  FOFormula.rename ![x, y, z] formula

/-- Embed a quaternary graph formula at four designated coordinates. -/
def formula4At {n : Nat} (formula : FOFormula 4)
    (w x y z : Fin n) : FOFormula n :=
  FOFormula.rename ![w, x, y, z] formula

/-- Embed a five-variable graph formula at designated coordinates. -/
def formula5At {n : Nat} (formula : FOFormula 5)
    (v w x y z : Fin n) : FOFormula n :=
  FOFormula.rename ![v, w, x, y, z] formula

/-- The shared recognition part of one constructor clause.  Its layout is
`[a,key,history,output,omega,m,n,i,j,tag]`.  When `bounded` is true the two
extra textbook guards `i in n` and `j in n` are included. -/
def codeGuardBody (literal : Nat) (bounded : Bool) : FOFormula 10 :=
  .conj (.mem (7 : Fin 10) (4 : Fin 10)) <|
  .conj (.mem (8 : Fin 10) (4 : Fin 10)) <|
  .conj (Delta0Formula.natLiteralDeltaAt literal (9 : Fin 10)).toFO <|
  .conj
    (TextbookNatFormula.textbookECodeFormulaAt
      (4 : Fin 10) (7 : Fin 10) (8 : Fin 10)
      (9 : Fin 10) (5 : Fin 10)) <|
  if bounded then
    .conj (.mem (7 : Fin 10) (6 : Fin 10))
      (.mem (8 : Fin 10) (6 : Fin 10))
  else
    .eq (9 : Fin 10) (9 : Fin 10)

/-- Constructor recognition after existentially binding `i`, `j`, and the
tag.  The free layout is `[a,key,history,output,omega,m,n]`. -/
def codeGuard (literal : Nat) (bounded : Bool) : FOFormula 7 :=
  .ex (.ex (.ex (codeGuardBody literal bounded)))

/-- Atomic membership clause, including the textbook bounds `i,j in n`. -/
def stepBranchZero : FOFormula 7 :=
  .ex <| .ex <| .ex <|
    .conj (codeGuardBody 0 true)
      (formula5At TextbookDefFormula.dInOutputFormula
        (0 : Fin 10) (6 : Fin 10) (7 : Fin 10)
        (8 : Fin 10) (3 : Fin 10))

/-- Atomic equality clause, including the textbook bounds `i,j in n`. -/
def stepBranchOne : FOFormula 7 :=
  .ex <| .ex <| .ex <|
    .conj (codeGuardBody 1 true)
      (formula5At TextbookDefFormula.dEqOutputFormula
        (0 : Fin 10) (6 : Fin 10) (7 : Fin 10)
        (8 : Fin 10) (3 : Fin 10))

/-- Relative-complement clause.  After the code fields, its witnesses are
the history key `<i,n>`, the total lookup value, and the genuine finite
function space `a^n`, in that order. -/
def stepBranchTwo : FOFormula 7 :=
  .ex <| .ex <| .ex <|
    .conj (codeGuardBody 2 false) <|
    .ex <| .conj
      (Delta0Formula.kuratowskiPairEqAt
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11)).toFO <|
    .ex <| .conj
      (formula3At TextbookDefFormula.uniqueGraphLookupFormula
        (2 : Fin 12) (10 : Fin 12) (Fin.last 11)) <|
    .ex <| .conj
      (formula3At Model.finiteFunctionSpaceGraph
        (6 : Fin 13) (0 : Fin 13) (Fin.last 12))
      (formula3At TextbookDefFormula.relativeDifferenceOutputFormula
        (Fin.last 12) (11 : Fin 13) (3 : Fin 13))

/-- Intersection clause.  The four witnesses following the code fields are
`<i,n>`, its lookup value, `<j,n>`, and its lookup value. -/
def stepBranchThree : FOFormula 7 :=
  .ex <| .ex <| .ex <|
    .conj (codeGuardBody 3 false) <|
    .ex <| .conj
      (Delta0Formula.kuratowskiPairEqAt
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11)).toFO <|
    .ex <| .conj
      (formula3At TextbookDefFormula.uniqueGraphLookupFormula
        (2 : Fin 12) (10 : Fin 12) (Fin.last 11)) <|
    .ex <| .conj
      (Delta0Formula.kuratowskiPairEqAt
        (Fin.last 12) (8 : Fin 13) (6 : Fin 13)).toFO <|
    .ex <| .conj
      (formula3At TextbookDefFormula.uniqueGraphLookupFormula
        (2 : Fin 14) (12 : Fin 14) (Fin.last 13))
      (formula3At TextbookDefFormula.intersectionOutputFormula
        (11 : Fin 14) (Fin.last 13) (3 : Fin 14))

/-- Existential-projection clause.  Its witnesses following the code fields
are `n+1`, the history key `<i,n+1>`, and the total lookup value. -/
def stepBranchFour : FOFormula 7 :=
  .ex <| .ex <| .ex <|
    .conj (codeGuardBody 4 false) <|
    .ex <| .conj
      (Delta0Formula.successorAt
        (Fin.last 10) (6 : Fin 11)).toFO <|
    .ex <| .conj
      (Delta0Formula.kuratowskiPairEqAt
        (Fin.last 11) (7 : Fin 12) (10 : Fin 12)).toFO <|
    .ex <| .conj
      (formula3At TextbookDefFormula.uniqueGraphLookupFormula
        (2 : Fin 13) (11 : Fin 13) (Fin.last 12))
      (formula4At TextbookDefFormula.existsProjOutputFormula
        (0 : Fin 13) (6 : Fin 13) (Fin.last 12) (3 : Fin 13))

/-- Disjunction of all five successful constructor guards. -/
def anyCodeGuard : FOFormula 7 :=
  .disj (codeGuard 0 true) <|
  .disj (codeGuard 1 true) <|
  .disj (codeGuard 2 false) <|
  .disj (codeGuard 3 false) (codeGuard 4 false)

/-- The exact "otherwise" clause: no successful guard holds and the output
is empty.  It does not depend on failure of an operation graph. -/
def stepFallback : FOFormula 7 :=
  .conj (.neg anyCodeGuard)
    (Delta0Formula.emptyDeltaAt (3 : Fin 7)).toFO

/-- Body after binding `omega`, the recursive code `m`, and arity `n`.
The free layout is `[a,key,history,output,omega,m,n]`. -/
def textbookEStepBody : FOFormula 7 :=
  .conj (Model.standardOmegaAt (4 : Fin 7)) <|
  .conj (.mem (5 : Fin 7) (4 : Fin 7)) <|
  .conj (.mem (6 : Fin 7) (4 : Fin 7)) <|
  .conj
    (Delta0Formula.kuratowskiPairEqAt
      (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)).toFO <|
  .disj stepBranchZero <|
  .disj stepBranchOne <|
  .disj stepBranchTwo <|
  .disj stepBranchThree <|
  .disj stepBranchFour stepFallback

/-- Pure membership-language graph of `textbookEStep`, with free-variable
layout `[a,key,history,output]`.  It is false off `TextbookEDomain`. -/
def textbookEStepFormula : FOFormula 4 :=
  .ex (.ex (.ex textbookEStepBody))

/-! ## Ambient semantics of the formula components -/

@[simp]
theorem satisfies_formula3At
    (formula : FOFormula 3) {n : Nat} (x y z : Fin n)
    (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (formula3At formula x y z) s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem formula
        ![s x, s y, s z] := by
  rw [formula3At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![x, y, z] i)) =
      ![s x, s y, s z] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

@[simp]
theorem satisfies_formula4At
    (formula : FOFormula 4) {n : Nat} (v w x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (formula4At formula v w x y) s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem formula
        ![s v, s w, s x, s y] := by
  rw [formula4At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![v, w, x, y] i)) =
      ![s v, s w, s x, s y] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

@[simp]
theorem satisfies_formula5At
    (formula : FOFormula 5) {n : Nat} (v w x y z : Fin n)
    (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (formula5At formula v w x y z) s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem formula
        ![s v, s w, s x, s y, s z] := by
  rw [formula5At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![v, w, x, y, z] i)) =
      ![s v, s w, s x, s y, s z] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

theorem satisfies_codeGuardBody_natCode
    (literal : Nat) (bounded : Bool)
    (a key history output : ZFSet.{u}) (m n i j : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (codeGuardBody literal bounded)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode literal] ↔
      m = textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  cases bounded <;>
    simp [codeGuardBody, TextbookNatFormula.satisfies_textbookECodeFormulaAt,
      IndexedSequenceZF.mem_omega_iff_exists_natCode,
      IndexedSequenceZF.mem_natCode_iff_exists_lt,
      natCode_injective.eq_iff]

theorem satisfies_codeGuard_standard
    (literal : Nat) (bounded : Bool)
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (codeGuard literal bounded)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  rw [codeGuard]
  simp only [FOFormula.Satisfies]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hbody⟩
    rw [hassign] at hbody
    have hiOmega :
        iSet ∈ (Ordinal.omega0.toZFSet : ZFSet.{u}) := hbody.1
    have hjOmega :
        jSet ∈ (Ordinal.omega0.toZFSet : ZFSet.{u}) := hbody.2.1
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
      hiOmega with ⟨i, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
      hjOmega with ⟨j, rfl⟩
    have htag : tagSet = (natCode literal : ZFSet.{u}) :=
      (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
        literal (9 : Fin 10)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet]).mp hbody.2.2.1
    subst tagSet
    exact ⟨i, j,
      (satisfies_codeGuardBody_natCode
        literal bounded a key history output m n i j).mp hbody⟩
  · rintro ⟨i, j, hcode⟩
    refine ⟨(natCode i : ZFSet.{u}), (natCode j : ZFSet.{u}),
      (natCode literal : ZFSet.{u}), ?_⟩
    rw [hassign]
    exact (satisfies_codeGuardBody_natCode
      literal bounded a key history output m n i j).mpr hcode

@[simp]
theorem satisfies_standardFiniteDomainAt_ambient_iff
    {n : Nat} (domain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.standardFiniteDomainAt domain) s ↔
      ∃ k : Nat, s domain = natCode k := by
  simp [Model.standardFiniteDomainAt,
    TextbookNatFormula.satisfies_standardOmegaAt_ambient_iff,
    IndexedSequenceZF.mem_omega_iff_exists_natCode]

@[simp]
theorem satisfies_finiteFunctionSpaceGraph_ambient
    (domain codomain space : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        Model.finiteFunctionSpaceGraph ![domain, codomain, space] ↔
      (∃ k : Nat, domain = natCode k) ∧
        space = ZFSet.funs domain codomain := by
  simp [Model.finiteFunctionSpaceGraph,
    TextbookDefFormula.satisfies_functionSpaceGraph]

@[simp]
theorem satisfies_dInOutputFormula_ambient
    (a arity left right output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookDefFormula.dInOutputFormula
        ![a, arity, left, right, output] ↔
      output = textbookDInCodeZF a arity left right := by
  rw [TextbookDefFormula.dInOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  change (∀ graph : ZFSet.{u}, graph ∈ output ↔
    FOFormula.Satisfies Delta0Formula.ZFMem
      TextbookDefFormula.dInOutputMemberCondition
      ![a, arity, left, right, output, graph]) ↔ _
  simp only [TextbookDefFormula.dInOutputMemberCondition,
    FOFormula.Satisfies, satisfies_standardFiniteDomainAt_ambient_iff,
    Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_dInMemberDeltaAt]
  rw [ZFSet.ext_iff]
  simp [mem_textbookDInCodeZF_iff]

@[simp]
theorem satisfies_dEqOutputFormula_ambient
    (a arity left right output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookDefFormula.dEqOutputFormula
        ![a, arity, left, right, output] ↔
      output = textbookDEqCodeZF a arity left right := by
  rw [TextbookDefFormula.dEqOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  change (∀ graph : ZFSet.{u}, graph ∈ output ↔
    FOFormula.Satisfies Delta0Formula.ZFMem
      TextbookDefFormula.dEqOutputMemberCondition
      ![a, arity, left, right, output, graph]) ↔ _
  simp only [TextbookDefFormula.dEqOutputMemberCondition,
    FOFormula.Satisfies, satisfies_standardFiniteDomainAt_ambient_iff,
    Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_dEqMemberDeltaAt]
  rw [ZFSet.ext_iff]
  simp [mem_textbookDEqCodeZF_iff]

@[simp]
theorem satisfies_existsProjOutputFormula_ambient
    (a arity relation output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        TextbookDefFormula.existsProjOutputFormula
        ![a, arity, relation, output] ↔
      output = textbookExistsProjCodeZF a arity relation := by
  rw [TextbookDefFormula.existsProjOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  change (∀ graph : ZFSet.{u}, graph ∈ output ↔
    FOFormula.Satisfies Delta0Formula.ZFMem
      TextbookDefFormula.existsProjOutputMemberCondition
      ![a, arity, relation, output, graph]) ↔ _
  simp only [TextbookDefFormula.existsProjOutputMemberCondition,
    FOFormula.Satisfies, satisfies_standardFiniteDomainAt_ambient_iff,
    Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_existsProjMemberDeltaAt]
  rw [ZFSet.ext_iff]
  simp [mem_textbookExistsProjCodeZF_iff]

@[simp]
theorem satisfies_stepBranchZero_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem stepBranchZero
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 0 ∧ i < n ∧ j < n ∧
        output = textbookDInCodeZF a (natCode n) (natCode i) (natCode j) := by
  rw [stepBranchZero]
  simp only [FOFormula.Satisfies]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, houtput⟩
    rw [hassign] at hguard houtput
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
      hguard.1 with ⟨i, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
      hguard.2.1 with ⟨j, rfl⟩
    have htag : tagSet = (natCode 0 : ZFSet.{u}) :=
      (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
        0 (9 : Fin 10)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet]).mp hguard.2.2.1
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_natCode
        0 true a key history output m n i j).mp hguard
    have hvalue :
        output = textbookDInCodeZF a (natCode n) (natCode i) (natCode j) := by
      simpa using houtput
    exact ⟨i, j, hrecognized.1,
      hrecognized.2.1, hrecognized.2.2, hvalue⟩
  · rintro ⟨i, j, hcode, hi, hj, houtput⟩
    refine ⟨(natCode i : ZFSet.{u}), (natCode j : ZFSet.{u}),
      (natCode 0 : ZFSet.{u}), ?_, ?_⟩
    · rw [hassign]
      exact (satisfies_codeGuardBody_natCode
        0 true a key history output m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign]
      simpa using houtput

@[simp]
theorem satisfies_stepBranchOne_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem stepBranchOne
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 1 ∧ i < n ∧ j < n ∧
        output = textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) := by
  rw [stepBranchOne]
  simp only [FOFormula.Satisfies]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, houtput⟩
    rw [hassign] at hguard houtput
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
      hguard.1 with ⟨i, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
      hguard.2.1 with ⟨j, rfl⟩
    have htag : tagSet = (natCode 1 : ZFSet.{u}) :=
      (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
        1 (9 : Fin 10)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet]).mp hguard.2.2.1
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_natCode
        1 true a key history output m n i j).mp hguard
    have hvalue :
        output = textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) := by
      simpa using houtput
    exact ⟨i, j, hrecognized.1,
      hrecognized.2.1, hrecognized.2.2, hvalue⟩
  · rintro ⟨i, j, hcode, hi, hj, houtput⟩
    refine ⟨(natCode i : ZFSet.{u}), (natCode j : ZFSet.{u}),
      (natCode 1 : ZFSet.{u}), ?_, ?_⟩
    · rw [hassign]
      exact (satisfies_codeGuardBody_natCode
        1 true a key history output m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign]
      simpa using houtput

@[simp]
theorem satisfies_stepBranchTwo_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem stepBranchTwo
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 2 ∧
        output = relativeDifferenceZF (ZFSet.funs (natCode n) a)
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n))) := by
  rw [stepBranchTwo]
  simp only [FOFormula.Satisfies]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hkeyAssignment (iSet jSet tagSet lookupKey : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] lookupKey =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey] := by
    funext k
    fin_cases k <;> rfl
  have hremovedAssignment
      (iSet jSet tagSet lookupKey removed : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey] removed =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey, removed] := by
    funext k
    fin_cases k <;> rfl
  have hspaceAssignment
      (iSet jSet tagSet lookupKey removed space : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey, removed] space =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey, removed, space] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, lookupKey, hpair,
      removed, hlookup, space, hspace, hdifference⟩
    rw [hfields] at hguard hpair hlookup hspace hdifference
    rw [hkeyAssignment] at hpair hlookup hspace hdifference
    rw [hremovedAssignment] at hlookup hspace hdifference
    rw [hspaceAssignment] at hspace hdifference
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
      hguard.1 with ⟨i, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
      hguard.2.1 with ⟨j, rfl⟩
    have htag : tagSet = (natCode 2 : ZFSet.{u}) :=
      (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
        2 (9 : Fin 10)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet]).mp hguard.2.2.1
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_natCode
        2 false a key history output m n i j).mp hguard
    have hlookupKey :
        lookupKey = ZFSet.pair (natCode i) (natCode n) := by
      simpa [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt] using hpair
    subst lookupKey
    have hremoved :
        removed = uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode n)) := by
      simpa [satisfies_formula3At,
        TextbookDefFormula.satisfies_uniqueGraphLookupFormula_iff] using hlookup
    subst removed
    have hspaceValue : space = ZFSet.funs (natCode n) a := by
      have h := hspace
      simp [satisfies_formula3At,
        satisfies_finiteFunctionSpaceGraph_ambient] at h
      exact h
    subst space
    have hvalue : output =
        relativeDifferenceZF (ZFSet.funs (natCode n) a)
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n))) := by
      simpa [satisfies_formula3At,
        TextbookDefFormula.satisfies_relativeDifferenceOutputFormula] using hdifference
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let lookupKey : ZFSet.{u} :=
      ZFSet.pair (natCode i) (natCode n)
    let removed : ZFSet.{u} := uniqueGraphLookupZF history lookupKey
    let space : ZFSet.{u} := ZFSet.funs (natCode n) a
    refine ⟨(natCode i : ZFSet.{u}), (natCode j : ZFSet.{u}),
      (natCode 2 : ZFSet.{u}), ?_, lookupKey, ?_, removed, ?_, space, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_natCode
        2 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields]
      rw [hkeyAssignment]
      simp [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt,
        lookupKey]
    · rw [hfields]
      rw [hkeyAssignment, hremovedAssignment]
      simp [satisfies_formula3At,
        TextbookDefFormula.satisfies_uniqueGraphLookupFormula_iff,
        removed, lookupKey]
    · rw [hfields]
      rw [hkeyAssignment, hremovedAssignment, hspaceAssignment]
      simp [satisfies_formula3At,
        satisfies_finiteFunctionSpaceGraph_ambient,
        space]
    · rw [hfields]
      rw [hkeyAssignment, hremovedAssignment, hspaceAssignment]
      simpa [satisfies_formula3At,
        TextbookDefFormula.satisfies_relativeDifferenceOutputFormula,
        space, removed, lookupKey] using houtput

@[simp]
theorem satisfies_stepBranchThree_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem stepBranchThree
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 3 ∧
        output = intersectionZF
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n)))
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode j) (natCode n))) := by
  rw [stepBranchThree]
  simp only [FOFormula.Satisfies]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hleftKeyAssignment (iSet jSet tagSet leftKey : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] leftKey =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey] := by
    funext k
    fin_cases k <;> rfl
  have hleftValueAssignment
      (iSet jSet tagSet leftKey leftValue : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey] leftValue =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue] := by
    funext k
    fin_cases k <;> rfl
  have hrightKeyAssignment
      (iSet jSet tagSet leftKey leftValue rightKey : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue] rightKey =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey] := by
    funext k
    fin_cases k <;> rfl
  have hrightValueAssignment
      (iSet jSet tagSet leftKey leftValue rightKey rightValue : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey] rightValue =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey, rightValue] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, leftKey, hleftPair,
      leftValue, hleftLookup, rightKey, hrightPair,
      rightValue, hrightLookup, hintersection⟩
    rw [hfields] at hguard hleftPair hleftLookup hrightPair hrightLookup hintersection
    rw [hleftKeyAssignment] at hleftPair hleftLookup hrightPair hrightLookup hintersection
    rw [hleftValueAssignment] at hleftLookup hrightPair hrightLookup hintersection
    rw [hrightKeyAssignment] at hrightPair hrightLookup hintersection
    rw [hrightValueAssignment] at hrightLookup hintersection
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
      hguard.1 with ⟨i, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
      hguard.2.1 with ⟨j, rfl⟩
    have htag : tagSet = (natCode 3 : ZFSet.{u}) :=
      (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
        3 (9 : Fin 10)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet]).mp hguard.2.2.1
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_natCode
        3 false a key history output m n i j).mp hguard
    have hleftKey : leftKey = ZFSet.pair (natCode i) (natCode n) := by
      simpa [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt] using hleftPair
    subst leftKey
    have hleftValue : leftValue =
        uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode n)) := by
      simpa [satisfies_formula3At,
        TextbookDefFormula.satisfies_uniqueGraphLookupFormula_iff] using
          hleftLookup
    subst leftValue
    have hrightKey : rightKey = ZFSet.pair (natCode j) (natCode n) := by
      simpa [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt] using hrightPair
    subst rightKey
    have hrightValue : rightValue =
        uniqueGraphLookupZF history
          (ZFSet.pair (natCode j) (natCode n)) := by
      simpa [satisfies_formula3At,
        TextbookDefFormula.satisfies_uniqueGraphLookupFormula_iff] using
          hrightLookup
    subst rightValue
    have hvalue : output = intersectionZF
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode n)))
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode j) (natCode n))) := by
      simpa [satisfies_formula3At,
        TextbookDefFormula.satisfies_intersectionOutputFormula] using
          hintersection
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let leftKey : ZFSet.{u} := ZFSet.pair (natCode i) (natCode n)
    let leftValue : ZFSet.{u} := uniqueGraphLookupZF history leftKey
    let rightKey : ZFSet.{u} := ZFSet.pair (natCode j) (natCode n)
    let rightValue : ZFSet.{u} := uniqueGraphLookupZF history rightKey
    refine ⟨(natCode i : ZFSet.{u}), (natCode j : ZFSet.{u}),
      (natCode 3 : ZFSet.{u}), ?_, leftKey, ?_, leftValue, ?_,
      rightKey, ?_, rightValue, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_natCode
        3 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields, hleftKeyAssignment]
      simp [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt, leftKey]
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment]
      simp [satisfies_formula3At,
        TextbookDefFormula.satisfies_uniqueGraphLookupFormula_iff,
        leftValue, leftKey]
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment]
      simp [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt, rightKey]
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment]
      simp [satisfies_formula3At,
        TextbookDefFormula.satisfies_uniqueGraphLookupFormula_iff,
        rightValue, rightKey]
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment]
      simpa [satisfies_formula3At,
        TextbookDefFormula.satisfies_intersectionOutputFormula,
        leftValue, leftKey, rightValue, rightKey] using houtput

@[simp]
theorem satisfies_stepBranchFour_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem stepBranchFour
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 4 ∧
        output = textbookExistsProjCodeZF a (natCode n)
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
  rw [stepBranchFour]
  simp only [FOFormula.Satisfies]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hsuccAssignment (iSet jSet tagSet succN : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] succN =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN] := by
    funext k
    fin_cases k <;> rfl
  have hkeyAssignment
      (iSet jSet tagSet succN lookupKey : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN] lookupKey =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN, lookupKey] := by
    funext k
    fin_cases k <;> rfl
  have hrelationAssignment
      (iSet jSet tagSet succN lookupKey relation : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN, lookupKey] relation =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN, lookupKey, relation] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, succN, hsucc,
      lookupKey, hpair, relation, hlookup, hprojection⟩
    rw [hfields] at hguard hsucc hpair hlookup hprojection
    rw [hsuccAssignment] at hsucc hpair hlookup hprojection
    rw [hkeyAssignment] at hpair hlookup hprojection
    rw [hrelationAssignment] at hlookup hprojection
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
      hguard.1 with ⟨i, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
      hguard.2.1 with ⟨j, rfl⟩
    have htag : tagSet = (natCode 4 : ZFSet.{u}) :=
      (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
        4 (9 : Fin 10)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet]).mp hguard.2.2.1
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_natCode
        4 false a key history output m n i j).mp hguard
    have hsuccN : succN = (natCode (n + 1) : ZFSet.{u}) := by
      simpa [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt,
        natCode_succ_eq_insert] using hsucc
    subst succN
    have hlookupKey : lookupKey =
        ZFSet.pair (natCode i) (natCode (n + 1)) := by
      simpa [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt] using hpair
    subst lookupKey
    have hrelation : relation = uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode (n + 1))) := by
      simpa [satisfies_formula3At,
        TextbookDefFormula.satisfies_uniqueGraphLookupFormula_iff] using
          hlookup
    subst relation
    have hvalue : output = textbookExistsProjCodeZF a (natCode n)
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
      simpa [satisfies_formula4At,
        satisfies_existsProjOutputFormula_ambient] using hprojection
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let succN : ZFSet.{u} := natCode (n + 1)
    let lookupKey : ZFSet.{u} := ZFSet.pair (natCode i) succN
    let relation : ZFSet.{u} := uniqueGraphLookupZF history lookupKey
    refine ⟨(natCode i : ZFSet.{u}), (natCode j : ZFSet.{u}),
      (natCode 4 : ZFSet.{u}), ?_, succN, ?_, lookupKey, ?_, relation, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_natCode
        4 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields, hsuccAssignment]
      simp [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt,
        natCode_succ_eq_insert, succN]
    · rw [hfields, hsuccAssignment, hkeyAssignment]
      simp [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt,
        lookupKey, succN]
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment]
      simp [satisfies_formula3At,
        TextbookDefFormula.satisfies_uniqueGraphLookupFormula_iff,
        relation, lookupKey]
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment]
      simpa [satisfies_formula4At,
        satisfies_existsProjOutputFormula_ambient,
        relation, lookupKey, succN] using houtput

/-! ## Exact combination of the five clauses and fallback -/

/-- The disjunction of the five textbook constructor guards at `(m,n)`. -/
def TextbookEGuard (m n : Nat) : Prop :=
  (∃ i j : Nat, m = textbookECode i j 0 ∧ i < n ∧ j < n) ∨
  (∃ i j : Nat, m = textbookECode i j 1 ∧ i < n ∧ j < n) ∨
  (∃ i j : Nat, m = textbookECode i j 2) ∨
  (∃ i j : Nat, m = textbookECode i j 3) ∨
  (∃ i j : Nat, m = textbookECode i j 4)

/-- Exact result relation for the five clauses plus the textbook's final
"otherwise empty" clause. -/
def TextbookEBranchResult
    (a history output : ZFSet.{u}) (m n : Nat) : Prop :=
  (∃ i j : Nat, m = textbookECode i j 0 ∧ i < n ∧ j < n ∧
    output = textbookDInCodeZF a (natCode n) (natCode i) (natCode j)) ∨
  (∃ i j : Nat, m = textbookECode i j 1 ∧ i < n ∧ j < n ∧
    output = textbookDEqCodeZF a (natCode n) (natCode i) (natCode j)) ∨
  (∃ i j : Nat, m = textbookECode i j 2 ∧
    output = relativeDifferenceZF (ZFSet.funs (natCode n) a)
      (uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode n)))) ∨
  (∃ i j : Nat, m = textbookECode i j 3 ∧
    output = intersectionZF
      (uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode n)))
      (uniqueGraphLookupZF history
        (ZFSet.pair (natCode j) (natCode n)))) ∨
  (∃ i j : Nat, m = textbookECode i j 4 ∧
    output = textbookExistsProjCodeZF a (natCode n)
      (uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode (n + 1))))) ∨
  (¬ TextbookEGuard m n ∧ output = (∅ : ZFSet.{u}))

@[simp]
theorem satisfies_anyCodeGuard_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem anyCodeGuard
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      TextbookEGuard m n := by
  simp only [anyCodeGuard, FOFormula.satisfies_disj,
    satisfies_codeGuard_standard]
  simp [TextbookEGuard]

@[simp]
theorem satisfies_stepFallback_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem stepFallback
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ¬ TextbookEGuard m n ∧ output = (∅ : ZFSet.{u}) := by
  simp [stepFallback]

@[simp]
theorem satisfies_stepBranches_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (.disj stepBranchZero <|
          .disj stepBranchOne <|
          .disj stepBranchTwo <|
          .disj stepBranchThree <|
          .disj stepBranchFour stepFallback)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      TextbookEBranchResult a history output m n := by
  simp only [FOFormula.satisfies_disj,
    satisfies_stepBranchZero_standard,
    satisfies_stepBranchOne_standard,
    satisfies_stepBranchTwo_standard,
    satisfies_stepBranchThree_standard,
    satisfies_stepBranchFour_standard,
    satisfies_stepFallback_standard]
  rfl

theorem textbookEStep_eq_empty_of_not_guard
    (a history : ZFSet.{u}) (m n : Nat)
    (hguard : ¬ TextbookEGuard m n) :
    textbookEStep a (ZFSet.pair (natCode m) (natCode n)) history = ∅ := by
  unfold textbookEStep
  rw [textbookEKeyDecode_pair_natCode]
  simp only
  cases hdecode : textbookEDecode m with
  | none => rfl
  | some fields =>
      rcases fields with ⟨i, j, tag⟩
      have hspec := (textbookEDecode_eq_some_iff m i j tag).mp hdecode
      cases tag with
      | zero =>
          simp only
          by_cases hbounds : i < n ∧ j < n
          · exfalso
            apply hguard
            exact Or.inl ⟨i, j, hspec.2, hbounds.1, hbounds.2⟩
          · simp only [if_neg hbounds]
      | succ tag =>
          cases tag with
          | zero =>
              simp only
              by_cases hbounds : i < n ∧ j < n
              · exfalso
                apply hguard
                exact Or.inr <| Or.inl
                  ⟨i, j, by simpa using hspec.2, hbounds.1, hbounds.2⟩
              · simp only [if_neg hbounds]
          | succ tag =>
              cases tag with
              | zero =>
                  exfalso
                  apply hguard
                  exact Or.inr <| Or.inr <| Or.inl
                    ⟨i, j, by simpa using hspec.2⟩
              | succ tag =>
                  cases tag with
                  | zero =>
                      exfalso
                      apply hguard
                      exact Or.inr <| Or.inr <| Or.inr <| Or.inl
                        ⟨i, j, by simpa using hspec.2⟩
                  | succ tag =>
                      cases tag with
                      | zero =>
                          exfalso
                          apply hguard
                          exact Or.inr <| Or.inr <| Or.inr <| Or.inr
                            ⟨i, j, by simpa using hspec.2⟩
                      | succ tag =>
                          omega

theorem textbookEBranchResult_iff_step
    (a history output : ZFSet.{u}) (m n : Nat) :
    TextbookEBranchResult a history output m n ↔
      output = textbookEStep a
        (ZFSet.pair (natCode m) (natCode n)) history := by
  constructor
  · rintro (hzero | hone | htwo | hthree | hfour | hfallback)
    · rcases hzero with ⟨i, j, hm, hi, hj, houtput⟩
      rw [hm, textbookEStep_code_zero a history n i j hi hj]
      exact houtput
    · rcases hone with ⟨i, j, hm, hi, hj, houtput⟩
      rw [hm, textbookEStep_code_one a history n i j hi hj]
      exact houtput
    · rcases htwo with ⟨i, j, hm, houtput⟩
      rw [hm, textbookEStep_code_two]
      exact houtput
    · rcases hthree with ⟨i, j, hm, houtput⟩
      rw [hm, textbookEStep_code_three]
      exact houtput
    · rcases hfour with ⟨i, j, hm, houtput⟩
      rw [hm, textbookEStep_code_four]
      exact houtput
    · rw [hfallback.2,
        textbookEStep_eq_empty_of_not_guard a history m n hfallback.1]
  · intro houtput
    by_cases hguard : TextbookEGuard m n
    · rcases hguard with hzero | hone | htwo | hthree | hfour
      · rcases hzero with ⟨i, j, hm, hi, hj⟩
        left
        refine ⟨i, j, hm, hi, hj, ?_⟩
        calc
          output = textbookEStep a
              (ZFSet.pair (natCode m) (natCode n)) history := houtput
          _ = textbookDInCodeZF a (natCode n) (natCode i) (natCode j) := by
            rw [hm, textbookEStep_code_zero a history n i j hi hj]
      · right; left
        rcases hone with ⟨i, j, hm, hi, hj⟩
        refine ⟨i, j, hm, hi, hj, ?_⟩
        calc
          output = textbookEStep a
              (ZFSet.pair (natCode m) (natCode n)) history := houtput
          _ = textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) := by
            rw [hm, textbookEStep_code_one a history n i j hi hj]
      · right; right; left
        rcases htwo with ⟨i, j, hm⟩
        refine ⟨i, j, hm, ?_⟩
        calc
          output = textbookEStep a
              (ZFSet.pair (natCode m) (natCode n)) history := houtput
          _ = relativeDifferenceZF (ZFSet.funs (natCode n) a)
              (uniqueGraphLookupZF history
                (ZFSet.pair (natCode i) (natCode n))) := by
            rw [hm, textbookEStep_code_two]
      · right; right; right; left
        rcases hthree with ⟨i, j, hm⟩
        refine ⟨i, j, hm, ?_⟩
        calc
          output = textbookEStep a
              (ZFSet.pair (natCode m) (natCode n)) history := houtput
          _ = intersectionZF
              (uniqueGraphLookupZF history
                (ZFSet.pair (natCode i) (natCode n)))
              (uniqueGraphLookupZF history
                (ZFSet.pair (natCode j) (natCode n))) := by
            rw [hm, textbookEStep_code_three]
      · right; right; right; right; left
        rcases hfour with ⟨i, j, hm⟩
        refine ⟨i, j, hm, ?_⟩
        calc
          output = textbookEStep a
              (ZFSet.pair (natCode m) (natCode n)) history := houtput
          _ = textbookExistsProjCodeZF a (natCode n)
              (uniqueGraphLookupZF history
                (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
            rw [hm, textbookEStep_code_four]
    · right; right; right; right; right
      exact ⟨hguard,
        houtput.trans (textbookEStep_eq_empty_of_not_guard
          a history m n hguard)⟩

@[simp]
theorem satisfies_textbookEStepBody_standard
    (a key history output : ZFSet.{u}) (m n : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookEStepBody
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      key = ZFSet.pair (natCode m) (natCode n) ∧
        output = textbookEStep a
          (ZFSet.pair (natCode m) (natCode n)) history := by
  rw [textbookEStepBody]
  change
    (FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.standardOmegaAt (4 : Fin 7))
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ∧
      (natCode m : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet ∧
      (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet ∧
      FOFormula.Satisfies Delta0Formula.ZFMem
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)).toFO
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ∧
      FOFormula.Satisfies Delta0Formula.ZFMem
        (.disj stepBranchZero <|
          .disj stepBranchOne <|
          .disj stepBranchTwo <|
          .disj stepBranchThree <|
          .disj stepBranchFour stepFallback)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]) ↔ _
  rw [TextbookNatFormula.satisfies_standardOmegaAt_ambient_iff,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    satisfies_stepBranches_standard,
    textbookEBranchResult_iff_step]
  simp [IndexedSequenceZF.mem_omega_iff_exists_natCode]

/-- Exact ambient graph semantics.  The domain conjunct is explicit, so the
formula is false at every input outside the actual set `omega x omega`. -/
@[simp]
theorem satisfies_textbookEStepFormula_iff
    (a key history output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookEStepFormula
        ![a, key, history, output] ↔
      key ∈ TextbookEDomain ∧ output = textbookEStep a key history := by
  rw [textbookEStepFormula]
  simp only [FOFormula.Satisfies]
  have hassign (omega mSet nSet : ZFSet.{u}) :
      snoc (snoc (snoc ![a, key, history, output] omega) mSet) nSet =
        ![a, key, history, output, omega, mSet, nSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨omega, mSet, nSet, hbody⟩
    rw [hassign] at hbody
    have homega : omega = (Ordinal.omega0.toZFSet : ZFSet.{u}) := by
      have h := hbody.1
      simpa [TextbookNatFormula.satisfies_standardOmegaAt_ambient_iff] using h
    subst omega
    have hmOmega : mSet ∈ (Ordinal.omega0.toZFSet : ZFSet.{u}) :=
      hbody.2.1
    have hnOmega : nSet ∈ (Ordinal.omega0.toZFSet : ZFSet.{u}) :=
      hbody.2.2.1
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode mSet).mp
      hmOmega with ⟨m, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nSet).mp
      hnOmega with ⟨n, rfl⟩
    have hstandard :=
      (satisfies_textbookEStepBody_standard
        a key history output m n).mp hbody
    constructor
    · apply mem_textbookEDomain_iff.mpr
      exact ⟨natCode m,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode m)).mpr ⟨m, rfl⟩,
        natCode n,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode n)).mpr ⟨n, rfl⟩,
        hstandard.1⟩
    · simpa only [hstandard.1] using hstandard.2
  · rintro ⟨hkeyDomain, houtput⟩
    rcases exists_textbookEKeyDecode_of_mem_textbookEDomain hkeyDomain with
      ⟨m, n, _hdecode, hkey⟩
    refine ⟨(Ordinal.omega0.toZFSet : ZFSet.{u}),
      (natCode m : ZFSet.{u}), (natCode n : ZFSet.{u}), ?_⟩
    rw [hassign]
    apply (satisfies_textbookEStepBody_standard
      a key history output m n).mpr
    exact ⟨hkey, by simpa only [hkey] using houtput⟩

end TextbookEFormula

namespace Model

/-! ## Closure in transitive ZF models -/

@[simp]
theorem satisfiesIn_formula3At
    (M : Set ZFSet.{u}) (formula : FOFormula 3) {n : Nat}
    (x y z : Fin n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (TextbookEFormula.formula3At formula x y z) s ↔
      SatisfiesIn M formula ![s x, s y, s z] := by
  rw [TextbookEFormula.formula3At, satisfiesIn_rename]
  have hassign : (fun i => s (![x, y, z] i)) =
      ![s x, s y, s z] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

@[simp]
theorem satisfiesIn_formula4At
    (M : Set ZFSet.{u}) (formula : FOFormula 4) {n : Nat}
    (v w x y : Fin n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (TextbookEFormula.formula4At formula v w x y) s ↔
      SatisfiesIn M formula ![s v, s w, s x, s y] := by
  rw [TextbookEFormula.formula4At, satisfiesIn_rename]
  have hassign : (fun i => s (![v, w, x, y] i)) =
      ![s v, s w, s x, s y] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

@[simp]
theorem satisfiesIn_formula5At
    (M : Set ZFSet.{u}) (formula : FOFormula 5) {n : Nat}
    (v w x y z : Fin n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (TextbookEFormula.formula5At formula v w x y z) s ↔
      SatisfiesIn M formula ![s v, s w, s x, s y, s z] := by
  rw [TextbookEFormula.formula5At, satisfiesIn_rename]
  have hassign : (fun i => s (![v, w, x, y, z] i)) =
      ![s v, s w, s x, s y, s z] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

theorem satisfiesIn_codeGuardBody_natCode
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M)
    (literal : Nat) (bounded : Bool) (m n i j : Nat) :
    SatisfiesIn (M : Set ZFSet.{u})
        (TextbookEFormula.codeGuardBody literal bounded)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode literal] ↔
      m = textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  let s : Tuple ZFSet.{u} 10 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
      natCode i, natCode j, natCode literal]
  have hs : ∀ k, s k ∈ M := by
    intro k
    fin_cases k
    · exact ha
    · exact hkey
    · exact hhistory
    · exact houtput
    · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
    · exact natCode_mem_of_isTransitiveZFModel hM m
    · exact natCode_mem_of_isTransitiveZFModel hM n
    · exact natCode_mem_of_isTransitiveZFModel hM i
    · exact natCode_mem_of_isTransitiveZFModel hM j
    · exact natCode_mem_of_isTransitiveZFModel hM literal
  have htag := satisfiesIn_natLiteralDeltaAt_iff hM.1
    literal (9 : Fin 10) s hs
  have hcode :
      SatisfiesIn (M : Set ZFSet.{u})
          (TextbookNatFormula.textbookECodeFormulaAt
            (4 : Fin 10) (7 : Fin 10) (8 : Fin 10)
            (9 : Fin 10) (5 : Fin 10)) s ↔
        (natCode m : ZFSet.{u}) =
          natCode (textbookECode i j literal) := by
    rw [TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    simpa [s] using
      (TextbookNatFormula.satisfiesIn_textbookECodeFormula_natCode_iff
        hM i j literal (natCode_mem_of_isTransitiveZFModel hM m))
  change SatisfiesIn (M : Set ZFSet.{u})
      (TextbookEFormula.codeGuardBody literal bounded) s ↔ _
  rw [TextbookEFormula.codeGuardBody]
  cases bounded <;>
    simp [SatisfiesIn, htag, hcode, s,
      IndexedSequenceZF.mem_omega_iff_exists_natCode,
      IndexedSequenceZF.mem_natCode_iff_exists_lt,
      natCode_injective.eq_iff]

theorem satisfiesIn_codeGuard_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M)
    (literal : Nat) (bounded : Bool) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u})
        (TextbookEFormula.codeGuard literal bounded)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  rw [TextbookEFormula.codeGuard]
  simp only [SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, _hiM, jSet, _hjM, tagSet, _htagM, hbody⟩
    rw [hassign] at hbody
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
      hbody.1 with ⟨i, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
      hbody.2.1 with ⟨j, rfl⟩
    have hs : ∀ k : Fin 10,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet] k ∈ M := by
      intro k
      fin_cases k
      · exact ha
      · exact hkey
      · exact hhistory
      · exact houtput
      · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
      · exact natCode_mem_of_isTransitiveZFModel hM m
      · exact natCode_mem_of_isTransitiveZFModel hM n
      · exact natCode_mem_of_isTransitiveZFModel hM i
      · exact natCode_mem_of_isTransitiveZFModel hM j
      · exact _htagM
    have htag : tagSet = (natCode literal : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_iff hM.1
        literal (9 : Fin 10)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, tagSet] hs).mp hbody.2.2.1
    subst tagSet
    exact ⟨i, j,
      (satisfiesIn_codeGuardBody_natCode hM ha hkey hhistory houtput
        literal bounded m n i j).mp hbody⟩
  · rintro ⟨i, j, hcode⟩
    refine ⟨(natCode i : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM i,
      (natCode j : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM j,
      (natCode literal : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM literal, ?_⟩
    rw [hassign]
    exact (satisfiesIn_codeGuardBody_natCode hM ha hkey hhistory houtput
      literal bounded m n i j).mpr hcode

theorem exists_natCode_fields_of_satisfiesIn_codeGuardBody
    {M a key history output iSet jSet tagSet : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M)
    (hiSet : iSet ∈ M) (hjSet : jSet ∈ M) (htagSet : tagSet ∈ M)
    (literal : Nat) (bounded : Bool) (m n : Nat)
    (hbody : SatisfiesIn (M : Set ZFSet.{u})
      (TextbookEFormula.codeGuardBody literal bounded)
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet]) :
    ∃ i j : Nat,
      iSet = natCode i ∧ jSet = natCode j ∧ tagSet = natCode literal ∧
        m = textbookECode i j literal ∧
          (if bounded then i < n ∧ j < n else True) := by
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet).mp
    hbody.1 with ⟨i, hi⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet).mp
    hbody.2.1 with ⟨j, hj⟩
  have hs : ∀ k : Fin 10,
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet] k ∈ M := by
    intro k
    fin_cases k
    · exact ha
    · exact hkey
    · exact hhistory
    · exact houtput
    · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
    · exact natCode_mem_of_isTransitiveZFModel hM m
    · exact natCode_mem_of_isTransitiveZFModel hM n
    · exact hiSet
    · exact hjSet
    · exact htagSet
  have htag : tagSet = (natCode literal : ZFSet.{u}) :=
    (satisfiesIn_natLiteralDeltaAt_iff hM.1
      literal (9 : Fin 10)
      ![a, key, history, output,
        (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
        iSet, jSet, tagSet] hs).mp hbody.2.2.1
  subst iSet
  subst jSet
  subst tagSet
  exact ⟨i, j, rfl, rfl, rfl,
    (satisfiesIn_codeGuardBody_natCode hM ha hkey hhistory houtput
      literal bounded m n i j).mp hbody⟩

@[simp]
theorem satisfiesIn_stepBranchZero_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.stepBranchZero
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 0 ∧ i < n ∧ j < n ∧
        output = textbookDInCodeZF a (natCode n) (natCode i) (natCode j) := by
  rw [TextbookEFormula.stepBranchZero]
  simp only [SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard, hvalue⟩
    rw [hassign] at hguard hvalue
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody
      hM ha hkey hhistory houtput hiSet hjSet htagSet
      0 true m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, hi, hj⟩
    subst iSet
    subst jSet
    subst tagSet
    have hvalueEq : output =
        textbookDInCodeZF a (natCode n) (natCode i) (natCode j) := by
      rw [satisfiesIn_formula5At] at hvalue
      exact (satisfiesIn_dInOutputFormula_iff hM
        ha (natCode_mem_of_isTransitiveZFModel hM n)
        (natCode_mem_of_isTransitiveZFModel hM i)
        (natCode_mem_of_isTransitiveZFModel hM j) houtput).mp
          (by simpa using hvalue)
    exact ⟨i, j, hcode, hi, hj, hvalueEq⟩
  · rintro ⟨i, j, hcode, hi, hj, hvalue⟩
    refine ⟨(natCode i : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM i,
      (natCode j : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM j,
      (natCode 0 : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM 0, ?_, ?_⟩
    · rw [hassign]
      exact (satisfiesIn_codeGuardBody_natCode
        hM ha hkey hhistory houtput 0 true m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign, satisfiesIn_formula5At]
      exact (satisfiesIn_dInOutputFormula_iff hM
        ha (natCode_mem_of_isTransitiveZFModel hM n)
        (natCode_mem_of_isTransitiveZFModel hM i)
        (natCode_mem_of_isTransitiveZFModel hM j) houtput).mpr hvalue

@[simp]
theorem satisfiesIn_stepBranchOne_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.stepBranchOne
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 1 ∧ i < n ∧ j < n ∧
        output = textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) := by
  rw [TextbookEFormula.stepBranchOne]
  simp only [SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hassign (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard, hvalue⟩
    rw [hassign] at hguard hvalue
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody
      hM ha hkey hhistory houtput hiSet hjSet htagSet
      1 true m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, hi, hj⟩
    subst iSet
    subst jSet
    subst tagSet
    have hvalueEq : output =
        textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) := by
      rw [satisfiesIn_formula5At] at hvalue
      exact (satisfiesIn_dEqOutputFormula_iff hM
        ha (natCode_mem_of_isTransitiveZFModel hM n)
        (natCode_mem_of_isTransitiveZFModel hM i)
        (natCode_mem_of_isTransitiveZFModel hM j) houtput).mp
          (by simpa using hvalue)
    exact ⟨i, j, hcode, hi, hj, hvalueEq⟩
  · rintro ⟨i, j, hcode, hi, hj, hvalue⟩
    refine ⟨(natCode i : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM i,
      (natCode j : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM j,
      (natCode 1 : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM 1, ?_, ?_⟩
    · rw [hassign]
      exact (satisfiesIn_codeGuardBody_natCode
        hM ha hkey hhistory houtput 1 true m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign, satisfiesIn_formula5At]
      exact (satisfiesIn_dEqOutputFormula_iff hM
        ha (natCode_mem_of_isTransitiveZFModel hM n)
        (natCode_mem_of_isTransitiveZFModel hM i)
        (natCode_mem_of_isTransitiveZFModel hM j) houtput).mpr hvalue

theorem satisfiesIn_kuratowskiPairEqAt_iff_eStep
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (pair left right : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ k, s k ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair left right).toFO s ↔
      s pair = ZFSet.pair (s left) (s right) := by
  rw [satisfiesIn_delta0_iff hM
    (Delta0Formula.kuratowskiPairEqAt pair left right) s hs,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

theorem satisfiesIn_successorAt_iff_eStep
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (successor index : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ k, s k ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.successorAt successor index).toFO s ↔
      s successor = insert (s index) (s index) := by
  rw [satisfiesIn_delta0_iff hM
    (Delta0Formula.successorAt successor index) s hs,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_successorAt]

@[simp]
theorem satisfiesIn_stepBranchTwo_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.stepBranchTwo
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 2 ∧
        output = relativeDifferenceZF (ZFSet.funs (natCode n) a)
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n))) := by
  rw [TextbookEFormula.stepBranchTwo]
  simp only [SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hkeyAssignment (iSet jSet tagSet lookupKey : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] lookupKey =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey] := by
    funext k
    fin_cases k <;> rfl
  have hremovedAssignment
      (iSet jSet tagSet lookupKey removed : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey] removed =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey, removed] := by
    funext k
    fin_cases k <;> rfl
  have hspaceAssignment
      (iSet jSet tagSet lookupKey removed space : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey, removed] space =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, lookupKey, removed, space] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard,
      lookupKey, hlookupKeyM, hpair, removed, hremovedM, hlookup,
      space, hspaceM, hspaceFormula, hdifference⟩
    rw [hfields] at hguard hpair hlookup hspaceFormula hdifference
    rw [hkeyAssignment] at hpair hlookup hspaceFormula hdifference
    rw [hremovedAssignment] at hlookup hspaceFormula hdifference
    rw [hspaceAssignment] at hspaceFormula hdifference
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody
      hM ha hkey hhistory houtput hiSet hjSet htagSet
      2 false m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, _htrivial⟩
    subst iSet
    subst jSet
    subst tagSet
    have hpairArgs : ∀ k : Fin 11,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 2, lookupKey] k ∈ M := by
      intro k
      fin_cases k
      · exact ha
      · exact hkey
      · exact hhistory
      · exact houtput
      · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
      · exact natCode_mem_of_isTransitiveZFModel hM m
      · exact natCode_mem_of_isTransitiveZFModel hM n
      · exact natCode_mem_of_isTransitiveZFModel hM i
      · exact natCode_mem_of_isTransitiveZFModel hM j
      · exact natCode_mem_of_isTransitiveZFModel hM 2
      · exact hlookupKeyM
    have hlookupKey : lookupKey =
        ZFSet.pair (natCode i) (natCode n) := by
      exact (satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11)
        _ hpairArgs).mp hpair
    subst lookupKey
    have hremoved : removed = uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode n)) := by
      rw [satisfiesIn_formula3At] at hlookup
      exact (satisfiesIn_uniqueGraphLookupFormula_iff hM
        hhistory
        (kuratowskiPair_mem_of_isTransitiveZFModel hM
          (natCode_mem_of_isTransitiveZFModel hM i)
          (natCode_mem_of_isTransitiveZFModel hM n))
        hremovedM).mp (by simpa using hlookup)
    subst removed
    have hspaceValue : space = ZFSet.funs (natCode n) a := by
      rw [satisfiesIn_formula3At] at hspaceFormula
      have h := (satisfiesIn_finiteFunctionSpaceGraph_iff hM
        (natCode_mem_of_isTransitiveZFModel hM n) ha hspaceM).mp
          (by simpa using hspaceFormula)
      exact h.2
    subst space
    have hvalue : output =
        relativeDifferenceZF (ZFSet.funs (natCode n) a)
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n))) := by
      rw [satisfiesIn_formula3At] at hdifference
      exact (satisfiesIn_relativeDifferenceOutputFormula_iff hM
        hspaceM hremovedM houtput).mp (by simpa using hdifference)
    exact ⟨i, j, hcode, hvalue⟩
  · rintro ⟨i, j, hcode, hvalue⟩
    let lookupKey : ZFSet.{u} := ZFSet.pair (natCode i) (natCode n)
    have hlookupKeyM : lookupKey ∈ M :=
      kuratowskiPair_mem_of_isTransitiveZFModel hM
        (natCode_mem_of_isTransitiveZFModel hM i)
        (natCode_mem_of_isTransitiveZFModel hM n)
    let removed : ZFSet.{u} := uniqueGraphLookupZF history lookupKey
    have hremovedM : removed ∈ M :=
      uniqueGraphLookupZF_mem_of_isTransitiveZFModel
        hM hhistory hlookupKeyM
    let space : ZFSet.{u} := ZFSet.funs (natCode n) a
    have hspaceM : space ∈ M := by
      simpa [space, textbookTupleSpace] using
        textbookTupleSpace_mem_of_isTransitiveZFModel hM ha n
    refine ⟨(natCode i : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM i,
      (natCode j : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM j,
      (natCode 2 : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM 2, ?_,
      lookupKey, hlookupKeyM, ?_, removed, hremovedM, ?_,
      space, hspaceM, ?_, ?_⟩
    · rw [hfields]
      exact (satisfiesIn_codeGuardBody_natCode
        hM ha hkey hhistory houtput 2 false m n i j).mpr
          ⟨hcode, trivial⟩
    · rw [hfields, hkeyAssignment]
      apply (satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11) _ (by
        intro k
        fin_cases k
        · exact ha
        · exact hkey
        · exact hhistory
        · exact houtput
        · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
        · exact natCode_mem_of_isTransitiveZFModel hM m
        · exact natCode_mem_of_isTransitiveZFModel hM n
        · exact natCode_mem_of_isTransitiveZFModel hM i
        · exact natCode_mem_of_isTransitiveZFModel hM j
        · exact natCode_mem_of_isTransitiveZFModel hM 2
        · exact hlookupKeyM)).mpr
      simp [lookupKey]
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        satisfiesIn_formula3At]
      apply (satisfiesIn_uniqueGraphLookupFormula_iff hM
        hhistory hlookupKeyM hremovedM).mpr
      rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        hspaceAssignment, satisfiesIn_formula3At]
      apply (satisfiesIn_finiteFunctionSpaceGraph_iff hM
        (natCode_mem_of_isTransitiveZFModel hM n) ha hspaceM).mpr
      exact ⟨⟨n, rfl⟩, rfl⟩
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        hspaceAssignment, satisfiesIn_formula3At]
      apply (satisfiesIn_relativeDifferenceOutputFormula_iff
        hM hspaceM hremovedM houtput).mpr
      simpa [space, removed, lookupKey] using hvalue

@[simp]
theorem satisfiesIn_stepBranchThree_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.stepBranchThree
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 3 ∧
        output = intersectionZF
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode n)))
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode j) (natCode n))) := by
  rw [TextbookEFormula.stepBranchThree]
  simp only [SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hleftKeyAssignment (iSet jSet tagSet leftKey : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] leftKey =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey] := by
    funext k
    fin_cases k <;> rfl
  have hleftValueAssignment
      (iSet jSet tagSet leftKey leftValue : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey] leftValue =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue] := by
    funext k
    fin_cases k <;> rfl
  have hrightKeyAssignment
      (iSet jSet tagSet leftKey leftValue rightKey : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue] rightKey =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey] := by
    funext k
    fin_cases k <;> rfl
  have hrightValueAssignment
      (iSet jSet tagSet leftKey leftValue rightKey rightValue : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey] rightValue =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey, rightValue] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard,
      leftKey, hleftKeyM, hleftPair, leftValue, hleftValueM, hleftLookup,
      rightKey, hrightKeyM, hrightPair, rightValue, hrightValueM,
      hrightLookup, hintersection⟩
    rw [hfields] at hguard hleftPair hleftLookup hrightPair hrightLookup hintersection
    rw [hleftKeyAssignment] at hleftPair hleftLookup hrightPair hrightLookup hintersection
    rw [hleftValueAssignment] at hleftLookup hrightPair hrightLookup hintersection
    rw [hrightKeyAssignment] at hrightPair hrightLookup hintersection
    rw [hrightValueAssignment] at hrightLookup hintersection
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody
      hM ha hkey hhistory houtput hiSet hjSet htagSet
      3 false m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, _htrivial⟩
    subst iSet
    subst jSet
    subst tagSet
    have hleftArgs : ∀ k : Fin 11,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 3, leftKey] k ∈ M := by
      intro k
      fin_cases k
      · exact ha
      · exact hkey
      · exact hhistory
      · exact houtput
      · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
      · exact natCode_mem_of_isTransitiveZFModel hM m
      · exact natCode_mem_of_isTransitiveZFModel hM n
      · exact natCode_mem_of_isTransitiveZFModel hM i
      · exact natCode_mem_of_isTransitiveZFModel hM j
      · exact natCode_mem_of_isTransitiveZFModel hM 3
      · exact hleftKeyM
    have hleftKey : leftKey =
        ZFSet.pair (natCode i) (natCode n) :=
      (satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11) _ hleftArgs).mp hleftPair
    subst leftKey
    have hleftValue : leftValue = uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode n)) := by
      rw [satisfiesIn_formula3At] at hleftLookup
      exact (satisfiesIn_uniqueGraphLookupFormula_iff hM
        hhistory hleftKeyM hleftValueM).mp (by simpa using hleftLookup)
    subst leftValue
    have hrightArgs : ∀ k : Fin 13,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 3,
          ZFSet.pair (natCode i) (natCode n),
          uniqueGraphLookupZF history (ZFSet.pair (natCode i) (natCode n)),
          rightKey] k ∈ M := by
      intro k
      fin_cases k
      · exact ha
      · exact hkey
      · exact hhistory
      · exact houtput
      · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
      · exact natCode_mem_of_isTransitiveZFModel hM m
      · exact natCode_mem_of_isTransitiveZFModel hM n
      · exact natCode_mem_of_isTransitiveZFModel hM i
      · exact natCode_mem_of_isTransitiveZFModel hM j
      · exact natCode_mem_of_isTransitiveZFModel hM 3
      · exact hleftKeyM
      · exact hleftValueM
      · exact hrightKeyM
    have hrightKey : rightKey =
        ZFSet.pair (natCode j) (natCode n) :=
      (satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
        (Fin.last 12) (8 : Fin 13) (6 : Fin 13) _ hrightArgs).mp hrightPair
    subst rightKey
    have hrightValue : rightValue = uniqueGraphLookupZF history
        (ZFSet.pair (natCode j) (natCode n)) := by
      rw [satisfiesIn_formula3At] at hrightLookup
      exact (satisfiesIn_uniqueGraphLookupFormula_iff hM
        hhistory hrightKeyM hrightValueM).mp (by simpa using hrightLookup)
    subst rightValue
    have hvalue : output = intersectionZF
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode n)))
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode j) (natCode n))) := by
      rw [satisfiesIn_formula3At] at hintersection
      exact (satisfiesIn_intersectionOutputFormula_iff hM
        hleftValueM hrightValueM houtput).mp (by simpa using hintersection)
    exact ⟨i, j, hcode, hvalue⟩
  · rintro ⟨i, j, hcode, hvalue⟩
    let leftKey : ZFSet.{u} := ZFSet.pair (natCode i) (natCode n)
    have hleftKeyM : leftKey ∈ M :=
      kuratowskiPair_mem_of_isTransitiveZFModel hM
        (natCode_mem_of_isTransitiveZFModel hM i)
        (natCode_mem_of_isTransitiveZFModel hM n)
    let leftValue : ZFSet.{u} := uniqueGraphLookupZF history leftKey
    have hleftValueM : leftValue ∈ M :=
      uniqueGraphLookupZF_mem_of_isTransitiveZFModel hM hhistory hleftKeyM
    let rightKey : ZFSet.{u} := ZFSet.pair (natCode j) (natCode n)
    have hrightKeyM : rightKey ∈ M :=
      kuratowskiPair_mem_of_isTransitiveZFModel hM
        (natCode_mem_of_isTransitiveZFModel hM j)
        (natCode_mem_of_isTransitiveZFModel hM n)
    let rightValue : ZFSet.{u} := uniqueGraphLookupZF history rightKey
    have hrightValueM : rightValue ∈ M :=
      uniqueGraphLookupZF_mem_of_isTransitiveZFModel hM hhistory hrightKeyM
    refine ⟨(natCode i : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM i,
      (natCode j : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM j,
      (natCode 3 : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM 3, ?_,
      leftKey, hleftKeyM, ?_, leftValue, hleftValueM, ?_,
      rightKey, hrightKeyM, ?_, rightValue, hrightValueM, ?_, ?_⟩
    · rw [hfields]
      exact (satisfiesIn_codeGuardBody_natCode
        hM ha hkey hhistory houtput 3 false m n i j).mpr
          ⟨hcode, trivial⟩
    · rw [hfields, hleftKeyAssignment]
      apply (satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
        (Fin.last 10) (7 : Fin 11) (6 : Fin 11) _ (by
          intro k
          fin_cases k
          · exact ha
          · exact hkey
          · exact hhistory
          · exact houtput
          · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
          · exact natCode_mem_of_isTransitiveZFModel hM m
          · exact natCode_mem_of_isTransitiveZFModel hM n
          · exact natCode_mem_of_isTransitiveZFModel hM i
          · exact natCode_mem_of_isTransitiveZFModel hM j
          · exact natCode_mem_of_isTransitiveZFModel hM 3
          · exact hleftKeyM)).mpr
      simp [leftKey]
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        satisfiesIn_formula3At]
      exact (satisfiesIn_uniqueGraphLookupFormula_iff hM
        hhistory hleftKeyM hleftValueM).mpr rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment]
      apply (satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
        (Fin.last 12) (8 : Fin 13) (6 : Fin 13) _ (by
          intro k
          fin_cases k
          · exact ha
          · exact hkey
          · exact hhistory
          · exact houtput
          · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
          · exact natCode_mem_of_isTransitiveZFModel hM m
          · exact natCode_mem_of_isTransitiveZFModel hM n
          · exact natCode_mem_of_isTransitiveZFModel hM i
          · exact natCode_mem_of_isTransitiveZFModel hM j
          · exact natCode_mem_of_isTransitiveZFModel hM 3
          · exact hleftKeyM
          · exact hleftValueM
          · exact hrightKeyM)).mpr
      simp [rightKey]
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment,
        satisfiesIn_formula3At]
      exact (satisfiesIn_uniqueGraphLookupFormula_iff hM
        hhistory hrightKeyM hrightValueM).mpr rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment,
        satisfiesIn_formula3At]
      apply (satisfiesIn_intersectionOutputFormula_iff hM
        hleftValueM hrightValueM houtput).mpr
      simpa [leftValue, leftKey, rightValue, rightKey] using hvalue

@[simp]
theorem satisfiesIn_stepBranchFour_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.stepBranchFour
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ∃ i j : Nat, m = textbookECode i j 4 ∧
        output = textbookExistsProjCodeZF a (natCode n)
          (uniqueGraphLookupZF history
            (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
  rw [TextbookEFormula.stepBranchFour]
  simp only [SatisfiesIn]
  let base : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hfields (iSet jSet tagSet : ZFSet.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hsuccAssignment (iSet jSet tagSet succN : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet] succN =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN] := by
    funext k
    fin_cases k <;> rfl
  have hkeyAssignment
      (iSet jSet tagSet succN lookupKey : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN] lookupKey =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN, lookupKey] := by
    funext k
    fin_cases k <;> rfl
  have hrelationAssignment
      (iSet jSet tagSet succN lookupKey relation : ZFSet.{u}) :
      snoc
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN, lookupKey] relation =
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          iSet, jSet, tagSet, succN, lookupKey, relation] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, hiSet, jSet, hjSet, tagSet, htagSet, hguard,
      succN, hsuccM, hsucc, lookupKey, hlookupKeyM, hpair,
      relation, hrelationM, hlookup, hprojection⟩
    rw [hfields] at hguard hsucc hpair hlookup hprojection
    rw [hsuccAssignment] at hsucc hpair hlookup hprojection
    rw [hkeyAssignment] at hpair hlookup hprojection
    rw [hrelationAssignment] at hlookup hprojection
    rcases exists_natCode_fields_of_satisfiesIn_codeGuardBody
      hM ha hkey hhistory houtput hiSet hjSet htagSet
      4 false m n hguard with
      ⟨i, j, hiEq, hjEq, htagEq, hcode, _htrivial⟩
    subst iSet
    subst jSet
    subst tagSet
    have hsuccArgs : ∀ k : Fin 11,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 4, succN] k ∈ M := by
      intro k
      fin_cases k
      · exact ha
      · exact hkey
      · exact hhistory
      · exact houtput
      · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
      · exact natCode_mem_of_isTransitiveZFModel hM m
      · exact natCode_mem_of_isTransitiveZFModel hM n
      · exact natCode_mem_of_isTransitiveZFModel hM i
      · exact natCode_mem_of_isTransitiveZFModel hM j
      · exact natCode_mem_of_isTransitiveZFModel hM 4
      · exact hsuccM
    have hsuccN : succN = (natCode (n + 1) : ZFSet.{u}) := by
      have h := (satisfiesIn_successorAt_iff_eStep hM.1
        (Fin.last 10) (6 : Fin 11) _ hsuccArgs).mp hsucc
      simpa [natCode_succ_eq_insert] using h
    subst succN
    have hpairArgs : ∀ k : Fin 12,
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n,
          natCode i, natCode j, natCode 4, natCode (n + 1), lookupKey]
          k ∈ M := by
      intro k
      fin_cases k
      · exact ha
      · exact hkey
      · exact hhistory
      · exact houtput
      · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
      · exact natCode_mem_of_isTransitiveZFModel hM m
      · exact natCode_mem_of_isTransitiveZFModel hM n
      · exact natCode_mem_of_isTransitiveZFModel hM i
      · exact natCode_mem_of_isTransitiveZFModel hM j
      · exact natCode_mem_of_isTransitiveZFModel hM 4
      · exact hsuccM
      · exact hlookupKeyM
    have hlookupKey : lookupKey =
        ZFSet.pair (natCode i) (natCode (n + 1)) :=
      (satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
        (Fin.last 11) (7 : Fin 12) (10 : Fin 12) _ hpairArgs).mp hpair
    subst lookupKey
    have hrelation : relation = uniqueGraphLookupZF history
        (ZFSet.pair (natCode i) (natCode (n + 1))) := by
      rw [satisfiesIn_formula3At] at hlookup
      exact (satisfiesIn_uniqueGraphLookupFormula_iff hM
        hhistory hlookupKeyM hrelationM).mp (by simpa using hlookup)
    subst relation
    have hvalue : output = textbookExistsProjCodeZF a (natCode n)
        (uniqueGraphLookupZF history
          (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
      rw [satisfiesIn_formula4At] at hprojection
      exact (satisfiesIn_existsProjOutputFormula_iff hM
        ha (natCode_mem_of_isTransitiveZFModel hM n)
        hrelationM houtput).mp (by simpa using hprojection)
    exact ⟨i, j, hcode, hvalue⟩
  · rintro ⟨i, j, hcode, hvalue⟩
    let succN : ZFSet.{u} := natCode (n + 1)
    have hsuccM : succN ∈ M :=
      natCode_mem_of_isTransitiveZFModel hM (n + 1)
    let lookupKey : ZFSet.{u} := ZFSet.pair (natCode i) succN
    have hlookupKeyM : lookupKey ∈ M :=
      kuratowskiPair_mem_of_isTransitiveZFModel hM
        (natCode_mem_of_isTransitiveZFModel hM i) hsuccM
    let relation : ZFSet.{u} := uniqueGraphLookupZF history lookupKey
    have hrelationM : relation ∈ M :=
      uniqueGraphLookupZF_mem_of_isTransitiveZFModel
        hM hhistory hlookupKeyM
    refine ⟨(natCode i : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM i,
      (natCode j : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM j,
      (natCode 4 : ZFSet.{u}),
      natCode_mem_of_isTransitiveZFModel hM 4, ?_,
      succN, hsuccM, ?_, lookupKey, hlookupKeyM, ?_,
      relation, hrelationM, ?_, ?_⟩
    · rw [hfields]
      exact (satisfiesIn_codeGuardBody_natCode
        hM ha hkey hhistory houtput 4 false m n i j).mpr
          ⟨hcode, trivial⟩
    · rw [hfields, hsuccAssignment]
      apply (satisfiesIn_successorAt_iff_eStep hM.1
        (Fin.last 10) (6 : Fin 11) _ (by
          intro k
          fin_cases k
          · exact ha
          · exact hkey
          · exact hhistory
          · exact houtput
          · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
          · exact natCode_mem_of_isTransitiveZFModel hM m
          · exact natCode_mem_of_isTransitiveZFModel hM n
          · exact natCode_mem_of_isTransitiveZFModel hM i
          · exact natCode_mem_of_isTransitiveZFModel hM j
          · exact natCode_mem_of_isTransitiveZFModel hM 4
          · exact hsuccM)).mpr
      simp [succN, natCode_succ_eq_insert]
    · rw [hfields, hsuccAssignment, hkeyAssignment]
      apply (satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
        (Fin.last 11) (7 : Fin 12) (10 : Fin 12) _ (by
          intro k
          fin_cases k
          · exact ha
          · exact hkey
          · exact hhistory
          · exact houtput
          · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
          · exact natCode_mem_of_isTransitiveZFModel hM m
          · exact natCode_mem_of_isTransitiveZFModel hM n
          · exact natCode_mem_of_isTransitiveZFModel hM i
          · exact natCode_mem_of_isTransitiveZFModel hM j
          · exact natCode_mem_of_isTransitiveZFModel hM 4
          · exact hsuccM
          · exact hlookupKeyM)).mpr
      simp [lookupKey]
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment, satisfiesIn_formula3At]
      exact (satisfiesIn_uniqueGraphLookupFormula_iff hM
        hhistory hlookupKeyM hrelationM).mpr rfl
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment, satisfiesIn_formula4At]
      apply (satisfiesIn_existsProjOutputFormula_iff hM
        ha (natCode_mem_of_isTransitiveZFModel hM n)
        hrelationM houtput).mpr
      simpa [relation, lookupKey, succN] using hvalue

 theorem satisfiesIn_eStepDisj_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (.disj left right) s ↔
      SatisfiesIn M left s ∨ SatisfiesIn M right s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

@[simp]
theorem satisfiesIn_anyCodeGuard_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.anyCodeGuard
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      TextbookEFormula.TextbookEGuard m n := by
  rw [TextbookEFormula.anyCodeGuard]
  repeat' rw [satisfiesIn_eStepDisj_iff]
  rw [satisfiesIn_codeGuard_standard hM ha hkey hhistory houtput,
    satisfiesIn_codeGuard_standard hM ha hkey hhistory houtput,
    satisfiesIn_codeGuard_standard hM ha hkey hhistory houtput,
    satisfiesIn_codeGuard_standard hM ha hkey hhistory houtput,
    satisfiesIn_codeGuard_standard hM ha hkey hhistory houtput]
  simp [TextbookEFormula.TextbookEGuard]

@[simp]
theorem satisfiesIn_stepFallback_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.stepFallback
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      ¬ TextbookEFormula.TextbookEGuard m n ∧
        output = (∅ : ZFSet.{u}) := by
  let s : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hs : ∀ k, s k ∈ M := by
    intro k
    fin_cases k
    · exact ha
    · exact hkey
    · exact hhistory
    · exact houtput
    · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
    · exact natCode_mem_of_isTransitiveZFModel hM m
    · exact natCode_mem_of_isTransitiveZFModel hM n
  have hempty := satisfiesIn_delta0_iff hM.1
    (Delta0Formula.emptyDeltaAt (3 : Fin 7)) s hs
  change SatisfiesIn (M : Set ZFSet.{u})
      TextbookEFormula.stepFallback s ↔ _
  rw [TextbookEFormula.stepFallback]
  simp only [SatisfiesIn]
  rw [satisfiesIn_anyCodeGuard_standard hM ha hkey hhistory houtput]
  rw [hempty, Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_emptyDeltaAt]
  rfl

@[simp]
theorem satisfiesIn_stepBranches_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u})
        (.disj TextbookEFormula.stepBranchZero <|
          .disj TextbookEFormula.stepBranchOne <|
          .disj TextbookEFormula.stepBranchTwo <|
          .disj TextbookEFormula.stepBranchThree <|
          .disj TextbookEFormula.stepBranchFour TextbookEFormula.stepFallback)
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      TextbookEFormula.TextbookEBranchResult a history output m n := by
  repeat' rw [satisfiesIn_eStepDisj_iff]
  rw [satisfiesIn_stepBranchZero_standard hM ha hkey hhistory houtput,
    satisfiesIn_stepBranchOne_standard hM ha hkey hhistory houtput,
    satisfiesIn_stepBranchTwo_standard hM ha hkey hhistory houtput,
    satisfiesIn_stepBranchThree_standard hM ha hkey hhistory houtput,
    satisfiesIn_stepBranchFour_standard hM ha hkey hhistory houtput,
    satisfiesIn_stepFallback_standard hM ha hkey hhistory houtput]
  rfl

@[simp]
theorem satisfiesIn_textbookEStepBody_standard
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) (m n : Nat) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.textbookEStepBody
        ![a, key, history, output,
          (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n] ↔
      key = ZFSet.pair (natCode m) (natCode n) ∧
        output = textbookEStep a
          (ZFSet.pair (natCode m) (natCode n)) history := by
  rw [TextbookEFormula.textbookEStepBody]
  let s : Tuple ZFSet.{u} 7 :=
    ![a, key, history, output,
      (Ordinal.omega0.toZFSet : ZFSet.{u}), natCode m, natCode n]
  have hs : ∀ k, s k ∈ M := by
    intro k
    fin_cases k
    · exact ha
    · exact hkey
    · exact hhistory
    · exact houtput
    · exact omega_toZFSet_mem_of_isTransitiveZFModel hM
    · exact natCode_mem_of_isTransitiveZFModel hM m
    · exact natCode_mem_of_isTransitiveZFModel hM n
  change
    (SatisfiesIn (M : Set ZFSet.{u})
        (standardOmegaAt (4 : Fin 7)) s ∧
      (natCode m : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet ∧
      (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)).toFO s ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (.disj TextbookEFormula.stepBranchZero <|
          .disj TextbookEFormula.stepBranchOne <|
          .disj TextbookEFormula.stepBranchTwo <|
          .disj TextbookEFormula.stepBranchThree <|
          .disj TextbookEFormula.stepBranchFour TextbookEFormula.stepFallback)
        s) ↔ _
  rw [satisfiesIn_standardOmegaAt_iff hM (4 : Fin 7) s hs,
    satisfiesIn_kuratowskiPairEqAt_iff_eStep hM.1
      (1 : Fin 7) (5 : Fin 7) (6 : Fin 7) s hs,
    satisfiesIn_stepBranches_standard hM ha hkey hhistory houtput,
    TextbookEFormula.textbookEBranchResult_iff_step]
  simp [s, IndexedSequenceZF.mem_omega_iff_exists_natCode]

/-- Exact restricted semantics of the complete E-step graph. -/
@[simp]
theorem satisfiesIn_textbookEStepFormula_iff
    {M a key history output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hkey : key ∈ M) (hhistory : history ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) TextbookEFormula.textbookEStepFormula
        ![a, key, history, output] ↔
      key ∈ TextbookEDomain ∧ output = textbookEStep a key history := by
  rw [TextbookEFormula.textbookEStepFormula]
  simp only [SatisfiesIn]
  have hassign (omega mSet nSet : ZFSet.{u}) :
      snoc (snoc (snoc ![a, key, history, output] omega) mSet) nSet =
        ![a, key, history, output, omega, mSet, nSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨omega, homegaM, mSet, hmSetM, nSet, hnSetM, hbody⟩
    rw [hassign] at hbody
    have hs : ∀ k : Fin 7,
        ![a, key, history, output, omega, mSet, nSet] k ∈ M := by
      intro k
      fin_cases k
      · exact ha
      · exact hkey
      · exact hhistory
      · exact houtput
      · exact homegaM
      · exact hmSetM
      · exact hnSetM
    have homega : omega = (Ordinal.omega0.toZFSet : ZFSet.{u}) :=
      (satisfiesIn_standardOmegaAt_iff hM (4 : Fin 7)
        ![a, key, history, output, omega, mSet, nSet] hs).mp hbody.1
    subst omega
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode mSet).mp
      hbody.2.1 with ⟨m, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nSet).mp
      hbody.2.2.1 with ⟨n, rfl⟩
    have hstandard := (satisfiesIn_textbookEStepBody_standard
      hM ha hkey hhistory houtput m n).mp hbody
    constructor
    · apply mem_textbookEDomain_iff.mpr
      exact ⟨natCode m,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode m)).mpr ⟨m, rfl⟩,
        natCode n,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode n)).mpr ⟨n, rfl⟩,
        hstandard.1⟩
    · simpa only [hstandard.1] using hstandard.2
  · rintro ⟨hkeyDomain, hvalue⟩
    rcases exists_textbookEKeyDecode_of_mem_textbookEDomain hkeyDomain with
      ⟨m, n, _hdecode, hkeyEq⟩
    refine ⟨(Ordinal.omega0.toZFSet : ZFSet.{u}),
      omega_toZFSet_mem_of_isTransitiveZFModel hM,
      (natCode m : ZFSet.{u}), natCode_mem_of_isTransitiveZFModel hM m,
      (natCode n : ZFSet.{u}), natCode_mem_of_isTransitiveZFModel hM n, ?_⟩
    rw [hassign]
    apply (satisfiesIn_textbookEStepBody_standard
      hM ha hkey hhistory houtput m n).mpr
    exact ⟨hkeyEq, by simpa only [hkeyEq] using hvalue⟩





end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEStep


