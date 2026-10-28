-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library14
-- name    : CH_ConstructibleGCH_Library14
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:47:52.229975+00:00
-- url     : https://prove2.me/theorems/500f72d2-b2c2-4f4c-a18d-0836bcf8b351
-- title:
--   Absolute atomic and Boolean relation formulas
-- statement:
--   This library supplies the realization interfaces for atomic relations, coordinate projections and Boolean operations in finite-tuple descriptions. These elementary constructors support the later definability enumeration.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookAtomicAbsolute.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookProjectionAbsolute.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookBooleanAbsolute.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library13
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookAtomicAbsolute -/
section GCHSource_Work_CUGCH_TextbookAtomicAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Absoluteness of the textbook atomic relation generators

This file gives first-order graph formulas for the total set-coded operations
`textbookDInCodeZF` and `textbookDEqCodeZF`.  The standard-finite guard occurs
inside the extensional membership condition.  Consequently an invalid arity
has the uniquely specified empty output, rather than merely lying outside the
domain of the graph formula.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookDefFormula

/-! ## Bounded membership predicates -/

/-- A candidate finite function graph belongs to `D_in(a,n,i,j)`. -/
def dInMemberDeltaAt {n : Nat}
    (a arity left right graph : Fin n) : Delta0Formula n :=
  .conj (.mem left arity)
    (.conj (.mem right arity)
      (.conj (isFunctionDeltaAt graph arity a)
        (Delta0Formula.boundedEx a
          (Delta0Formula.boundedEx a.castSucc
            (.conj
              (graphValueDeltaAt graph.castSucc.castSucc
                left.castSucc.castSucc (Fin.last n).castSucc)
              (.conj
                (graphValueDeltaAt graph.castSucc.castSucc
                  right.castSucc.castSucc (Fin.last (n + 1)))
                (.mem (Fin.last n).castSucc (Fin.last (n + 1)))))))))

@[simp]
theorem satisfies_dInMemberDeltaAt {n : Nat}
    (a arity left right graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (dInMemberDeltaAt a arity left right graph) s ↔
      s left ∈ s arity ∧ s right ∈ s arity ∧
        ZFSet.IsFunc (s arity) (s a) (s graph) ∧
          ∃ x ∈ s a, ∃ y ∈ s a,
            ZFSet.pair (s left) x ∈ s graph ∧
              ZFSet.pair (s right) y ∈ s graph ∧ x ∈ y := by
  simp [dInMemberDeltaAt]

/-- A candidate finite function graph belongs to `D_eq(a,n,i,j)`. -/
def dEqMemberDeltaAt {n : Nat}
    (a arity left right graph : Fin n) : Delta0Formula n :=
  .conj (.mem left arity)
    (.conj (.mem right arity)
      (.conj (isFunctionDeltaAt graph arity a)
        (Delta0Formula.boundedEx a
          (.conj
            (graphValueDeltaAt graph.castSucc left.castSucc (Fin.last n))
            (graphValueDeltaAt graph.castSucc right.castSucc
              (Fin.last n))))))

@[simp]
theorem satisfies_dEqMemberDeltaAt {n : Nat}
    (a arity left right graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (dEqMemberDeltaAt a arity left right graph) s ↔
      s left ∈ s arity ∧ s right ∈ s arity ∧
        ZFSet.IsFunc (s arity) (s a) (s graph) ∧
          ∃ x ∈ s a,
            ZFSet.pair (s left) x ∈ s graph ∧
              ZFSet.pair (s right) x ∈ s graph := by
  simp [dEqMemberDeltaAt]

/-- Layout `[a, arity, left, right, graph]`. -/
def dInMemberDelta : Delta0Formula 5 :=
  dInMemberDeltaAt
    (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5)

/-- Layout `[a, arity, left, right, graph]`. -/
def dEqMemberDelta : Delta0Formula 5 :=
  dEqMemberDeltaAt
    (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5)

@[simp]
theorem satisfies_dInMemberDelta
    (a arity left right graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem dInMemberDelta
        ![a, arity, left, right, graph] ↔
      left ∈ arity ∧ right ∈ arity ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ x ∈ a, ∃ y ∈ a,
            ZFSet.pair left x ∈ graph ∧
              ZFSet.pair right y ∈ graph ∧ x ∈ y := by
  simp [dInMemberDelta]

@[simp]
theorem satisfies_dEqMemberDelta
    (a arity left right graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem dEqMemberDelta
        ![a, arity, left, right, graph] ↔
      left ∈ arity ∧ right ∈ arity ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ x ∈ a,
            ZFSet.pair left x ∈ graph ∧
              ZFSet.pair right x ∈ graph := by
  simp [dEqMemberDelta]

/-! ## Extensional output formulas -/

/-- The right-hand side of the extensional definition of `D_in` membership.
Layout `[a, arity, left, right, output, candidate]`; `output` is unused. -/
def dInOutputMemberCondition : FOFormula 6 :=
  .conj
    (Model.standardFiniteDomainAt (1 : Fin 6))
    (dInMemberDeltaAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (Fin.last 5)).toFO

/-- The right-hand side of the extensional definition of `D_eq` membership.
Layout `[a, arity, left, right, output, candidate]`; `output` is unused. -/
def dEqOutputMemberCondition : FOFormula 6 :=
  .conj
    (Model.standardFiniteDomainAt (1 : Fin 6))
    (dEqMemberDeltaAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (Fin.last 5)).toFO

/-- Layout `[a, arity, left, right, output]`. -/
def dInOutputFormula : FOFormula 5 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      dInOutputMemberCondition)

/-- Layout `[a, arity, left, right, output]`. -/
def dEqOutputFormula : FOFormula 5 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      dEqOutputMemberCondition)

end TextbookDefFormula

/-! ## Exact ambient specifications of the totalized operations -/

@[simp]
theorem mem_textbookDInCodeZF_iff
    {a arity left right graph : ZFSet.{u}} :
    graph ∈ textbookDInCodeZF a arity left right ↔
      (∃ n : Nat, arity = natCode n) ∧
        left ∈ arity ∧ right ∈ arity ∧
          ZFSet.IsFunc arity a graph ∧
            ∃ x ∈ a, ∃ y ∈ a,
              ZFSet.pair left x ∈ graph ∧
                ZFSet.pair right y ∈ graph ∧ x ∈ y := by
  constructor
  · intro hgraph
    unfold textbookDInCodeZF at hgraph
    cases harity : textbookNatDecode arity with
    | none => simp [harity] at hgraph
    | some n =>
        cases hleft : textbookNatDecode left with
        | none => simp [harity, hleft] at hgraph
        | some i =>
            cases hright : textbookNatDecode right with
            | none => simp [harity, hleft, hright] at hgraph
            | some j =>
                simp only [harity, hleft, hright] at hgraph
                have harityEq : arity = natCode n :=
                  textbookNatDecode_eq_some_iff.mp harity
                have hleftEq : left = natCode i :=
                  textbookNatDecode_eq_some_iff.mp hleft
                have hrightEq : right = natCode j :=
                  textbookNatDecode_eq_some_iff.mp hright
                subst arity
                subst left
                subst right
                rcases mem_textbookDInZF_iff.mp hgraph with
                  ⟨hspace, hi, hj, x, y, hx, hy, hxy⟩
                have hfunc : ZFSet.IsFunc (natCode n) a graph :=
                  mem_textbookTupleSpace_iff.mp hspace
                have hxa : x ∈ a :=
                  (ZFSet.pair_mem_prod.mp (hfunc.1 hx)).2
                have hya : y ∈ a :=
                  (ZFSet.pair_mem_prod.mp (hfunc.1 hy)).2
                exact ⟨⟨n, rfl⟩,
                  (natCode_mem_natCode_iff i n).mpr hi,
                  (natCode_mem_natCode_iff j n).mpr hj,
                  hfunc, x, hxa, y, hya, hx, hy, hxy⟩
  · rintro ⟨⟨n, rfl⟩, hleft, hright, hfunc,
      x, hxa, y, hya, hx, hy, hxy⟩
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt left n).mp hleft with
      ⟨i, hi, rfl⟩
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt right n).mp hright with
      ⟨j, hj, rfl⟩
    rw [textbookDInCodeZF_natCode, mem_textbookDInZF_iff]
    exact ⟨mem_textbookTupleSpace_iff.mpr hfunc,
      hi, hj, x, y, hx, hy, hxy⟩

@[simp]
theorem mem_textbookDEqCodeZF_iff
    {a arity left right graph : ZFSet.{u}} :
    graph ∈ textbookDEqCodeZF a arity left right ↔
      (∃ n : Nat, arity = natCode n) ∧
        left ∈ arity ∧ right ∈ arity ∧
          ZFSet.IsFunc arity a graph ∧
            ∃ x ∈ a,
              ZFSet.pair left x ∈ graph ∧
                ZFSet.pair right x ∈ graph := by
  constructor
  · intro hgraph
    unfold textbookDEqCodeZF at hgraph
    cases harity : textbookNatDecode arity with
    | none => simp [harity] at hgraph
    | some n =>
        cases hleft : textbookNatDecode left with
        | none => simp [harity, hleft] at hgraph
        | some i =>
            cases hright : textbookNatDecode right with
            | none => simp [harity, hleft, hright] at hgraph
            | some j =>
                simp only [harity, hleft, hright] at hgraph
                have harityEq : arity = natCode n :=
                  textbookNatDecode_eq_some_iff.mp harity
                have hleftEq : left = natCode i :=
                  textbookNatDecode_eq_some_iff.mp hleft
                have hrightEq : right = natCode j :=
                  textbookNatDecode_eq_some_iff.mp hright
                subst arity
                subst left
                subst right
                rcases mem_textbookDEqZF_iff.mp hgraph with
                  ⟨hspace, hi, hj, x, hx, hx'⟩
                have hfunc : ZFSet.IsFunc (natCode n) a graph :=
                  mem_textbookTupleSpace_iff.mp hspace
                have hxa : x ∈ a :=
                  (ZFSet.pair_mem_prod.mp (hfunc.1 hx)).2
                exact ⟨⟨n, rfl⟩,
                  (natCode_mem_natCode_iff i n).mpr hi,
                  (natCode_mem_natCode_iff j n).mpr hj,
                  hfunc, x, hxa, hx, hx'⟩
  · rintro ⟨⟨n, rfl⟩, hleft, hright, hfunc,
      x, hxa, hx, hx'⟩
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt left n).mp hleft with
      ⟨i, hi, rfl⟩
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt right n).mp hright with
      ⟨j, hj, rfl⟩
    rw [textbookDEqCodeZF_natCode, mem_textbookDEqZF_iff]
    exact ⟨mem_textbookTupleSpace_iff.mpr hfunc,
      hi, hj, x, hx, hx'⟩

namespace Model

noncomputable section

 theorem satisfiesIn_atomicAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

 theorem satisfiesIn_atomicBiimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj,
    SatisfiesIn]
  tauto

/-! ## Restricted semantics of the bounded predicates -/

theorem satisfiesIn_dInMemberDelta_iff
    {M a arity left right graph : ZFSet.{u}}
    (hM : M.IsTransitive) (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInMemberDelta.toFO
        ![a, arity, left, right, graph] ↔
      left ∈ arity ∧ right ∈ arity ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ x ∈ a, ∃ y ∈ a,
            ZFSet.pair left x ∈ graph ∧
              ZFSet.pair right y ∈ graph ∧ x ∈ y := by
  have hs : ∀ i : Fin 5, ![a, arity, left, right, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hleft
    · exact hright
    · exact hgraph
  rw [satisfiesIn_delta0_iff hM TextbookDefFormula.dInMemberDelta
    ![a, arity, left, right, graph] hs]
  simpa only [Delta0Formula.satisfies_toFO] using
    (TextbookDefFormula.satisfies_dInMemberDelta
      a arity left right graph)

theorem satisfiesIn_dEqMemberDelta_iff
    {M a arity left right graph : ZFSet.{u}}
    (hM : M.IsTransitive) (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqMemberDelta.toFO
        ![a, arity, left, right, graph] ↔
      left ∈ arity ∧ right ∈ arity ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ x ∈ a,
            ZFSet.pair left x ∈ graph ∧
              ZFSet.pair right x ∈ graph := by
  have hs : ∀ i : Fin 5, ![a, arity, left, right, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hleft
    · exact hright
    · exact hgraph
  rw [satisfiesIn_delta0_iff hM TextbookDefFormula.dEqMemberDelta
    ![a, arity, left, right, graph] hs]
  simpa only [Delta0Formula.satisfies_toFO] using
    (TextbookDefFormula.satisfies_dEqMemberDelta
      a arity left right graph)

/-! ## Restricted semantics of the totalized member conditions -/

theorem satisfiesIn_dInOutputMemberCondition_iff
    {M a arity left right output graph : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputMemberCondition
        ![a, arity, left, right, output, graph] ↔
      graph ∈ textbookDInCodeZF a arity left right := by
  rw [TextbookDefFormula.dInOutputMemberCondition]
  simp only [SatisfiesIn]
  have hs : ∀ i : Fin 6,
      ![a, arity, left, right, output, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hleft
    · exact hright
    · exact houtput
    · exact hgraph
  rw [satisfiesIn_standardFiniteDomainAt_iff hM
    (1 : Fin 6) ![a, arity, left, right, output, graph] hs]
  rw [satisfiesIn_delta0_iff hM.1
    (TextbookDefFormula.dInMemberDeltaAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (Fin.last 5))
    ![a, arity, left, right, output, graph] hs]
  simp [Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_dInMemberDeltaAt]

theorem satisfiesIn_dEqOutputMemberCondition_iff
    {M a arity left right output graph : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputMemberCondition
        ![a, arity, left, right, output, graph] ↔
      graph ∈ textbookDEqCodeZF a arity left right := by
  rw [TextbookDefFormula.dEqOutputMemberCondition]
  simp only [SatisfiesIn]
  have hs : ∀ i : Fin 6,
      ![a, arity, left, right, output, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hleft
    · exact hright
    · exact houtput
    · exact hgraph
  rw [satisfiesIn_standardFiniteDomainAt_iff hM
    (1 : Fin 6) ![a, arity, left, right, output, graph] hs]
  rw [satisfiesIn_delta0_iff hM.1
    (TextbookDefFormula.dEqMemberDeltaAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (Fin.last 5))
    ![a, arity, left, right, output, graph] hs]
  simp [Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_dEqMemberDeltaAt]

/-! ## Closure of the standard-`Nat` atomic outputs -/

theorem textbookDInZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (n i j : Nat) : textbookDInZF a n i j ∈ M := by
  have hnM : (natCode n : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM n
  have hiM : (natCode i : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM i
  have hjM : (natCode j : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM j
  have hspaceM : textbookTupleSpace a n ∈ M :=
    textbookTupleSpace_mem_of_isTransitiveZFModel hM ha n
  let params : Tuple (ZFCarrier M) 4 :=
    ![⟨a, ha⟩, ⟨natCode n, hnM⟩,
      ⟨natCode i, hiM⟩, ⟨natCode j, hjM⟩]
  let space : ZFCarrier M := ⟨textbookTupleSpace a n, hspaceM⟩
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
    TextbookDefFormula.dInMemberDelta.toFO params space
  have hassign (graph : ZFSet.{u}) :
      snoc (zfCarrierTupleVal params) graph =
        ![a, natCode n, natCode i, natCode j, graph] := by
    funext k
    fin_cases k <;> rfl
  have hsepEq :
      (space.1.sep fun graph =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookDefFormula.dInMemberDelta.toFO
          (snoc (zfCarrierTupleVal params) graph)) =
        textbookDInZF a n i j := by
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_sep, mem_textbookDInZF_iff]
    constructor
    · rintro ⟨hgraphSpace, hformula⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspaceM
      rw [hassign graph] at hformula
      rcases (satisfiesIn_dInMemberDelta_iff hM.1 ha hnM hiM hjM
          hgraphM).mp hformula with
        ⟨hiCode, hjCode, _hfunc, x, _hxa, y, _hya, hx, hy, hxy⟩
      exact ⟨hgraphSpace,
        (natCode_mem_natCode_iff i n).mp hiCode,
        (natCode_mem_natCode_iff j n).mp hjCode,
        x, y, hx, hy, hxy⟩
    · rintro ⟨hgraphSpace, hi, hj, x, y, hx, hy, hxy⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspaceM
      have hfunc : ZFSet.IsFunc (natCode n) a graph :=
        mem_textbookTupleSpace_iff.mp hgraphSpace
      have hxa : x ∈ a :=
        (ZFSet.pair_mem_prod.mp (hfunc.1 hx)).2
      have hya : y ∈ a :=
        (ZFSet.pair_mem_prod.mp (hfunc.1 hy)).2
      refine ⟨hgraphSpace, ?_⟩
      rw [hassign graph]
      apply (satisfiesIn_dInMemberDelta_iff hM.1 ha hnM hiM hjM
        hgraphM).mpr
      exact ⟨(natCode_mem_natCode_iff i n).mpr hi,
        (natCode_mem_natCode_iff j n).mpr hj,
        hfunc, x, hxa, y, hya, hx, hy, hxy⟩
  rw [hsepEq] at hsep
  exact hsep

theorem textbookDEqZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (n i j : Nat) : textbookDEqZF a n i j ∈ M := by
  have hnM : (natCode n : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM n
  have hiM : (natCode i : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM i
  have hjM : (natCode j : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM j
  have hspaceM : textbookTupleSpace a n ∈ M :=
    textbookTupleSpace_mem_of_isTransitiveZFModel hM ha n
  let params : Tuple (ZFCarrier M) 4 :=
    ![⟨a, ha⟩, ⟨natCode n, hnM⟩,
      ⟨natCode i, hiM⟩, ⟨natCode j, hjM⟩]
  let space : ZFCarrier M := ⟨textbookTupleSpace a n, hspaceM⟩
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
    TextbookDefFormula.dEqMemberDelta.toFO params space
  have hassign (graph : ZFSet.{u}) :
      snoc (zfCarrierTupleVal params) graph =
        ![a, natCode n, natCode i, natCode j, graph] := by
    funext k
    fin_cases k <;> rfl
  have hsepEq :
      (space.1.sep fun graph =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookDefFormula.dEqMemberDelta.toFO
          (snoc (zfCarrierTupleVal params) graph)) =
        textbookDEqZF a n i j := by
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_sep, mem_textbookDEqZF_iff]
    constructor
    · rintro ⟨hgraphSpace, hformula⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspaceM
      rw [hassign graph] at hformula
      rcases (satisfiesIn_dEqMemberDelta_iff hM.1 ha hnM hiM hjM
          hgraphM).mp hformula with
        ⟨hiCode, hjCode, _hfunc, x, _hxa, hx, hx'⟩
      exact ⟨hgraphSpace,
        (natCode_mem_natCode_iff i n).mp hiCode,
        (natCode_mem_natCode_iff j n).mp hjCode,
        x, hx, hx'⟩
    · rintro ⟨hgraphSpace, hi, hj, x, hx, hx'⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspaceM
      have hfunc : ZFSet.IsFunc (natCode n) a graph :=
        mem_textbookTupleSpace_iff.mp hgraphSpace
      have hxa : x ∈ a :=
        (ZFSet.pair_mem_prod.mp (hfunc.1 hx)).2
      refine ⟨hgraphSpace, ?_⟩
      rw [hassign graph]
      apply (satisfiesIn_dEqMemberDelta_iff hM.1 ha hnM hiM hjM
        hgraphM).mpr
      exact ⟨(natCode_mem_natCode_iff i n).mpr hi,
        (natCode_mem_natCode_iff j n).mpr hj,
        hfunc, x, hxa, hx, hx'⟩
  rw [hsepEq] at hsep
  exact hsep

/-! ## Closure of the total set-coded outputs -/

theorem textbookDInCodeZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (arity left right : ZFSet.{u}) :
    textbookDInCodeZF a arity left right ∈ M := by
  unfold textbookDInCodeZF
  cases harity : textbookNatDecode arity with
  | none =>
      exact empty_mem_of_isTransitiveZFModel hM
  | some n =>
      cases hleft : textbookNatDecode left with
      | none =>
          exact empty_mem_of_isTransitiveZFModel hM
      | some i =>
          cases hright : textbookNatDecode right with
          | none =>
              exact empty_mem_of_isTransitiveZFModel hM
          | some j =>
              exact textbookDInZF_mem_of_isTransitiveZFModel
                hM ha n i j

theorem textbookDEqCodeZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (arity left right : ZFSet.{u}) :
    textbookDEqCodeZF a arity left right ∈ M := by
  unfold textbookDEqCodeZF
  cases harity : textbookNatDecode arity with
  | none =>
      exact empty_mem_of_isTransitiveZFModel hM
  | some n =>
      cases hleft : textbookNatDecode left with
      | none =>
          exact empty_mem_of_isTransitiveZFModel hM
      | some i =>
          cases hright : textbookNatDecode right with
          | none =>
              exact empty_mem_of_isTransitiveZFModel hM
          | some j =>
              exact textbookDEqZF_mem_of_isTransitiveZFModel
                hM ha n i j

/-! ## Exact restricted semantics of the output formulas -/

theorem satisfiesIn_dInOutputFormula_components
    {M a arity left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputFormula
        ![a, arity, left, right, output] ↔
      ∀ graph : ZFSet.{u}, graph ∈ M →
        (graph ∈ output ↔
          graph ∈ textbookDInCodeZF a arity left right) := by
  rw [TextbookDefFormula.dInOutputFormula,
    satisfiesIn_atomicAll_iff]
  have hassign (graph : ZFSet.{u}) :
      snoc ![a, arity, left, right, output] graph =
        ![a, arity, left, right, output, graph] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h graph hgraph
    have hbiimp := (satisfiesIn_atomicBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      TextbookDefFormula.dInOutputMemberCondition
      (snoc ![a, arity, left, right, output] graph)).mp
        (h graph hgraph)
    rw [hassign graph] at hbiimp
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputMemberCondition
        ![a, arity, left, right, output, graph] at hbiimp
    exact hbiimp.trans
      (satisfiesIn_dInOutputMemberCondition_iff hM
        ha harity hleft hright houtput hgraph)
  · intro h graph hgraph
    apply (satisfiesIn_atomicBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      TextbookDefFormula.dInOutputMemberCondition
      (snoc ![a, arity, left, right, output] graph)).mpr
    rw [hassign graph]
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputMemberCondition
        ![a, arity, left, right, output, graph]
    exact (h graph hgraph).trans
      (satisfiesIn_dInOutputMemberCondition_iff hM
        ha harity hleft hright houtput hgraph).symm

theorem satisfiesIn_dEqOutputFormula_components
    {M a arity left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputFormula
        ![a, arity, left, right, output] ↔
      ∀ graph : ZFSet.{u}, graph ∈ M →
        (graph ∈ output ↔
          graph ∈ textbookDEqCodeZF a arity left right) := by
  rw [TextbookDefFormula.dEqOutputFormula,
    satisfiesIn_atomicAll_iff]
  have hassign (graph : ZFSet.{u}) :
      snoc ![a, arity, left, right, output] graph =
        ![a, arity, left, right, output, graph] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h graph hgraph
    have hbiimp := (satisfiesIn_atomicBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      TextbookDefFormula.dEqOutputMemberCondition
      (snoc ![a, arity, left, right, output] graph)).mp
        (h graph hgraph)
    rw [hassign graph] at hbiimp
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputMemberCondition
        ![a, arity, left, right, output, graph] at hbiimp
    exact hbiimp.trans
      (satisfiesIn_dEqOutputMemberCondition_iff hM
        ha harity hleft hright houtput hgraph)
  · intro h graph hgraph
    apply (satisfiesIn_atomicBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      TextbookDefFormula.dEqOutputMemberCondition
      (snoc ![a, arity, left, right, output] graph)).mpr
    rw [hassign graph]
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputMemberCondition
        ![a, arity, left, right, output, graph]
    exact (h graph hgraph).trans
      (satisfiesIn_dEqOutputMemberCondition_iff hM
        ha harity hleft hright houtput hgraph).symm

theorem satisfiesIn_dInOutputFormula_iff
    {M a arity left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputFormula
        ![a, arity, left, right, output] ↔
      output = textbookDInCodeZF a arity left right := by
  rw [satisfiesIn_dInOutputFormula_components hM
    ha harity hleft hright houtput]
  have hcode : textbookDInCodeZF a arity left right ∈ M :=
    textbookDInCodeZF_mem_of_isTransitiveZFModel hM ha arity left right
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraph
      exact (h graph (hM.1.mem_trans hgraph houtput)).mp hgraph
    · intro hgraph
      exact (h graph (hM.1.mem_trans hgraph hcode)).mpr hgraph
  · intro h graph _hgraph
    rw [h]

theorem satisfiesIn_dEqOutputFormula_iff
    {M a arity left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputFormula
        ![a, arity, left, right, output] ↔
      output = textbookDEqCodeZF a arity left right := by
  rw [satisfiesIn_dEqOutputFormula_components hM
    ha harity hleft hright houtput]
  have hcode : textbookDEqCodeZF a arity left right ∈ M :=
    textbookDEqCodeZF_mem_of_isTransitiveZFModel hM ha arity left right
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraph
      exact (h graph (hM.1.mem_trans hgraph houtput)).mp hgraph
    · intro hgraph
      exact (h graph (hM.1.mem_trans hgraph hcode)).mpr hgraph
  · intro h graph _hgraph
    rw [h]

/-! ## Standard `FunctionAbsoluteTo` packages -/







end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookAtomicAbsolute


/- Source module: Solutions.Work_CUGCH_TextbookProjectionAbsolute -/
section GCHSource_Work_CUGCH_TextbookProjectionAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Absoluteness of the textbook existential projection

This file gives a first-order graph for the total set-coded operation
`textbookExistsProjCodeZF`.  The finite-arity and nonempty-arity conditions
are part of the member condition.  In particular, the graph defines the
empty output at arity zero, exactly as in the textbook definition.

The formula describing an extended tuple graph is genuinely bounded: it
says that the extended graph is obtained by adjoining the Kuratowski pair
`<arity, value>` to the original graph.  Closure of the projection output is
then obtained by Separation from the already internalized finite tuple
space; no ambient powerset is identified with an internal powerset.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookDefFormula

/-! ## A bounded formula for adjoining the final graph entry -/

/--
`extended` is exactly `insert (pair arity value) graph`.

The three conjuncts respectively give the upper inclusion, inclusion of the
old graph, and membership of the newly adjoined pair.  Every quantifier is
bounded by either `extended` or `graph`.
-/
def insertPairEqDeltaAt {n : Nat}
    (extended graph arity value : Fin n) : Delta0Formula n :=
  .conj
    (Delta0Formula.boundedAll extended
      (.disj
        (.mem (Fin.last n) graph.castSucc)
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last n) arity.castSucc value.castSucc)))
    (.conj
      (Delta0Formula.boundedAll graph
        (.mem (Fin.last n) extended.castSucc))
      (Delta0Formula.boundedEx extended
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last n) arity.castSucc value.castSucc)))

@[simp]
theorem satisfies_insertPairEqDeltaAt {n : Nat}
    (extended graph arity value : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (insertPairEqDeltaAt extended graph arity value) s ↔
      s extended = insert (ZFSet.pair (s arity) (s value)) (s graph) := by
  simp only [insertPairEqDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_boundedAll,
    Delta0Formula.satisfies_disj,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hupper, hlower, pairWitness, hpairMem, hpairWitness⟩
    have hnew : ZFSet.pair (s arity) (s value) ∈ s extended := by
      rwa [hpairWitness] at hpairMem
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      rcases hupper z hz with hzGraph | hzPair
      · exact Or.inr hzGraph
      · exact Or.inl hzPair
    · rintro (rfl | hzGraph)
      · exact hnew
      · exact hlower z hzGraph
  · intro hextended
    constructor
    · intro z hz
      change z ∈ s extended at hz
      rw [hextended, ZFSet.mem_insert_iff] at hz
      rcases hz with hzPair | hzGraph
      · exact Or.inr hzPair
      · exact Or.inl hzGraph
    · constructor
      · intro z hz
        change z ∈ s graph at hz
        change z ∈ s extended
        rw [hextended, ZFSet.mem_insert_iff]
        exact Or.inr hz
      · refine ⟨ZFSet.pair (s arity) (s value), ?_, rfl⟩
        change ZFSet.pair (s arity) (s value) ∈ s extended
        rw [hextended, ZFSet.mem_insert_iff]
        exact Or.inl rfl

/-- Layout `[extended, graph, arity, value]`. -/
def insertPairEqDelta : Delta0Formula 4 :=
  insertPairEqDeltaAt
    (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)

@[simp]
theorem satisfies_insertPairEqDelta
    (extended graph arity value : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem insertPairEqDelta
        ![extended, graph, arity, value] ↔
      extended = insert (ZFSet.pair arity value) graph := by
  simp [insertPairEqDelta]

/-! ## The bounded projection-member predicate -/

/--
A graph is an `arity`-tuple over `a`, `arity` is nonempty, and adjoining one
last value from `a` gives a graph in `relation`.  Standard finiteness is a
separate first-order guard below, since membership in the standard omega is
not Delta-zero without an omega parameter.
-/
def existsProjMemberDeltaAt {n : Nat}
    (a arity relation graph : Fin n) : Delta0Formula n :=
  .conj
    (Delta0Formula.boundedEx arity
      (.eq (Fin.last n) (Fin.last n)))
    (.conj
      (isFunctionDeltaAt graph arity a)
      (Delta0Formula.boundedEx a
        (Delta0Formula.boundedEx relation.castSucc
          (insertPairEqDeltaAt
            (Fin.last (n + 1))
            graph.castSucc.castSucc
            arity.castSucc.castSucc
            (Fin.last n).castSucc))))

@[simp]
theorem satisfies_existsProjMemberDeltaAt {n : Nat}
    (a arity relation graph : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (existsProjMemberDeltaAt a arity relation graph) s ↔
      (∃ index : ZFSet.{u}, index ∈ s arity) ∧
        ZFSet.IsFunc (s arity) (s a) (s graph) ∧
          ∃ value ∈ s a,
            insert (ZFSet.pair (s arity) value) (s graph) ∈ s relation := by
  simp [existsProjMemberDeltaAt]

/-- Layout `[a, arity, relation, graph]`. -/
def existsProjMemberDelta : Delta0Formula 4 :=
  existsProjMemberDeltaAt
    (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)

@[simp]
theorem satisfies_existsProjMemberDelta
    (a arity relation graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem existsProjMemberDelta
        ![a, arity, relation, graph] ↔
      (∃ index : ZFSet.{u}, index ∈ arity) ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ value ∈ a,
            insert (ZFSet.pair arity value) graph ∈ relation := by
  simp [existsProjMemberDelta]

/-! ## Guarded extensional graph of the total operation -/

/--
Layout `[a, arity, relation, output, graph]`; `output` is unused.  The first
conjunct says that `arity` is a standard finite ordinal.  Nonemptiness remains
explicit in `existsProjMemberDeltaAt`, so arity zero has no members.
-/
def existsProjOutputMemberCondition : FOFormula 5 :=
  .conj
    (Model.standardFiniteDomainAt (1 : Fin 5))
    (existsProjMemberDeltaAt
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4)).toFO

/-- Layout `[a, arity, relation, output]`. -/
def existsProjOutputFormula : FOFormula 4 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 4) (3 : Fin 4).castSucc)
      existsProjOutputMemberCondition)

end TextbookDefFormula

/-! ## Exact ambient membership of the totalized operation -/

 theorem exists_mem_natCode_iff (n : Nat) :
    (∃ index : ZFSet.{u}, index ∈ natCode n) ↔ n ≠ 0 := by
  constructor
  · intro h hn
    subst n
    rcases h with ⟨index, hindex⟩
    simp [natCode] at hindex
  · intro hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
        exact ⟨natCode n,
          (natCode_mem_natCode_iff n (n + 1)).mpr (Nat.lt_succ_self n)⟩

@[simp]
theorem mem_textbookExistsProjCodeZF_iff
    {a arity relation graph : ZFSet.{u}} :
    graph ∈ textbookExistsProjCodeZF a arity relation ↔
      (∃ n : Nat, arity = natCode n) ∧
        (∃ index : ZFSet.{u}, index ∈ arity) ∧
          ZFSet.IsFunc arity a graph ∧
            ∃ value ∈ a,
              insert (ZFSet.pair arity value) graph ∈ relation := by
  constructor
  · intro hgraph
    unfold textbookExistsProjCodeZF at hgraph
    cases harity : textbookNatDecode arity with
    | none => simp [harity] at hgraph
    | some n =>
        have harityEq : arity = natCode n :=
          textbookNatDecode_eq_some_iff.mp harity
        subst arity
        simp only [harity] at hgraph
        have hn : n ≠ 0 := by
          intro hn
          subst n
          rw [textbookExistsProjZF_zero] at hgraph
          exact ZFSet.notMem_empty graph hgraph
        rcases (mem_textbookExistsProjZF_iff hn).mp hgraph with
          ⟨hspace, value, hvalue, hextended⟩
        exact ⟨⟨n, rfl⟩, (exists_mem_natCode_iff n).2 hn,
          mem_textbookTupleSpace_iff.mp hspace,
          value, hvalue, by
            simpa only [textbookTupleSnocGraph] using hextended⟩
  · rintro ⟨⟨n, rfl⟩, hnonempty, hfunc,
      value, hvalue, hextended⟩
    have hn : n ≠ 0 := (exists_mem_natCode_iff n).1 hnonempty
    rw [textbookExistsProjCodeZF_natCode,
      mem_textbookExistsProjZF_iff hn]
    exact ⟨mem_textbookTupleSpace_iff.mpr hfunc,
      value, hvalue, by
        simpa only [textbookTupleSnocGraph] using hextended⟩

namespace Model

noncomputable section

 theorem satisfiesIn_projectionAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

 theorem satisfiesIn_projectionBiimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj,
    SatisfiesIn]
  tauto

/-! ## Restricted semantics of the bounded member predicate -/

theorem satisfiesIn_existsProjMemberDelta_iff
    {M a arity relation graph : ZFSet.{u}}
    (hM : M.IsTransitive) (ha : a ∈ M) (harity : arity ∈ M)
    (hrelation : relation ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjMemberDelta.toFO
        ![a, arity, relation, graph] ↔
      (∃ index : ZFSet.{u}, index ∈ arity) ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ value ∈ a,
            insert (ZFSet.pair arity value) graph ∈ relation := by
  have hs : ∀ i : Fin 4, ![a, arity, relation, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hrelation
    · exact hgraph
  rw [satisfiesIn_delta0_iff hM
    TextbookDefFormula.existsProjMemberDelta
    ![a, arity, relation, graph] hs]
  simpa only [Delta0Formula.satisfies_toFO] using
    (TextbookDefFormula.satisfies_existsProjMemberDelta
      a arity relation graph)

theorem satisfiesIn_existsProjOutputMemberCondition_iff
    {M a arity relation output graph : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hrelation : relation ∈ M) (houtput : output ∈ M)
    (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputMemberCondition
        ![a, arity, relation, output, graph] ↔
      graph ∈ textbookExistsProjCodeZF a arity relation := by
  rw [TextbookDefFormula.existsProjOutputMemberCondition]
  simp only [SatisfiesIn]
  have hs : ∀ i : Fin 5,
      ![a, arity, relation, output, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hrelation
    · exact houtput
    · exact hgraph
  rw [satisfiesIn_standardFiniteDomainAt_iff hM
    (1 : Fin 5) ![a, arity, relation, output, graph] hs]
  have hdelta := satisfiesIn_delta0_iff hM.1
    (TextbookDefFormula.existsProjMemberDeltaAt
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4))
    ![a, arity, relation, output, graph] hs
  rw [Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_existsProjMemberDeltaAt] at hdelta
  rw [hdelta]
  exact mem_textbookExistsProjCodeZF_iff.symm

/-! ## Closure under the standard and total projections -/

theorem textbookExistsProjZF_mem_of_isTransitiveZFModel
    {M a relation : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hrelation : relation ∈ M) (n : Nat) :
    textbookExistsProjZF a n relation ∈ M := by
  by_cases hn : n = 0
  · subst n
    simp only [textbookExistsProjZF_zero]
    exact empty_mem_of_isTransitiveZFModel hM
  · have hnM : (natCode n : ZFSet.{u}) ∈ M :=
      natOrdinal_mem_of_isTransitiveZFModel hM n
    have hspaceM : textbookTupleSpace a n ∈ M :=
      textbookTupleSpace_mem_of_isTransitiveZFModel hM ha n
    let params : Tuple (ZFCarrier M) 3 :=
      ![⟨a, ha⟩, ⟨natCode n, hnM⟩, ⟨relation, hrelation⟩]
    let space : ZFCarrier M := ⟨textbookTupleSpace a n, hspaceM⟩
    have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
      TextbookDefFormula.existsProjMemberDelta.toFO params space
    have hassign (graph : ZFSet.{u}) :
        snoc (zfCarrierTupleVal params) graph =
          ![a, natCode n, relation, graph] := by
      funext i
      fin_cases i <;> rfl
    have hsepEq :
        (space.1.sep fun graph =>
          SatisfiesIn (M : Set ZFSet.{u})
            TextbookDefFormula.existsProjMemberDelta.toFO
            (snoc (zfCarrierTupleVal params) graph)) =
          textbookExistsProjZF a n relation := by
      apply ZFSet.ext
      intro graph
      rw [ZFSet.mem_sep, mem_textbookExistsProjZF_iff hn]
      constructor
      · rintro ⟨hgraphSpace, hformula⟩
        have hgraphM : graph ∈ M :=
          hM.1.mem_trans hgraphSpace hspaceM
        rw [hassign graph] at hformula
        rcases (satisfiesIn_existsProjMemberDelta_iff
            hM.1 ha hnM hrelation hgraphM).mp hformula with
          ⟨_hnonempty, _hfunc, value, hvalue, hextendedRelation⟩
        refine ⟨hgraphSpace, value, hvalue, ?_⟩
        simpa only [textbookTupleSnocGraph] using hextendedRelation
      · rintro ⟨hgraphSpace, value, hvalue, hextendedRelation⟩
        have hgraphM : graph ∈ M :=
          hM.1.mem_trans hgraphSpace hspaceM
        have hfunc : ZFSet.IsFunc (natCode n) a graph :=
          mem_textbookTupleSpace_iff.mp hgraphSpace
        refine ⟨hgraphSpace, ?_⟩
        rw [hassign graph]
        apply (satisfiesIn_existsProjMemberDelta_iff
          hM.1 ha hnM hrelation hgraphM).mpr
        refine ⟨(exists_mem_natCode_iff n).2 hn, hfunc,
          value, hvalue, ?_⟩
        simpa only [textbookTupleSnocGraph] using hextendedRelation
    rw [hsepEq] at hsep
    exact hsep

theorem textbookExistsProjCodeZF_mem_of_isTransitiveZFModel
    {M a relation : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hrelation : relation ∈ M) (arity : ZFSet.{u}) :
    textbookExistsProjCodeZF a arity relation ∈ M := by
  unfold textbookExistsProjCodeZF
  cases harity : textbookNatDecode arity with
  | none => exact empty_mem_of_isTransitiveZFModel hM
  | some n =>
      exact textbookExistsProjZF_mem_of_isTransitiveZFModel
        hM ha hrelation n

/-! ## Exact restricted semantics of the output formula -/

theorem satisfiesIn_existsProjOutputFormula_components
    {M a arity relation output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hrelation : relation ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputFormula
        ![a, arity, relation, output] ↔
      ∀ graph : ZFSet.{u}, graph ∈ M →
        (graph ∈ output ↔
          graph ∈ textbookExistsProjCodeZF a arity relation) := by
  rw [TextbookDefFormula.existsProjOutputFormula,
    satisfiesIn_projectionAll_iff]
  have hassign (graph : ZFSet.{u}) :
      snoc ![a, arity, relation, output] graph =
        ![a, arity, relation, output, graph] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h graph hgraph
    have hbiimp := (satisfiesIn_projectionBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 4) (3 : Fin 4).castSucc)
      TextbookDefFormula.existsProjOutputMemberCondition
      (snoc ![a, arity, relation, output] graph)).mp
        (h graph hgraph)
    rw [hassign graph] at hbiimp
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputMemberCondition
        ![a, arity, relation, output, graph] at hbiimp
    exact hbiimp.trans
      (satisfiesIn_existsProjOutputMemberCondition_iff hM
        ha harity hrelation houtput hgraph)
  · intro h graph hgraph
    apply (satisfiesIn_projectionBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 4) (3 : Fin 4).castSucc)
      TextbookDefFormula.existsProjOutputMemberCondition
      (snoc ![a, arity, relation, output] graph)).mpr
    rw [hassign graph]
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputMemberCondition
        ![a, arity, relation, output, graph]
    exact (h graph hgraph).trans
      (satisfiesIn_existsProjOutputMemberCondition_iff hM
        ha harity hrelation houtput hgraph).symm

theorem satisfiesIn_existsProjOutputFormula_iff
    {M a arity relation output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hrelation : relation ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputFormula
        ![a, arity, relation, output] ↔
      output = textbookExistsProjCodeZF a arity relation := by
  rw [satisfiesIn_existsProjOutputFormula_components hM
    ha harity hrelation houtput]
  have hcode : textbookExistsProjCodeZF a arity relation ∈ M :=
    textbookExistsProjCodeZF_mem_of_isTransitiveZFModel
      hM ha hrelation arity
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraph
      exact (h graph (hM.1.mem_trans hgraph houtput)).mp hgraph
    · intro hgraph
      exact (h graph (hM.1.mem_trans hgraph hcode)).mpr hgraph
  · intro h graph _hgraph
    rw [h]

/-! ## Standard `FunctionAbsoluteTo` package -/



end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookProjectionAbsolute


/- Source module: Solutions.Work_CUGCH_TextbookBooleanAbsolute -/
section GCHSource_Work_CUGCH_TextbookBooleanAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Absoluteness of the textbook Boolean set operations

The complementation and intersection clauses in the textbook recursion for
`E(a,n,m)` are operations on actual sets.  This file packages those operations
as total `ZFSet`-valued functions and proves that their extensional graph
formulas are absolute to every transitive set model of ZF.

The complement is relative to the tuple space supplied as its first input:
`relativeDifferenceZF space r = space \ r`.  Both closure proofs use the
model's own Separation axiom.  The ambient `ZFSet.sep` appearing in the proof
is only the extensional description of that internal Separation witness.
-/

section

open Set

universe u

namespace Constructible

/-! ## Actual set-valued operations -/

/-- Relative complement in a specified ambient set. -/
def relativeDifferenceZF (space r : ZFSet.{u}) : ZFSet.{u} :=
  space \ r

/-- Binary intersection as an actual `ZFSet`. -/
def intersectionZF (r t : ZFSet.{u}) : ZFSet.{u} :=
  r ∩ t

@[simp]
theorem mem_relativeDifferenceZF_iff
    {space r x : ZFSet.{u}} :
    x ∈ relativeDifferenceZF space r ↔ x ∈ space ∧ x ∉ r := by
  simp [relativeDifferenceZF]

@[simp]
theorem mem_intersectionZF_iff {r t x : ZFSet.{u}} :
    x ∈ intersectionZF r t ↔ x ∈ r ∧ x ∈ t := by
  simp [intersectionZF]

namespace TextbookDefFormula

/-! ## Pure membership-language graph formulas -/

/-- A candidate belongs to the relative complement of `removed` in `space`. -/
def relativeDifferenceMemberAt {n : Nat}
    (space removed candidate : Fin n) : FOFormula n :=
  .conj (.mem candidate space) (.neg (.mem candidate removed))

/-- A candidate belongs to the intersection of `left` and `right`. -/
def intersectionMemberAt {n : Nat}
    (left right candidate : Fin n) : FOFormula n :=
  .conj (.mem candidate left) (.mem candidate right)

@[simp]
theorem satisfies_relativeDifferenceMemberAt {A : Type u}
    (E : A → A → Prop) {n : Nat}
    (space removed candidate : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E
        (relativeDifferenceMemberAt space removed candidate) s ↔
      E (s candidate) (s space) ∧ ¬E (s candidate) (s removed) := by
  simp [relativeDifferenceMemberAt]

@[simp]
theorem satisfies_intersectionMemberAt {A : Type u}
    (E : A → A → Prop) {n : Nat}
    (left right candidate : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E
        (intersectionMemberAt left right candidate) s ↔
      E (s candidate) (s left) ∧ E (s candidate) (s right) := by
  simp [intersectionMemberAt]

/--
Layout `[space, removed, output]`.  The bound variable is a candidate member.
-/
def relativeDifferenceOutputFormula : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (relativeDifferenceMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3)))

/-- Layout `[left, right, output]`. -/
def intersectionOutputFormula : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (intersectionMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3)))

/-! ## Exact ambient semantics -/

@[simp]
theorem satisfies_relativeDifferenceOutputFormula
    (space removed output : ZFSet.{u}) :
    FOFormula.Satisfies (· ∈ ·) relativeDifferenceOutputFormula
        ![space, removed, output] ↔
      output = relativeDifferenceZF space removed := by
  rw [relativeDifferenceOutputFormula, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_relativeDifferenceMemberAt]
  change
    (∀ x : ZFSet.{u}, x ∈ output ↔ x ∈ space ∧ x ∉ removed) ↔
      output = relativeDifferenceZF space removed
  rw [ZFSet.ext_iff]
  simp only [mem_relativeDifferenceZF_iff]

@[simp]
theorem satisfies_intersectionOutputFormula
    (left right output : ZFSet.{u}) :
    FOFormula.Satisfies (· ∈ ·) intersectionOutputFormula
        ![left, right, output] ↔
      output = intersectionZF left right := by
  rw [intersectionOutputFormula, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_intersectionMemberAt]
  change
    (∀ x : ZFSet.{u}, x ∈ output ↔ x ∈ left ∧ x ∈ right) ↔
      output = intersectionZF left right
  rw [ZFSet.ext_iff]
  simp only [mem_intersectionZF_iff]

end TextbookDefFormula

namespace Model

noncomputable section

 theorem satisfiesIn_booleanAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

 theorem satisfiesIn_booleanBiimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj,
    SatisfiesIn]
  tauto

/-! ## Closure obtained from the model's Separation axiom -/

theorem relativeDifferenceZF_mem_of_isTransitiveZFModel
    {M space removed : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hspace : space ∈ M) (hremoved : removed ∈ M) :
    relativeDifferenceZF space removed ∈ M := by
  let params : Tuple (ZFCarrier M) 2 :=
    ![⟨space, hspace⟩, ⟨removed, hremoved⟩]
  let base : ZFCarrier M := ⟨space, hspace⟩
  let memberFormula : FOFormula 3 :=
    TextbookDefFormula.relativeDifferenceMemberAt
      (0 : Fin 3) (1 : Fin 3) (Fin.last 2)
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel
    hM memberFormula params base
  have hassign (x : ZFSet.{u}) :
      snoc (zfCarrierTupleVal params) x = ![space, removed, x] := by
    funext i
    fin_cases i <;> rfl
  have hsepEq :
      (base.1.sep fun x =>
        SatisfiesIn (M : Set ZFSet.{u}) memberFormula
          (snoc (zfCarrierTupleVal params) x)) =
        relativeDifferenceZF space removed := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_relativeDifferenceZF_iff, hassign]
    simp [base, memberFormula,
      TextbookDefFormula.relativeDifferenceMemberAt, SatisfiesIn]
  rw [hsepEq] at hsep
  exact hsep

theorem intersectionZF_mem_of_isTransitiveZFModel
    {M left right : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hleft : left ∈ M) (hright : right ∈ M) :
    intersectionZF left right ∈ M := by
  let params : Tuple (ZFCarrier M) 2 :=
    ![⟨left, hleft⟩, ⟨right, hright⟩]
  let base : ZFCarrier M := ⟨left, hleft⟩
  let memberFormula : FOFormula 3 :=
    TextbookDefFormula.intersectionMemberAt
      (0 : Fin 3) (1 : Fin 3) (Fin.last 2)
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel
    hM memberFormula params base
  have hassign (x : ZFSet.{u}) :
      snoc (zfCarrierTupleVal params) x = ![left, right, x] := by
    funext i
    fin_cases i <;> rfl
  have hsepEq :
      (base.1.sep fun x =>
        SatisfiesIn (M : Set ZFSet.{u}) memberFormula
          (snoc (zfCarrierTupleVal params) x)) =
        intersectionZF left right := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_intersectionZF_iff, hassign]
    simp [base, memberFormula,
      TextbookDefFormula.intersectionMemberAt, SatisfiesIn]
  rw [hsepEq] at hsep
  exact hsep

/-! ## Exact restricted semantics -/

theorem satisfiesIn_relativeDifferenceOutputFormula_components
    {M space removed output : ZFSet.{u}} :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.relativeDifferenceOutputFormula
        ![space, removed, output] ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        (x ∈ output ↔ x ∈ relativeDifferenceZF space removed) := by
  rw [TextbookDefFormula.relativeDifferenceOutputFormula,
    satisfiesIn_booleanAll_iff]
  have hassign (x : ZFSet.{u}) :
      snoc ![space, removed, output] x = ![space, removed, output, x] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h x hx
    have hbiimp := (satisfiesIn_booleanBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (TextbookDefFormula.relativeDifferenceMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3))
      (snoc ![space, removed, output] x)).mp (h x hx)
    rw [hassign x] at hbiimp
    simpa [SatisfiesIn,
      TextbookDefFormula.relativeDifferenceMemberAt] using hbiimp
  · intro h x hx
    apply (satisfiesIn_booleanBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (TextbookDefFormula.relativeDifferenceMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3))
      (snoc ![space, removed, output] x)).mpr
    rw [hassign x]
    simpa [SatisfiesIn,
      TextbookDefFormula.relativeDifferenceMemberAt] using h x hx

theorem satisfiesIn_intersectionOutputFormula_components
    {M left right output : ZFSet.{u}} :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.intersectionOutputFormula
        ![left, right, output] ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        (x ∈ output ↔ x ∈ intersectionZF left right) := by
  rw [TextbookDefFormula.intersectionOutputFormula,
    satisfiesIn_booleanAll_iff]
  have hassign (x : ZFSet.{u}) :
      snoc ![left, right, output] x = ![left, right, output, x] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h x hx
    have hbiimp := (satisfiesIn_booleanBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (TextbookDefFormula.intersectionMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3))
      (snoc ![left, right, output] x)).mp (h x hx)
    rw [hassign x] at hbiimp
    simpa [SatisfiesIn,
      TextbookDefFormula.intersectionMemberAt] using hbiimp
  · intro h x hx
    apply (satisfiesIn_booleanBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (TextbookDefFormula.intersectionMemberAt
        (0 : Fin 4) (1 : Fin 4) (Fin.last 3))
      (snoc ![left, right, output] x)).mpr
    rw [hassign x]
    simpa [SatisfiesIn,
      TextbookDefFormula.intersectionMemberAt] using h x hx

theorem satisfiesIn_relativeDifferenceOutputFormula_iff
    {M space removed output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hspace : space ∈ M) (hremoved : removed ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.relativeDifferenceOutputFormula
        ![space, removed, output] ↔
      output = relativeDifferenceZF space removed := by
  rw [satisfiesIn_relativeDifferenceOutputFormula_components]
  have hresult : relativeDifferenceZF space removed ∈ M :=
    relativeDifferenceZF_mem_of_isTransitiveZFModel
      hM hspace hremoved
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      exact (h x (hM.1.mem_trans hx houtput)).mp hx
    · intro hx
      exact (h x (hM.1.mem_trans hx hresult)).mpr hx
  · intro h x _hx
    rw [h]

theorem satisfiesIn_intersectionOutputFormula_iff
    {M left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.intersectionOutputFormula
        ![left, right, output] ↔
      output = intersectionZF left right := by
  rw [satisfiesIn_intersectionOutputFormula_components]
  have hresult : intersectionZF left right ∈ M :=
    intersectionZF_mem_of_isTransitiveZFModel hM hleft hright
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      exact (h x (hM.1.mem_trans hx houtput)).mp hx
    · intro hx
      exact (h x (hM.1.mem_trans hx hresult)).mpr hx
  · intro h x _hx
    rw [h]

/-! ## Standard `FunctionAbsoluteTo` packages -/





end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookBooleanAbsolute


