-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library03
-- name    : CH_ConstructibleGCH_Library03
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:08:26.908991+00:00
-- url     : https://prove2.me/theorems/d181a727-6cbc-47b9-8c29-1983745c9a38
-- title:
--   Bounded histories and elementary hull data
-- statement:
--   This library provides the interfaces for bounds on stage histories and correctness of the fixed rudimentary evaluators, together with finite-fragment elementarity, Skolem hulls and Mostowski collapse. These data let later theorems compare a hull with its transitive collapse.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/BareStageHistoryBounds.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/BareGodelDefAbsolute.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalBareHistory.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationReflection.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FiniteFragmentElementarity.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FiniteFragmentSkolemHull.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/MostowskiCollapse.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library02
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_BareStageHistoryBounds -/
section GCHSource_Work_CUGCH_BareStageHistoryBounds
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Local bounds for bounded constructible-stage histories

This file records the elementary closure facts needed before constructing a
stage-only ("bare") history inside a prescribed limit level.  The hypotheses
and conclusions are deliberately local: membership in the proper class `L`
is not used as a substitute for membership in `LStageZF theta`.

The results below do not yet internalize the Replacement family occurring at
a limit step.  In particular, they do not claim that `stageHistoryData alpha`
belongs to every later limit level.
-/

section

universe u v

namespace Constructible

section ZFC

open Set

/-! ## Explicit finite successor bounds -/













/-! ## Local closure under the rudimentary basis -/





/-- A nonzero limit level is closed under unordered pairing. -/
theorem pair_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF theta)
    (hy : y ∈ LStageZF theta) :
    ({x, y} : ZFSet.{u}) ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxAlpha⟩
  rcases (mem_LStageZF_limit_iff htheta).mp hy with
    ⟨beta, hbeta, hyBeta⟩
  let gamma := max alpha beta
  apply (mem_LStageZF_limit_iff htheta).mpr
  refine ⟨Order.succ gamma, htheta.succ_lt (max_lt halpha hbeta), ?_⟩
  rw [LStageZF_succ]
  exact pair_mem_DefZF
    (LStageZF_mono (le_max_left alpha beta) hxAlpha)
    (LStageZF_mono (le_max_right alpha beta) hyBeta)

/-- A nonzero limit level is closed under singleton formation. -/
theorem singleton_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x : ZFSet.{u}} (hx : x ∈ LStageZF theta) :
    ({x} : ZFSet.{u}) ∈ LStageZF theta := by
  simpa using pair_mem_LStageZF_of_isSuccLimit htheta hx hx

/-- A nonzero limit level is closed under set union. -/
theorem sUnion_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x : ZFSet.{u}} (hx : x ∈ LStageZF theta) :
    ZFSet.sUnion x ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxAlpha⟩
  apply (mem_LStageZF_limit_iff htheta).mpr
  refine ⟨Order.succ alpha, htheta.succ_lt halpha, ?_⟩
  rw [LStageZF_succ]
  exact sUnion_mem_DefZF (LStageZF_isTransitive alpha) hxAlpha

/-- A nonzero limit level is closed under binary union. -/
theorem union_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF theta)
    (hy : y ∈ LStageZF theta) :
    x ∪ y ∈ LStageZF theta := by
  rw [← ZFSet.sUnion_pair]
  exact sUnion_mem_LStageZF_of_isSuccLimit htheta
    (pair_mem_LStageZF_of_isSuccLimit htheta hx hy)

/-- A nonzero limit level is closed under Kuratowski ordered pairing. -/
theorem orderedPair_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF theta)
    (hy : y ∈ LStageZF theta) :
    ZFSet.pair x y ∈ LStageZF theta := by
  change ({{x}, {x, y}} : ZFSet.{u}) ∈ LStageZF theta
  exact pair_mem_LStageZF_of_isSuccLimit htheta
    (singleton_mem_LStageZF_of_isSuccLimit htheta hx)
    (pair_mem_LStageZF_of_isSuccLimit htheta hx hy)

/-- A nonzero limit level is closed under the right-associated triple code. -/
theorem triple_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x y z : ZFSet.{u}} (hx : x ∈ LStageZF theta)
    (hy : y ∈ LStageZF theta) (hz : z ∈ LStageZF theta) :
    Godel.triple x y z ∈ LStageZF theta := by
  change ZFSet.pair x (ZFSet.pair y z) ∈ LStageZF theta
  exact orderedPair_mem_LStageZF_of_isSuccLimit htheta hx
    (orderedPair_mem_LStageZF_of_isSuccLimit htheta hy hz)

/-- Every earlier ordinal code belongs to a strictly later constructible
level.  No limit hypothesis is needed. -/
theorem ordinal_toZFSet_mem_LStageZF_of_lt
    {alpha theta : Ordinal.{u}} (halpha : alpha < theta) :
    alpha.toZFSet ∈ LStageZF theta := by
  exact LStageZF_mono (Order.succ_le_of_lt halpha)
    (ordinal_toZFSet_mem_LStage_succ alpha)







/-! ## Local bounds for finite sequence and program codes -/

/-- Every finite ordinal code belongs to every nonzero limit level. -/
theorem FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (n : Nat) :
    (FiniteSequenceZF.natCode n : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [FiniteSequenceZF.natCode] using
    ordinal_toZFSet_mem_LStageZF_of_lt
      (Ordinal.natCast_lt_of_isSuccLimit htheta n)

/-- The empty set belongs to every nonzero limit level. -/
theorem empty_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta) :
    (∅ : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [FiniteSequenceZF.natCode, Nat.cast_zero,
    Ordinal.toZFSet_zero] using
    FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit htheta 0

/-- A structural finite-list code stays in a nonzero limit level when all
of its entries lie there. -/
theorem FiniteSequenceZF.listCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ LStageZF theta) :
    FiniteSequenceZF.listCode xs ∈ LStageZF theta := by
  induction xs with
  | nil =>
      simpa only [FiniteSequenceZF.listCode_nil] using
        empty_mem_LStageZF_of_isSuccLimit htheta
  | cons x xs ih =>
      rw [FiniteSequenceZF.listCode_cons]
      apply orderedPair_mem_LStageZF_of_isSuccLimit htheta
      · exact hxs x (by simp)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])



/-- The finite indexed graph of a list stays in a nonzero limit level when
all list entries lie there. -/
theorem IndexedSequenceZF.graphFrom_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ LStageZF theta) (start : Nat) :
    IndexedSequenceZF.graphFrom start xs ∈ LStageZF theta := by
  induction xs generalizing start with
  | nil =>
      simpa only [IndexedSequenceZF.graphFrom_nil] using
        empty_mem_LStageZF_of_isSuccLimit htheta
  | cons x xs ih =>
      rw [IndexedSequenceZF.graphFrom_cons, ZFSet.insert_eq]
      apply union_mem_LStageZF_of_isSuccLimit htheta
      · apply singleton_mem_LStageZF_of_isSuccLimit htheta
        exact orderedPair_mem_LStageZF_of_isSuccLimit htheta
          (hxs x (by simp))
          (FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit
            htheta start)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])

/-- A length-tagged indexed sequence code stays in a nonzero limit level
when all of its entries lie there. -/
theorem IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ LStageZF theta) :
    IndexedSequenceZF.sequenceCode xs ∈ LStageZF theta := by
  exact orderedPair_mem_LStageZF_of_isSuccLimit htheta
    (FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit htheta xs.length)
    (IndexedSequenceZF.graphFrom_mem_LStageZF_of_isSuccLimit
      htheta hxs 0)

namespace Godel.RudimentaryTerm

/-- The variable-token tag is available in every nonzero limit level. -/
theorem varTag_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta) :
    (varTag : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [varTag, Nat.cast_zero] using
    ordinal_toZFSet_mem_LStageZF_of_lt
      (Ordinal.natCast_lt_of_isSuccLimit htheta 0)

/-- The application-token tag is available in every nonzero limit level. -/
theorem appTag_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta) :
    (appTag : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [appTag, Nat.cast_one] using
    ordinal_toZFSet_mem_LStageZF_of_lt
      (Ordinal.natCast_lt_of_isSuccLimit htheta 1)

/-- Every one of the nine finite operation tags is available in every
nonzero limit level. -/
theorem operationCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (i : Fin 9) :
    (operationCode i : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [operationCode] using
    ordinal_toZFSet_mem_LStageZF_of_lt
      (Ordinal.natCast_lt_of_isSuccLimit htheta i.1)

/-- The natural interpretation of a rudimentary generator stays in a
transitive limit level containing its seed `U`. -/
theorem rudimentaryGenerator_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (_htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (generator : Option (Constructible.ZFCarrier U)) :
    rudimentaryGenerator U generator ∈ LStageZF theta := by
  cases generator with
  | none => exact hU
  | some x =>
      exact (LStageZF_isTransitive theta).mem_trans x.2 hU

/-- The genuine set code of one stack token stays in a nonzero limit level
containing its seed. -/
theorem stackTokenZFCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (token : StackToken (Option (Constructible.ZFCarrier U))) :
    stackTokenZFCode U token ∈ LStageZF theta := by
  cases token with
  | inl generator =>
      exact triple_mem_LStageZF_of_isSuccLimit htheta
        (varTag_mem_LStageZF_of_isSuccLimit htheta)
        (rudimentaryGenerator_mem_LStageZF_of_isSuccLimit
          htheta hU generator)
        (empty_mem_LStageZF_of_isSuccLimit htheta)
  | inr operation =>
      exact triple_mem_LStageZF_of_isSuccLimit htheta
        (appTag_mem_LStageZF_of_isSuccLimit htheta)
        (operationCode_mem_LStageZF_of_isSuccLimit htheta operation)
        (empty_mem_LStageZF_of_isSuccLimit htheta)

/-- The indexed code of a finite postfix program stays in a nonzero limit
level containing its seed. -/
theorem stackProgramZFCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (program : List (StackToken
      (Option (Constructible.ZFCarrier U)))) :
    stackProgramZFCode U program ∈ LStageZF theta := by
  apply IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit htheta
  intro encodedToken hEncodedToken
  rcases List.mem_map.mp hEncodedToken with ⟨token, _htoken, rfl⟩
  exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit htheta hU token

/-! ## Local bounds for successful stack executions -/









end Godel.RudimentaryTerm

namespace Model











end Model

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_BareStageHistoryBounds


/- Source module: Solutions.Work_CUGCH_BareGodelDefAbsolute -/
section GCHSource_Work_CUGCH_BareGodelDefAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Local correctness of the Goedel-definability evaluator

This file proves that the first-order formula used at a successor step of a
bare stage history has its intended ambient meaning when interpreted in a
constructible limit level above `omega`.

The proof deliberately separates soundness from completeness.  Soundness
only projects a restricted finite evaluation certificate to the ambient
universe.  Completeness constructs the canonical program and execution-trace
codes and checks, using the local bounds from `BareStageHistoryBounds`, that
every unbounded witness belongs to the prescribed level.
-/

section

open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF
open Constructible.FiniteSequenceZF

 abbrev Carrier (a : ZFSet.{u}) := Constructible.ZFCarrier a



@[simp]
 theorem carrierVal_snoc_apply {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) (x : Carrier a) (i : Fin (n + 1)) :
    (snoc s x i).1 = snoc (fun j => (s j).1) x.1 i := by
  exact congrFun (Delta0Formula.val_snoc s x) i







 theorem satisfies_kuratowskiPairEqAt_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive) {n : Nat}
    (pair left right : Fin n) (s : Tuple (Carrier a) n) :
    FOFormula.Satisfies (zfCarrierMem a)
        (Delta0Formula.kuratowskiPairEqAt pair left right).toFO s ↔
      (s pair).1 = ZFSet.pair (s left).1 (s right).1 := by
  rw [Delta0Formula.satisfies_toFO_absolute ha,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  simp only [Delta0Formula.val_apply]

@[simp]
 theorem satisfies_functionGraphValueAt_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive) {n : Nat}
    (graph value index : Fin n) (s : Tuple (Carrier a) n) :
    FOFormula.Satisfies (zfCarrierMem a)
        (functionGraphValueAt graph value index) s ↔
      ZFSet.pair (s value).1 (s index).1 ∈ (s graph).1 := by
  rw [functionGraphValueAt,
    Delta0Formula.satisfies_toFO_absolute ha,
    Delta0Formula.satisfies_toFO]
  simp only [Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    have hpair : ZFSet.pair (s value).1 (s index).1 ∈ a :=
      ha.mem_trans hq (s graph).2
    let q : Carrier a :=
      ⟨ZFSet.pair (s value).1 (s index).1, hpair⟩
    exact ⟨q, hq, rfl⟩

@[simp]
 theorem satisfies_uniqueValueAtBody_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence length graph index value : Carrier a) :
    FOFormula.Satisfies (zfCarrierMem a) uniqueValueAtBody
        ![omega, sequence, length, graph, index, value] ↔
      ZFSet.pair value.1 index.1 ∈ graph.1 ∧
        ∀ other : Carrier a,
          ZFSet.pair other.1 index.1 ∈ graph.1 → other.1 = value.1 := by
  simp only [uniqueValueAtBody, FOFormula.Satisfies,
    FOFormula.satisfies_all, satisfies_formulaImp,
    satisfies_functionGraphValueAt_carrier ha,
    Subtype.ext_iff, Model.snoc_eq_finSnoc]
  change
    (ZFSet.pair value.1 index.1 ∈ graph.1 ∧
      ∀ other : Carrier a,
        ZFSet.pair other.1 index.1 ∈ graph.1 → other.1 = value.1) ↔ _
  rfl

@[simp]
 theorem satisfies_totalFunctionalBody_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence length graph index : Carrier a) :
    FOFormula.Satisfies (zfCarrierMem a) totalFunctionalBody
        ![omega, sequence, length, graph, index] ↔
      (index.1 ∈ length.1 →
        ∃ value : Carrier a,
          ZFSet.pair value.1 index.1 ∈ graph.1 ∧
            ∀ other : Carrier a,
              ZFSet.pair other.1 index.1 ∈ graph.1 →
                other.1 = value.1) := by
  simp only [totalFunctionalBody, satisfies_formulaImp,
    FOFormula.Satisfies, Model.snoc_eq_finSnoc, zfCarrierMem]
  change
    (index.1 ∈ length.1 →
      ∃ value : Carrier a,
        FOFormula.Satisfies (zfCarrierMem a) uniqueValueAtBody
          ![omega, sequence, length, graph, index, value]) ↔ _
  apply imp_congr_right
  intro _hindex
  apply exists_congr
  intro value
  exact satisfies_uniqueValueAtBody_carrier ha
    omega sequence length graph index value

@[simp]
 theorem satisfies_sequenceValidityFormula_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence : Carrier a) :
    FOFormula.Satisfies (zfCarrierMem a) sequenceValidityFormula
        ![omega, sequence] ↔
      ∃ length graph : Carrier a,
        sequence.1 = ZFSet.pair length.1 graph.1 ∧
          length.1 ∈ omega.1 ∧
          ∀ index : Carrier a, index.1 ∈ length.1 →
            ∃ value : Carrier a,
              ZFSet.pair value.1 index.1 ∈ graph.1 ∧
                ∀ other : Carrier a,
                  ZFSet.pair other.1 index.1 ∈ graph.1 →
                    other.1 = value.1 := by
  simp only [sequenceValidityFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all]
  constructor
  · rintro ⟨length, graph, hpair, hlength, htotal⟩
    refine ⟨length, graph, ?_, hlength, ?_⟩
    · exact (satisfies_kuratowskiPairEqAt_carrier ha
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) _).mp hpair
    · intro index hindex
      have hbody := htotal index
      exact ((satisfies_totalFunctionalBody_carrier ha
        omega sequence length graph index).mp (by
          change FOFormula.Satisfies (zfCarrierMem a)
            totalFunctionalBody
            ![omega, sequence, length, graph, index] at hbody
          exact hbody)) hindex
  · rintro ⟨length, graph, hpair, hlength, htotal⟩
    refine ⟨length, graph, ?_, hlength, ?_⟩
    · exact (satisfies_kuratowskiPairEqAt_carrier ha
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) _).mpr hpair
    · intro index
      have hbody := (satisfies_totalFunctionalBody_carrier ha
        omega sequence length graph index).mpr (htotal index)
      change FOFormula.Satisfies (zfCarrierMem a)
        totalFunctionalBody ![omega, sequence, length, graph, index]
      exact hbody



















/-! ## Canonical witnesses inside a limit stage -/

/-- The intended one-step assignment, with every coordinate packaged in the
prescribed constructible limit level. -/
 def stackStepStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    Tuple (Carrier A) 16 :=
  ![⟨U, hsub hU⟩,
    ⟨varTag, hsub (varTag_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨appTag, hsub (appTag_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨operationCode 0, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 0)⟩,
    ⟨operationCode 1, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 1)⟩,
    ⟨operationCode 2, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 2)⟩,
    ⟨operationCode 3, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 3)⟩,
    ⟨operationCode 4, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 4)⟩,
    ⟨operationCode 5, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 5)⟩,
    ⟨operationCode 6, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 6)⟩,
    ⟨operationCode 7, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 7)⟩,
    ⟨operationCode 8, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 8)⟩,
    ⟨stackTokenZFCode U token,
      hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩,
    ⟨listCode input,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩,
    ⟨listCode output,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩]

 theorem stackStepStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    (fun i => (stackStepStageAssignment hdelta hsub U hU token input output
      hinput houtput i).1) =
      stackStepAssignment U (stackTokenZFCode U token)
        (listCode input) (listCode output) := by
  funext i
  fin_cases i <;> rfl

@[simp]
 theorem stackStepStageAssignment_val_apply
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) (i : Fin 16) :
    (stackStepStageAssignment hdelta hsub U hU token input output
      hinput houtput i).1 =
      stackStepAssignment U (stackTokenZFCode U token)
        (listCode input) (listCode output) i := by
  exact congrFun (stackStepStageAssignment_val hdelta hsub U hU token
    input output hinput houtput) i

















 theorem encodedStackStates_entries_mem_LStageZF
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {states : List (List ZFSet.{u})}
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF theta) :
    ∀ code ∈ encodedStackStates states, code ∈ LStageZF theta := by
  intro code hcode
  rcases List.mem_map.mp hcode with ⟨stack, hstack, rfl⟩
  exact listCode_mem_LStageZF_of_isSuccLimit htheta
    (hstates stack hstack)

 def stackStepPrefixStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta) :
    Tuple (Carrier A) 13 :=
  ![⟨U, hsub hU⟩,
    ⟨varTag, hsub (varTag_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨appTag, hsub (appTag_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨operationCode 0, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 0)⟩,
    ⟨operationCode 1, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 1)⟩,
    ⟨operationCode 2, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 2)⟩,
    ⟨operationCode 3, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 3)⟩,
    ⟨operationCode 4, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 4)⟩,
    ⟨operationCode 5, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 5)⟩,
    ⟨operationCode 6, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 6)⟩,
    ⟨operationCode 7, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 7)⟩,
    ⟨operationCode 8, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 8)⟩]



 def traceStepExecutionStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat) :
    Tuple (Carrier A) 16 :=
  snoc (snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
    ⟨stackProgramZFCode U program,
      hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit hdelta hU program)⟩)
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩)
    ⟨natCode k, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩













 def stackProgramEvalCoreExecutionStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    Tuple (Carrier A) 20 :=
  snoc (snoc (snoc (snoc
    (snoc (snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
      ⟨Ordinal.omega0.toZFSet, homegaA⟩)
      ⟨stackProgramZFCode U program,
        hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
          hdelta hU program)⟩) ⟨result, hsub hresult⟩)
      ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
        hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩)
      ⟨natCode program.length,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩)
      ⟨natCode states.length,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩)
      ⟨listCode [result],
        hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta (by
          intro x hx
          simp only [List.mem_singleton] at hx
          subst x
          exact hresult))⟩



@[simp]
 theorem stackProgramEvalCoreExecutionStageAssignment_trace
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (16 : Fin 20) =
      ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
        hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩ := by
  rfl

@[simp]
 theorem stackProgramEvalCoreExecutionStageAssignment_programLength
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (17 : Fin 20) =
      ⟨natCode program.length,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩ := by
  rfl

@[simp]
 theorem stackProgramEvalCoreExecutionStageAssignment_finalStack
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (19 : Fin 20)).1 =
      listCode [result] := by
  rfl

@[simp]
 theorem stackProgramEvalCoreExecutionStageAssignment_result
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (15 : Fin 20)).1 = result := by
  rfl

@[simp]
 theorem stackProgramEvalCoreExecutionStageAssignment_traceLength
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (18 : Fin 20) =
      ⟨natCode states.length,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩ := by
  rfl

@[simp]
 theorem stackProgramEvalCoreExecutionStageAssignment_empty
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (3 : Fin 20) =
      (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
        Carrier A) := by
  apply Subtype.ext
  rw [show (3 : Fin 20) =
      (3 : Fin 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
    by rfl]
  simp only [stackProgramEvalCoreExecutionStageAssignment,
    snoc_castSucc]
  rfl























 def stackProgramEvalStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresultA : result ∈ A) :
    Tuple (Carrier A) 16 :=
  snoc (snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
    ⟨Ordinal.omega0.toZFSet, homegaA⟩)
    ⟨stackProgramZFCode U program,
      hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit hdelta hU program)⟩)
    ⟨result, hresultA⟩











/-! ## The output formula over a limit stage -/

 def godelDefOutputStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    Tuple (Carrier A) 15 :=
  snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
    ⟨Ordinal.omega0.toZFSet, homegaA⟩)
    ⟨nextU, hnextU⟩



 def stackProgramEvalCodeStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U code result : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hcode : code ∈ A)
    (hresult : result ∈ A) :
    Tuple (Carrier A) 16 :=
  snoc (snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
    ⟨Ordinal.omega0.toZFSet, homegaA⟩)
    ⟨code, hcode⟩) ⟨result, hresult⟩



















end
end «RudimentaryTerm»
end «Godel»
end «Constructible»
end
end GCHSource_Work_CUGCH_BareGodelDefAbsolute


/- Source module: Solutions.Work_CUGCH_CanonicalBareHistory -/
section GCHSource_Work_CUGCH_CanonicalBareHistory
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The canonical relation-free constructible-stage history

This file fixes the actual set which later local-absoluteness arguments must
put inside a prescribed constructible level.  For an ordinal `alpha`,
`canonicalBareHistory alpha` is exactly

`{ <beta, L_beta> | beta <= alpha }`.

The definition uses ambient ZF Replacement only to obtain a genuine `ZFSet`.
No constructibility bound is claimed here.  In particular, membership in the
proper class `L` would not by itself imply the local bound required by
Condensation; that bound is a separate theorem.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-- The canonical Kuratowski pair at one constructible stage. -/
def canonicalBareHistoryPair (ordinal : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.pair ordinal.toZFSet (LStageZF ordinal)

/-- The graph of all canonical stage pairs at indices strictly below
`bound`. -/
def canonicalBareHistoryBelow (bound : Ordinal.{u}) : ZFSet.{u} :=
  replacementRangeZF bound fun ordinal _hordinal =>
    canonicalBareHistoryPair ordinal

/-- The graph of all canonical stage pairs through `bound`, including its
top pair. -/
def canonicalBareHistory (bound : Ordinal.{u}) : ZFSet.{u} :=
  canonicalBareHistoryBelow (Order.succ bound)

@[simp]
theorem mem_canonicalBareHistoryBelow_iff
    {bound : Ordinal.{u}} {entry : ZFSet.{u}} :
    entry ∈ canonicalBareHistoryBelow bound ↔
      ∃ ordinal < bound, canonicalBareHistoryPair ordinal = entry := by
  rw [canonicalBareHistoryBelow, mem_replacementRangeZF_iff]
  constructor
  · rintro ⟨ordinal, hordinal, hentry⟩
    exact ⟨ordinal, hordinal, hentry⟩
  · rintro ⟨ordinal, hordinal, hentry⟩
    exact ⟨ordinal, hordinal, hentry⟩

@[simp]
theorem mem_canonicalBareHistory_iff
    {bound : Ordinal.{u}} {entry : ZFSet.{u}} :
    entry ∈ canonicalBareHistory bound ↔
      ∃ ordinal ≤ bound, canonicalBareHistoryPair ordinal = entry := by
  rw [canonicalBareHistory, mem_canonicalBareHistoryBelow_iff]
  apply exists_congr
  intro ordinal
  rw [Order.lt_succ_iff]











/-! ## Proper-class constructibility (not a local bound) -/

/-- The canonical graph agrees extensionally with the Replacement graph
already constructed in the full class `L`, hence is itself constructible.
This theorem deliberately gives only membership in `L`. -/
theorem canonicalBareHistory_mem_L (bound : Ordinal.{u}) :
    canonicalBareHistory bound ∈ L := by
  rcases exists_bareStagePairFamily bound with ⟨history, hhistory⟩
  have heq : history.1 = canonicalBareHistory bound := by
    apply ZFSet.ext
    intro entry
    constructor
    · intro hentry
      have hentryL : entry ∈ L := mem_L_of_mem hentry history.2
      let entryL : LCarrier.{u} := ⟨entry, hentryL⟩
      rcases (hhistory entryL).mp hentry with
        ⟨index, hindex, stage, relation, hstate, hcode⟩
      rcases exists_eq_ordinalLCarrier_of_mem hindex with
        ⟨ordinal, hordinal, hindexEq⟩
      subst index
      rcases exists_stageStateAt_ordinal ordinal with
        ⟨canonicalRelation, hcanonical⟩
      have houtputs := stageStateAt_ordinal_outputs_unique ordinal
        hstate hcanonical
      apply mem_canonicalBareHistory_iff.mpr
      refine ⟨ordinal, Order.lt_succ_iff.mp hordinal, ?_⟩
      apply Eq.symm
      calc
        entry = ZFSet.pair (ordinalLCarrier ordinal).1 stage.1 := hcode
        _ = canonicalBareHistoryPair ordinal := by
          rw [houtputs.1]
          rfl
    · intro hentry
      rcases mem_canonicalBareHistory_iff.mp hentry with
        ⟨ordinal, hordinal, hcode⟩
      have hpairL : canonicalBareHistoryPair ordinal ∈ L := by
        exact orderedPair_mem_L
          (ordinal_toZFSet_mem_L ordinal)
          (LStageZF_mem_L ordinal)
      let entryL : LCarrier.{u} :=
        ⟨canonicalBareHistoryPair ordinal, hpairL⟩
      have hentryFamily : entryL.1 ∈ history.1 :=
        (hhistory entryL).mpr (by
          refine ⟨ordinalLCarrier ordinal, ?_, ?_⟩
          · exact (ordinalLCarrier_mem_ordinalLCarrier_iff
              (Order.succ bound) ordinal).mpr
              (Order.lt_succ_iff.mpr hordinal)
          · rcases exists_stageStateAt_ordinal ordinal with
              ⟨relation, hstate⟩
            exact ⟨stageLCarrier ordinal, relation, hstate, rfl⟩)
      change canonicalBareHistoryPair ordinal ∈ history.1 at hentryFamily
      rw [hcode] at hentryFamily
      exact hentryFamily
  rw [← heq]
  exact history.2

/-- The canonical history packaged as an element of the full constructible
universe.  Its subtype proof must not be used as a substitute for a local
`LStageZF` membership proof. -/
def canonicalBareHistoryLCarrier (bound : Ordinal.{u}) : LCarrier.{u} :=
  ⟨canonicalBareHistory bound, canonicalBareHistory_mem_L bound⟩

@[simp]
theorem canonicalBareHistoryLCarrier_val (bound : Ordinal.{u}) :
    (canonicalBareHistoryLCarrier bound).1 = canonicalBareHistory bound :=
  rfl

/-! ## A formula for one canonical bare pair -/

/-- After binding an index and a stage to the free layout `(fixed13,pair)`,
select the existing `(fixed13,index,stage)` bare-stage layout. -/
def canonicalBarePairStageRename : Fin 15 → Fin 16 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15]

/-- Free layout `(fixed13,pair)`.  The formula says that `pair` is the
Kuratowski pair of an ordinal index and a stage recognized by the existing
relation-free stage predicate. -/
def canonicalBarePairFormula : FOFormula 14 :=
  .ex (.ex
    (.conj
      (ordinalAt (14 : Fin 16))
      (.conj
        (FOFormula.rename canonicalBarePairStageRename bareStageAtFormula)
        (Delta0Formula.kuratowskiPairEqAt
          (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)).toFO)))

/-- Raw free assignment `(fixed13,pair)`. -/
def canonicalBarePairRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (pair : ZFSet.{u}) :
    Tuple ZFSet.{u} 14 :=
  snoc fixed pair

/-- Raw assignment after adjoining the hidden index and stage. -/
def canonicalBarePairWitnessRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (snoc (canonicalBarePairRawAssignment fixed pair) index) stage











/-- Raw values of the thirteen canonical evaluator parameters. -/
def canonicalBareFixedParameters : Tuple ZFSet.{u} 13 :=
  fun i => (stageHistoryFixedParameters.{u} i).1

/-- The exact, assumption-transparent correctness contract used below.  It
speaks about `BareStageAtIn`, not syntactic satisfaction; the preceding raw
semantic theorem is the bridge between the two. -/
def CanonicalBareStagesCorrectIn (U : ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13) : Prop :=
  ∀ ordinal : Ordinal.{u}, ∀ stage : ZFSet.{u},
    ordinal.toZFSet ∈ U → stage ∈ U →
      (BareStageAtIn (U : Set ZFSet.{u}) fixed
          ordinal.toZFSet stage ↔
        stage = LStageZF ordinal)





/-! ## Pointwise stage bounds -/







/-! ## Ordinal bookkeeping for the intended local bound -/







/-! ## Conditional local Separation at a limit -/













end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistory


/- Source module: Solutions.Work_CUGCH_CondensationReflection -/
section GCHSource_Work_CUGCH_CondensationReflection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Cofinal reflection levels for condensation

A condensation argument needs an ambient level at which the fixed internal
definition of the constructible hierarchy is correct.  This is separate from
the later requirement that a Skolem hull be elementary for *all* formulas.

The single formula below contains both the `V = L` core and, as a syntactic
subformula, the assertion that a stage exists at a supplied index.  Applying
the existing reflection construction to that formula gives arbitrarily high
limit levels at which both relevant subformulas are absolute to `L`.
-/

section

universe u

namespace Constructible

open Set

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

/-- The formula whose closure supplies both ingredients needed by the
condensation proof.  The second conjunct is used only to place
`exists stage, InternalLStageAt index stage` among its subformulas; it is not
asserted for nonordinal indices. -/
def condensationReflectionFormula : FOFormula 13 :=
  .conj vEqualsLCoreFormula
    (FOFormula.all (.ex internalLStageAtFormula))

/-- A common starting level containing all thirteen fixed evaluator
parameters. -/
noncomputable def condensationParameterBound : Ordinal.{u} :=
  iSup fun i : Fin 13 =>
    stageOf (stageHistoryFixedParameters.{u} i).1
      (stageHistoryFixedParameters.{u} i).2

theorem stageHistoryFixedParameters_mem_parameterBound (i : Fin 13) :
    (stageHistoryFixedParameters.{u} i).1 ∈
      LStageZF condensationParameterBound := by
  unfold condensationParameterBound
  exact LStageZF_mono
    (Ordinal.le_iSup
      (fun j : Fin 13 =>
        stageOf (stageHistoryFixedParameters.{u} j).1
          (stageHistoryFixedParameters.{u} j).2) i)
    (mem_LStageZF_stageOf (stageHistoryFixedParameters.{u} i).1
      (stageHistoryFixedParameters.{u} i).2)

/-- The canonical cofinal family of levels used by condensation. -/
noncomputable def condensationReflectionOrdinal (alpha : Ordinal.{u}) :
    Ordinal.{u} :=
  reflectionOrdinal condensationReflectionFormula
    (max alpha condensationParameterBound)

theorem le_condensationReflectionOrdinal (alpha : Ordinal.{u}) :
    alpha ≤ condensationReflectionOrdinal alpha := by
  exact (le_max_left alpha condensationParameterBound).trans
    (le_reflectionOrdinal condensationReflectionFormula
      (max alpha condensationParameterBound))

theorem condensationReflectionOrdinal_isSuccLimit (alpha : Ordinal.{u}) :
    Order.IsSuccLimit (condensationReflectionOrdinal alpha) :=
  reflectionOrdinal_isSuccLimit condensationReflectionFormula
    (max alpha condensationParameterBound)

theorem stageHistoryFixedParameters_mem_condensationReflectionOrdinal
    (alpha : Ordinal.{u}) (i : Fin 13) :
    (stageHistoryFixedParameters.{u} i).1 ∈
      LStageZF (condensationReflectionOrdinal alpha) := by
  apply LStageZF_mono _
    (stageHistoryFixedParameters_mem_parameterBound i)
  exact (le_max_right alpha condensationParameterBound).trans
    (le_reflectionOrdinal condensationReflectionFormula
      (max alpha condensationParameterBound))

/-- Closure data retained from the reflection construction.  Keeping the
closure, rather than only the truth value of one sentence, exposes the two
subformula absoluteness statements needed below. -/
def IsCondensationReflectionLevel (theta : Ordinal.{u}) : Prop :=
  Order.IsSuccLimit theta ∧
    (∀ i : Fin 13,
      (stageHistoryFixedParameters.{u} i).1 ∈ LStageZF theta) ∧
    ClosesFrom vEqualsLCoreFormula theta theta ∧
    ClosesFrom (.ex internalLStageAtFormula) theta theta

 theorem closes_vEquals_of_closes_condensationReflection
    {theta : Ordinal.{u}}
    (hclose : ClosesFrom condensationReflectionFormula theta theta) :
    ClosesFrom vEqualsLCoreFormula theta theta :=
  hclose.1

 theorem closes_existsStage_of_closes_condensationReflection
    {theta : Ordinal.{u}}
    (hclose : ClosesFrom condensationReflectionFormula theta theta) :
    ClosesFrom (.ex internalLStageAtFormula) theta theta := by
  exact hclose.2.1

/-- Condensation reflection levels occur above every prescribed ordinal. -/
theorem exists_condensationReflectionLevel (alpha : Ordinal.{u}) :
    ∃ theta : Ordinal.{u}, alpha ≤ theta ∧
      IsCondensationReflectionLevel theta := by
  let theta := condensationReflectionOrdinal alpha
  have hclose :
      ClosesFrom condensationReflectionFormula theta theta :=
    closesFrom_reflectionOrdinal condensationReflectionFormula
      (max alpha condensationParameterBound)
  refine ⟨theta, le_condensationReflectionOrdinal alpha,
    condensationReflectionOrdinal_isSuccLimit alpha, ?_,
    closes_vEquals_of_closes_condensationReflection hclose,
    closes_existsStage_of_closes_condensationReflection hclose⟩
  intro i
  exact stageHistoryFixedParameters_mem_condensationReflectionOrdinal alpha i







end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_CondensationReflection


/- Source module: Solutions.Work_CUGCH_FiniteFragmentElementarity -/
section GCHSource_Work_CUGCH_FiniteFragmentElementarity
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Elementarity for a finite formula fragment

This file isolates the Tarski--Vaught argument needed by the later Skolem-hull
and condensation construction.  For one fixed formula, `ClosesWithin` asks a
smaller carrier to contain witnesses for every existential subformula, with
parameters from the smaller carrier.  This finite closure condition is enough
to make satisfaction of the formula absolute between the two carriers.

Unlike a full elementary-substructure predicate, this construction does not
quantify over or encode all first-order formulas.  That distinction matters
for the cardinality-controlled hull used in the proof of GCH in `L`.
-/

section

open Set

universe u

namespace Constructible

section ZFC

/--
`ClosesWithin phi small big` says that `small` contains a witness, whenever
`big` satisfies an existential subformula of `phi` with parameters in
`small`.  The recursive clauses impose the same condition on every subformula
of `phi`.
-/
def ClosesWithin (small big : Set ZFSet.{u}) :
    {n : Nat} -> FOFormula n -> Prop
  | _, .mem _ _ => True
  | _, .eq _ _ => True
  | _, .neg phi => ClosesWithin small big phi
  | _, .conj phi psi =>
      ClosesWithin small big phi /\ ClosesWithin small big psi
  | n, .ex phi =>
      ClosesWithin small big phi /\
        forall s : Tuple ZFSet.{u} n,
          (forall i, s i ∈ small) ->
          Model.SatisfiesIn big (.ex phi) s ->
          exists x : ZFSet.{u},
            x ∈ small /\ Model.SatisfiesIn big phi (snoc s x)





/-! ## The extensionality fragment -/

/-- A witness belongs to exactly one of the two free set variables. -/
def distinguishingMemberFormula : FOFormula 2 :=
  .ex (FOFormula.disj
    (.conj
      (.mem (Fin.last 2) (0 : Fin 2).castSucc)
      (.neg (.mem (Fin.last 2) (1 : Fin 2).castSucc)))
    (.conj
      (.mem (Fin.last 2) (1 : Fin 2).castSucc)
      (.neg (.mem (Fin.last 2) (0 : Fin 2).castSucc))))

@[simp]
theorem satisfiesIn_distinguishingMemberFormula
    (carrier : Set ZFSet.{u}) (x y : ZFSet.{u}) :
    Model.SatisfiesIn carrier distinguishingMemberFormula ![x, y] <->
      exists z : ZFSet.{u}, z ∈ carrier /\
        ((z ∈ x /\ z ∉ y) \/ (z ∈ y /\ z ∉ x)) := by
  classical
  simp only [distinguishingMemberFormula, Model.SatisfiesIn,
    FOFormula.disj, snoc_last, snoc_castSucc,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  apply exists_congr
  intro z
  apply and_congr_right
  intro _hz
  tauto



end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_FiniteFragmentElementarity


/- Source module: Solutions.Work_CUGCH_FiniteFragmentSkolemHull -/
section GCHSource_Work_CUGCH_FiniteFragmentSkolemHull
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Full elementarity and internally represented omega unions

The first part of this file upgrades the one-formula Tarski--Vaught interface
from `FiniteFragmentElementarity` to an external quantification over every
first-order formula.  This is the elementarity notion required by a genuine
Mostowski condensation theorem; closure under one fixed finite fragment is
not substituted for full elementarity.

The second part isolates the internal set construction used by a Skolem-hull
argument.  If one fixed first-order formula uniformly defines an omega-indexed
family of constructible sets, Replacement produces an actual member of `L`
whose members are precisely that family.  Its union is therefore an actual
`ZFSet` in `L`, rather than an external `Set ZFSet`.

This file deliberately does not assert that the full Skolem iteration has
already been constructed.  The implication from closure under all
rudimentary relation sets to elementarity is useful as a semantic comparison,
but that closure predicate is too strong for a cardinal-controlled hull:
nullary singleton relations force the smaller carrier to contain all of `U`.
Consequently a genuine Skolem construction must enumerate only the compiled
relations of first-order formulas; it must not iterate the unrestricted
predicate below.
-/

section

open Set

universe u

namespace Constructible

section ZFC

/-! ## Full Tarski--Vaught closure -/

/-- Closure under witnesses for every first-order formula and all of its
subformulas.  Formula syntax is quantified over externally here. -/
def ClosesWithinAll (small big : Set ZFSet.{u}) : Prop :=
  forall {n : Nat} (phi : FOFormula n), ClosesWithin small big phi

/-- Satisfaction is absolute between `small` and `big` for every formula
whose free parameters lie in `small`. -/
def SatisfactionAbsolute (small big : Set ZFSet.{u}) : Prop :=
  forall {n : Nat} (phi : FOFormula n) (s : Tuple ZFSet.{u} n),
    (forall i, s i ∈ small) ->
      (Model.SatisfiesIn small phi s <-> Model.SatisfiesIn big phi s)









/-! ## Full formula closure through rudimentary relation sets -/







/-! ## A uniform omega-indexed Replacement interface -/

namespace Model

open FiniteSequenceZF

local notation "LMem" => lCarrierMem

/-- The constructible carrier corresponding to the von Neumann code of `n`. -/
noncomputable def natLCarrier (n : Nat) : LCarrier.{u} :=
  ⟨natCode n, natCode_mem_L n⟩

@[simp]
theorem natLCarrier_val (n : Nat) : (natLCarrier n).1 = natCode n :=
  rfl

/--
Data showing that one fixed object-language formula uniformly defines an
omega-indexed family.  The formula layout is `[index, value]`.

This is intentionally stronger than merely giving an external function
`Nat -> LCarrier`: the uniform formula is exactly what permits internal
Replacement over `omega`.
-/
structure UniformOmegaFamilySpec where
  formula : FOFormula 2
  value : Nat -> LCarrier.{u}
  realizes : forall (n : Nat) (y : LCarrier.{u}),
    FOFormula.Satisfies LMem formula ![natLCarrier n, y] <-> y = value n

 theorem snoc_snoc_empty_eq_pair
    (x y : LCarrier.{u}) :
    snoc (snoc (fun i : Fin 0 => Fin.elim0 i) x) y = ![x, y] := by
  funext i
  fin_cases i <;> rfl

/-- Replacement can be applied to every uniform omega-family specification. -/
theorem exists_uniformOmegaFamily (spec : UniformOmegaFamilySpec.{u}) :
    exists family : LCarrier.{u}, forall y : LCarrier.{u},
      y.1 ∈ family.1 <-> exists n : Nat, y = spec.value n := by
  let noParams : Tuple LCarrier.{u} 0 := fun i => Fin.elim0 i
  have hfun : forall x : LCarrier.{u}, x.1 ∈ omegaLCarrier.1 ->
      ∃! y : LCarrier.{u},
        FOFormula.Satisfies LMem spec.formula
          (snoc (snoc noParams x) y) := by
    intro x hx
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x.1).mp hx with
      ⟨n, hxCode⟩
    have hxNat : x = natLCarrier n := Subtype.ext hxCode
    refine ⟨spec.value n, ?_, ?_⟩
    · change FOFormula.Satisfies LMem spec.formula
        (snoc (snoc noParams x) (spec.value n))
      rw [show snoc (snoc noParams x) (spec.value n) =
          ![natLCarrier n, spec.value n] by
        simpa only [noParams, hxNat] using
          snoc_snoc_empty_eq_pair (natLCarrier n) (spec.value n)]
      exact (spec.realizes n (spec.value n)).mpr rfl
    · intro y hy
      apply (spec.realizes n y).mp
      rw [← show snoc (snoc noParams x) y = ![natLCarrier n, y] by
        simpa only [noParams, hxNat] using
          snoc_snoc_empty_eq_pair (natLCarrier n) y]
      exact hy
  rcases exists_replacementLCarrier spec.formula noParams omegaLCarrier hfun with
    ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro y
  rw [hfamily]
  constructor
  · rintro ⟨x, hxOmega, hxy⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x.1).mp hxOmega with
      ⟨n, hxCode⟩
    have hxNat : x = natLCarrier n := Subtype.ext hxCode
    refine ⟨n, (spec.realizes n y).mp ?_⟩
    rw [← show snoc (snoc noParams x) y = ![natLCarrier n, y] by
      simpa only [noParams, hxNat] using
        snoc_snoc_empty_eq_pair (natLCarrier n) y]
    exact hxy
  · rintro ⟨n, rfl⟩
    refine ⟨natLCarrier n, ?_, ?_⟩
    · change natCode n ∈ Ordinal.omega0.toZFSet
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
        (Ordinal.natCast_lt_omega0 n)
    · change FOFormula.Satisfies LMem spec.formula
        (snoc (snoc noParams (natLCarrier n)) (spec.value n))
      rw [show snoc (snoc noParams (natLCarrier n)) (spec.value n) =
          ![natLCarrier n, spec.value n] by
        simpa only [noParams] using
          snoc_snoc_empty_eq_pair (natLCarrier n) (spec.value n)]
      exact (spec.realizes n (spec.value n)).mpr rfl

/-- The internally represented range selected from Replacement. -/
noncomputable def uniformOmegaFamily
    (spec : UniformOmegaFamilySpec.{u}) : LCarrier.{u} :=
  Classical.choose (exists_uniformOmegaFamily spec)

@[simp]
theorem mem_uniformOmegaFamily_iff
    (spec : UniformOmegaFamilySpec.{u}) (y : LCarrier.{u}) :
    y.1 ∈ (uniformOmegaFamily spec).1 <->
      exists n : Nat, y = spec.value n :=
  Classical.choose_spec (exists_uniformOmegaFamily spec) y

/-- The actual internal union of all values in a uniform omega-family. -/
noncomputable def uniformOmegaUnion
    (spec : UniformOmegaFamilySpec.{u}) : LCarrier.{u} :=
  sUnionLCarrier (uniformOmegaFamily spec)

@[simp]
theorem mem_uniformOmegaUnion_iff
    (spec : UniformOmegaFamilySpec.{u}) (z : LCarrier.{u}) :
    z.1 ∈ (uniformOmegaUnion spec).1 <->
      exists n : Nat, z.1 ∈ (spec.value n).1 := by
  rw [uniformOmegaUnion, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨stage, hstage, hz⟩
    rcases (mem_uniformOmegaFamily_iff spec stage).mp hstage with
      ⟨n, rfl⟩
    exact ⟨n, hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨spec.value n,
      (mem_uniformOmegaFamily_iff spec (spec.value n)).mpr ⟨n, rfl⟩,
      hz⟩





end Model

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_FiniteFragmentSkolemHull


/- Source module: Solutions.Work_CUGCH_MostowskiCollapse -/
section GCHSource_Work_CUGCH_MostowskiCollapse
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Mostowski collapse for set-sized membership structures

This file develops the external collapse of membership restricted to a
`ZFSet`.  The recursion is along genuine well-founded membership, while each
recursive image is again packaged as a `ZFSet`.
-/

section

universe u

namespace Constructible.MostowskiCollapse

noncomputable section

/-- The collapse of `x`, using only predecessors which belong to `domain`. -/
noncomputable def collapse (domain x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun y : {y : ZFSet.{u} // y ∈ x ∩ domain} =>
    collapse domain y.1
termination_by x
decreasing_by
  exact (ZFSet.mem_inter.mp y.2).1

/-- Membership in the collapse is exactly membership through a predecessor
which lies in the restricted domain. -/
@[simp]
theorem mem_collapse_iff {domain x z : ZFSet.{u}} :
    z ∈ collapse domain x ↔
      ∃ y : ZFSet.{u}, y ∈ x ∧ y ∈ domain ∧ collapse domain y = z := by
  rw [collapse, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨y, hy⟩, hvalue⟩
    exact ⟨y, (ZFSet.mem_inter.mp hy).1,
      (ZFSet.mem_inter.mp hy).2, hvalue⟩
  · rintro ⟨y, hyx, hydomain, hvalue⟩
    exact ⟨⟨y, ZFSet.mem_inter.mpr ⟨hyx, hydomain⟩⟩, hvalue⟩

/-- The transitive target of the collapse. -/
noncomputable def range (domain : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun x : {x : ZFSet.{u} // x ∈ domain} =>
    collapse domain x.1

@[simp]
theorem mem_range_iff {domain z : ZFSet.{u}} :
    z ∈ range domain ↔
      ∃ x : ZFSet.{u}, x ∈ domain ∧ collapse domain x = z := by
  rw [range, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨x, hx⟩, hvalue⟩
    exact ⟨x, hx, hvalue⟩
  · rintro ⟨x, hx, hvalue⟩
    exact ⟨⟨x, hx⟩, hvalue⟩



/-- Extensionality of membership after both arguments and all predecessors
are restricted to `domain`. -/
def IsExtensional (domain : ZFSet.{u}) : Prop :=
  ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain →
    ∀ ⦃y : ZFSet.{u}⦄, y ∈ domain →
      (∀ z : ZFSet.{u}, z ∈ domain → (z ∈ x ↔ z ∈ y)) → x = y

/-- Extensionality of the restricted membership structure makes the collapse
injective on its domain. -/
theorem collapse_eq_imp_eq_of_mem {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) :
    ∀ x : ZFSet.{u}, x ∈ domain →
      ∀ y : ZFSet.{u}, y ∈ domain →
        collapse domain x = collapse domain y → x = y := by
  intro x
  refine ZFSet.inductionOn
    (p := fun x => x ∈ domain →
      ∀ y : ZFSet.{u}, y ∈ domain →
        collapse domain x = collapse domain y → x = y)
    x ?_
  intro x ih hxdomain y hydomain hcollapse
  apply hextensional hxdomain hydomain
  intro z hzdomain
  constructor
  · intro hzx
    have hzCollapse : collapse domain z ∈ collapse domain x :=
      mem_collapse_iff.mpr ⟨z, hzx, hzdomain, rfl⟩
    rw [hcollapse] at hzCollapse
    rcases mem_collapse_iff.mp hzCollapse with
      ⟨w, hwy, hwdomain, hwz⟩
    have hzw : z = w :=
      ih z hzx hzdomain w hwdomain hwz.symm
    simpa only [hzw] using hwy
  · intro hzy
    have hzCollapse : collapse domain z ∈ collapse domain y :=
      mem_collapse_iff.mpr ⟨z, hzy, hzdomain, rfl⟩
    rw [← hcollapse] at hzCollapse
    rcases mem_collapse_iff.mp hzCollapse with
      ⟨w, hwx, hwdomain, hwz⟩
    have hwz' : w = z :=
      ih w hwx hwdomain z hzdomain hwz
    simpa only [hwz'] using hwx



/-- The collapse map with its codomain restricted to the collapse range. -/
def toRange (domain : ZFSet.{u}) :
    {x : ZFSet.{u} // x ∈ domain} →
      {z : ZFSet.{u} // z ∈ range domain} :=
  fun x => ⟨collapse domain x.1,
    mem_range_iff.mpr ⟨x.1, x.2, rfl⟩⟩

@[simp]
theorem toRange_val (domain : ZFSet.{u})
    (x : {x : ZFSet.{u} // x ∈ domain}) :
    (toRange domain x).1 = collapse domain x.1 := rfl

theorem toRange_surjective (domain : ZFSet.{u}) :
    Function.Surjective (toRange domain) := by
  intro z
  rcases mem_range_iff.mp z.2 with ⟨x, hx, hvalue⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hvalue

theorem toRange_injective {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) :
    Function.Injective (toRange domain) := by
  intro x y hxy
  apply Subtype.ext
  apply collapse_eq_imp_eq_of_mem hextensional x.1 x.2 y.1 y.2
  exact congrArg Subtype.val hxy

/-- The Mostowski equivalence between an extensional restricted membership
structure and its transitive collapse range. -/
noncomputable def equivRange {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) :
    {x : ZFSet.{u} // x ∈ domain} ≃
      {z : ZFSet.{u} // z ∈ range domain} :=
  Equiv.ofBijective (toRange domain)
    ⟨toRange_injective hextensional, toRange_surjective domain⟩

@[simp]
theorem equivRange_apply {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (x : {x : ZFSet.{u} // x ∈ domain}) :
    (equivRange hextensional x).1 = collapse domain x.1 := rfl

/-- On an extensional restricted structure, the collapse preserves and
reflects membership. -/
theorem collapse_mem_collapse_iff {domain x y : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (hxdomain : x ∈ domain) (_hydomain : y ∈ domain) :
    collapse domain x ∈ collapse domain y ↔ x ∈ y := by
  constructor
  · intro hcollapse
    rcases mem_collapse_iff.mp hcollapse with
      ⟨z, hzy, hzdomain, hzx⟩
    have hxz : x = z := collapse_eq_imp_eq_of_mem hextensional
      x hxdomain z hzdomain hzx.symm
    simpa only [hxz] using hzy
  · intro hxy
    exact mem_collapse_iff.mpr ⟨x, hxy, hxdomain, rfl⟩

@[simp]
theorem equivRange_mem_iff {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (x y : {x : ZFSet.{u} // x ∈ domain}) :
    (equivRange hextensional x).1 ∈ (equivRange hextensional y).1 ↔
      x.1 ∈ y.1 := by
  simp only [equivRange_apply]
  exact collapse_mem_collapse_iff hextensional x.2 y.2





end

end Constructible.MostowskiCollapse

end
end GCHSource_Work_CUGCH_MostowskiCollapse


