-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library13
-- name    : CH_ConstructibleAC_Library13
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:36:10.07307+00:00
-- url     : https://prove2.me/theorems/2a1ffb71-a32b-4917-856d-cc077fc17a11
-- title:
--   Defining and collecting stage histories
-- statement:
--   A valid stage history must satisfy the base, successor, and limit conditions and assign compatible data to its ordinal indices. This library provides the formulas and constructor interfaces for validity, functionality, ordinal indexing, state lookup, history operations, and replacement. They support collecting the recursively defined earlier stages into a set-coded history.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistorySuccessorFormula.lean#L1-L362; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryFunctionality.lean#L1-L130; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/ValidStageHistoryFormula.lean#L1-L435; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryOrdinal.lean#L1-L123; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageStateAtFormula.lean#L1-L384; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryOperations.lean#L1-L102; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryReplacement.lean#L1-L277

import Definitions.Def_CH_ConstructibleAC_Library12
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

/-!
# Adaptation of Zike Liu's constructible-universe Choice proof

Original formalization: Copyright (c) 2026 Zike Liu, Apache-2.0.
Source: https://github.com/05-02-07/lean-constructible-universe
Commit: 7f5a7d03d63d9769172f17350bbe8303996e5b53.
All original per-file copyright notices are retained below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

This credit concerns the Prove2Me adaptation and semantic bridge. The original
well-ordering formalization is by Zike Liu, credited above and in each source section.
-/

set_option autoImplicit false


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistorySuccessorFormula -/
section CUAdapterModule85
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The successor-state clause for constructible-stage histories

The outer layout is `(fixed13, history, index, stage, relation)`.  Three
existential witnesses append `(predecessorIndex, predecessorStage,
predecessorRelation)`.  The existing deterministic successor-state formula
is then renamed into this combined context.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- Select
`(predecessorStage, fixed13, predecessorRelation, stage, relation)`
from the twenty-coordinate successor-history witness layout. -/
def historySuccessorStepRename : Fin 17 → Fin 20 :=
  Fin.lastCases
    (16 : Fin 20)
    (fun i15 => Fin.lastCases
      (15 : Fin 20)
      (fun i14 => Fin.lastCases
        (19 : Fin 20)
        (fun i13 => Fin.cases
          (18 : Fin 20)
          (fun j => Fin.castLE (by decide) j)
          i13)
        i14)
      i15)

/-- Assignment after adjoining the three predecessor witnesses. -/
def historySuccessorWitnessAssignment
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    Tuple LCarrier.{u} 20 :=
  snoc
    (snoc
      (snoc (stageHistoryStateLAssignment history index stage relation)
        predecessorIndex)
      predecessorStage)
    predecessorRelation

 lemma historySuccessorWitnessAssignment_expanded_eq
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    snoc
        (snoc
          (snoc (stageHistoryStateLAssignment history index stage relation)
            predecessorIndex)
          predecessorStage)
        predecessorRelation =
      historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation := by
  rfl

@[simp]  lemma historySuccessorWitness_history
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (13 : Fin 20) =
      history := by
  rw [show (13 : Fin 20) =
      (13 : Fin 17).castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_castSucc,
    stageHistoryStateLAssignment_history]

@[simp]  lemma historySuccessorWitness_index
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (14 : Fin 20) =
      index := by
  rw [show (14 : Fin 20) =
      (14 : Fin 17).castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_castSucc,
    stageHistoryStateLAssignment_index]

@[simp]  lemma historySuccessorWitness_predecessorIndex
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (17 : Fin 20) =
      predecessorIndex := by
  rw [show (17 : Fin 20) = (Fin.last 17).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_castSucc, snoc_last]

@[simp]  lemma historySuccessorWitness_predecessorStageProjection
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (18 : Fin 20) =
      predecessorStage := by
  rw [show (18 : Fin 20) = (Fin.last 18).castSucc by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_castSucc, snoc_last]

@[simp]  lemma historySuccessorWitness_predecessorRelation
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (19 : Fin 20) =
      predecessorRelation := by
  rw [show (19 : Fin 20) = Fin.last 19 by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_last]

 lemma insert_self_eq_union_singleton (x : ZFSet.{u}) :
    insert x x = x ∪ {x} := by
  rw [ZFSet.insert_eq]
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_union, or_comm]

 lemma historySuccessorWitness_fixed
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) (i : Fin 13) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation
          i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  simp only [historySuccessorWitnessAssignment,
    stageHistoryStateLAssignment, snoc_castSucc]

 lemma historySuccessorWitness_fixed_castLE
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) (i : Fin 13) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  exact historySuccessorWitness_fixed history index stage relation
    predecessorIndex predecessorStage predecessorRelation i

 lemma successorStageState_fixedParameters
    (predecessorStage predecessorRelation stage relation : LCarrier.{u})
    (i : Fin 13) :
    successorStageStateLAssignment
        predecessorStage predecessorRelation stage relation
          i.succ.castSucc.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [successorStageStateLAssignment,
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
      snoc_castSucc, stageHistoryFixedParameters_last,
      Fin.succ_last, snoc_last]
  · rw [stageHistoryFixedParameters_init predecessorStage k]
    simp only [successorStageStateLAssignment,
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
      snoc_castSucc, Fin.succ_castSucc]

 lemma historySuccessor_relation_coordinate
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (16 : Fin 20) =
      successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (16 : Fin 17) := by
  rfl

 lemma historySuccessor_stage_coordinate
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (15 : Fin 20) =
      successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (15 : Fin 17) := by
  rfl

 lemma historySuccessor_predecessorRelation_coordinate
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (19 : Fin 20) =
      successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (14 : Fin 17) := by
  rfl

 lemma historySuccessorWitness_predecessorStage
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (18 : Fin 20) = predecessorStage := by
  rfl

 lemma successorStageState_to_parameters
    (predecessorStage predecessorRelation stage relation : LCarrier.{u})
    (i : Fin 15) :
    successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation i.castSucc.castSucc =
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
        predecessorStage predecessorRelation i := by
  simp only [successorStageStateLAssignment, snoc_castSucc]

 lemma leastParameters_to_stackPrefix
    (predecessorStage predecessorRelation : LCarrier.{u}) (i : Fin 13) :
    Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
        predecessorStage predecessorRelation i.castSucc.castSucc =
      Godel.RudimentaryTerm.stackStepPrefixLAssignment
        predecessorStage.1 predecessorStage.2 i := by
  simp only [Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
    snoc_castSucc]

 lemma stackStepPrefix_zero (predecessorStage : LCarrier.{u}) :
    Godel.RudimentaryTerm.stackStepPrefixLAssignment
        predecessorStage.1 predecessorStage.2 (0 : Fin 13) =
      predecessorStage := by
  apply Subtype.ext
  have h := congrFun
    (Godel.RudimentaryTerm.stackStepPrefixLAssignment_val
      predecessorStage.1 predecessorStage.2) (0 : Fin 13)
  exact h

 lemma successorStageState_predecessorStage
    (predecessorStage predecessorRelation stage relation : LCarrier.{u}) :
    successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (0 : Fin 17) = predecessorStage := by
  exact (successorStageState_to_parameters predecessorStage
    predecessorRelation stage relation ((0 : Fin 13).castSucc.castSucc)).trans
    ((leastParameters_to_stackPrefix predecessorStage predecessorRelation
      (0 : Fin 13)).trans (stackStepPrefix_zero predecessorStage))

 lemma historySuccessor_predecessorStage_coordinate
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (18 : Fin 20) =
      successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (0 : Fin 17) :=
  (historySuccessorWitness_predecessorStage history index stage relation
    predecessorIndex predecessorStage predecessorRelation).trans
    (successorStageState_predecessorStage predecessorStage
      predecessorRelation stage relation).symm

 lemma historySuccessorStepRename_fixed (j : Fin 13) :
    historySuccessorStepRename j.succ.castSucc.castSucc.castSucc =
      Fin.castLE (by decide) j := by
  simp only [historySuccessorStepRename,
    Fin.lastCases_castSucc, Fin.cases_succ]

theorem comp_historySuccessorStepRename
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    (fun i => historySuccessorWitnessAssignment
      history index stage relation predecessorIndex predecessorStage
        predecessorRelation (historySuccessorStepRename i)) =
      successorStageStateLAssignment
        predecessorStage predecessorRelation stage relation := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · exact historySuccessor_relation_coordinate history index stage relation
      predecessorIndex predecessorStage predecessorRelation
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · exact historySuccessor_stage_coordinate history index stage relation
        predecessorIndex predecessorStage predecessorRelation
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · exact historySuccessor_predecessorRelation_coordinate history index
          stage relation predecessorIndex predecessorStage predecessorRelation
      · refine Fin.cases ?_ (fun j => ?_) i13
        · exact historySuccessor_predecessorStage_coordinate history index
            stage relation predecessorIndex predecessorStage predecessorRelation
        · rw [historySuccessorStepRename_fixed]
          exact (historySuccessorWitness_fixed_castLE history index stage
            relation predecessorIndex predecessorStage predecessorRelation j).trans
            (successorStageState_fixedParameters predecessorStage
              predecessorRelation stage relation j).symm

/-- The local recursion rule at a successor index. -/
def historySuccessorStateFormula : FOFormula 17 :=
  .ex (.ex (.ex
    (.conj
      (Delta0Formula.successorFOAt (14 : Fin 20) (17 : Fin 20))
      (.conj
        (historyEntryAt
          (13 : Fin 20) (17 : Fin 20) (18 : Fin 20) (19 : Fin 20))
        (FOFormula.rename historySuccessorStepRename
          successorStageStateFormula)))))

@[simp]
theorem satisfies_historySuccessorStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historySuccessorStateFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      ∃ predecessorIndex predecessorStage predecessorRelation :
          LCarrier.{u},
        index.1 = predecessorIndex.1 ∪ {predecessorIndex.1} ∧
          HistoryEntry history predecessorIndex
            predecessorStage predecessorRelation ∧
          FOFormula.Satisfies LMem successorStageStateFormula
            (successorStageStateLAssignment
              predecessorStage predecessorRelation stage relation) := by
  simp only [historySuccessorStateFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    satisfies_historyEntryAt_iff, HistoryEntry,
    FOFormula.satisfies_rename,
    historySuccessorWitnessAssignment_expanded_eq,
    comp_historySuccessorStepRename,
    historySuccessorWitness_history, historySuccessorWitness_index,
    historySuccessorWitness_predecessorIndex,
    historySuccessorWitness_predecessorStageProjection,
    historySuccessorWitness_predecessorRelation,
    insert_self_eq_union_singleton]

/-- Fully normalized semantics of the successor-history rule. -/
theorem satisfies_historySuccessorStateFormula_iff_outputs
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historySuccessorStateFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      ∃ predecessorIndex predecessorStage predecessorRelation :
          LCarrier.{u},
        index.1 = predecessorIndex.1 ∪ {predecessorIndex.1} ∧
          HistoryEntry history predecessorIndex
            predecessorStage predecessorRelation ∧
          stage.1 = Godel.godelDef predecessorStage.1 ∧
          relation = canonicalSuccessorStateRelation
            predecessorStage predecessorRelation stage := by
  rw [satisfies_historySuccessorStateFormula]
  apply exists_congr
  intro predecessorIndex
  apply exists_congr
  intro predecessorStage
  apply exists_congr
  intro predecessorRelation
  simp only [satisfies_successorStageStateFormula_iff]

end

end Constructible.Model
end CUAdapterModule85



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryFunctionality -/
section CUAdapterModule86
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Functionality of stage-history lookup

A stage history is functional at an index when it contains exactly one pair
of stage and relation coordinates at that index.  The formula in this file
expresses that property entirely in the first-order membership language.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-!
The free-variable layout is `(history, index)`.  The first two existential
variables are `(stage, relation)`.  Inside the two universal quantifiers the
layout is

`(history, index, stage, relation, otherStage, otherRelation)`.
-/

/-- Once a history entry has been chosen, every other entry at the same index
has the same stage and relation coordinates. -/
def historyStateUniqueBody : FOFormula 4 :=
  FOFormula.all (FOFormula.all
    (FOFormula.imp
      (historyEntryAt
        (0 : Fin 6) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6))
      (.conj
        (.eq (4 : Fin 6) (2 : Fin 6))
        (.eq (5 : Fin 6) (3 : Fin 6)))))

/-- `history` has exactly one `(stage, relation)` state at `index`. -/
def historyHasUniqueStateFormula : FOFormula 2 :=
  .ex (.ex
    (.conj
      (historyEntryAt
        (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4))
      historyStateUniqueBody))

@[simp]  lemma historyStateUniqueWitnessAssignment
    (history index stage relation otherStage otherRelation : LCarrier.{u}) :
    snoc (snoc ![history, index, stage, relation] otherStage) otherRelation =
      ![history, index, stage, relation, otherStage, otherRelation] := by
  funext i
  fin_cases i <;> rfl

@[simp]  lemma historyUniqueStateWitnessAssignment
    (history index stage relation : LCarrier.{u}) :
    snoc (snoc ![history, index] stage) relation =
      ![history, index, stage, relation] := by
  funext i
  fin_cases i <;> rfl

/-- Expanded semantics of the uniqueness body. -/
@[simp]
theorem satisfies_historyStateUniqueBody
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyStateUniqueBody
        ![history, index, stage, relation] ↔
      ∀ otherStage otherRelation : LCarrier.{u},
        HistoryEntry history index otherStage otherRelation →
          otherStage = stage ∧ otherRelation = relation := by
  simp only [historyStateUniqueBody, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.Satisfies]
  apply forall_congr'
  intro otherStage
  apply forall_congr'
  intro otherRelation
  rw [historyStateUniqueWitnessAssignment,
    satisfies_historyEntryAt_iff]
  rfl

/-- Expanded semantics before packaging the two output coordinates as a
product. -/
@[simp]
theorem satisfies_historyHasUniqueStateFormula_expanded
    (history index : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyHasUniqueStateFormula
        ![history, index] ↔
      ∃ stage relation : LCarrier.{u},
        HistoryEntry history index stage relation ∧
          ∀ otherStage otherRelation : LCarrier.{u},
            HistoryEntry history index otherStage otherRelation →
              otherStage = stage ∧ otherRelation = relation := by
  simp only [historyHasUniqueStateFormula, FOFormula.Satisfies]
  apply exists_congr
  intro stage
  apply exists_congr
  intro relation
  rw [historyUniqueStateWitnessAssignment,
    satisfies_historyEntryAt_iff, satisfies_historyStateUniqueBody]
  rfl



end

end Constructible.Model
end CUAdapterModule86



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.ValidStageHistoryFormula -/
section CUAdapterModule87
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A fixed validity formula for constructible-stage histories

The local rule combines the zero, successor, and nonzero-limit clauses in the
shared seventeen-coordinate layout

`(fixed13, history, index, stage, relation)`.

The global validity formula has layout `(fixed13, history, bound)`.  It says
that every index at most `bound` has exactly one history entry, and that its
stage and relation coordinates obey the appropriate local rule.  As in the
indexed-sequence validity predicate, irrelevant extra members of the history
set are permitted; every lookup uses only the total functional part below the
stated bound.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## The unified local rule -/

/-- Select `(history, index, stage, relation)` from the shared seventeen-
coordinate history-state layout. -/
def historyLimitStateRename : Fin 4 → Fin 17 :=
  fun i => Fin.natAdd 13 i

theorem comp_historyLimitStateRename
    (history index stage relation : LCarrier.{u}) :
    (fun i =>
      stageHistoryStateLAssignment history index stage relation
        (historyLimitStateRename i)) =
      historyStateAssignment history index stage relation := by
  funext i
  fin_cases i <;> rfl

/-- The current index is the empty set. -/
def historyIndexIsZeroFormula : FOFormula 17 :=
  .eq (14 : Fin 17) stageHistoryEmptyIndex

/-- The current index has a von Neumann predecessor. -/
def historyIndexHasPredecessorFormula : FOFormula 17 :=
  .ex (Delta0Formula.successorFOAt (14 : Fin 18) (17 : Fin 18))

 lemma historyIndexPredecessorAssignment_index
    (history index stage relation predecessor : LCarrier.{u}) :
    snoc (stageHistoryStateLAssignment history index stage relation) predecessor
        (14 : Fin 18) = index := by
  rw [show (14 : Fin 18) = (14 : Fin 17).castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, stageHistoryStateLAssignment_index]

 lemma historyIndexPredecessorAssignment_predecessor
    (history index stage relation predecessor : LCarrier.{u}) :
    snoc (stageHistoryStateLAssignment history index stage relation) predecessor
        (17 : Fin 18) = predecessor := by
  rw [show (17 : Fin 18) = Fin.last 17 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

@[simp]
theorem satisfies_historyIndexIsZeroFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyIndexIsZeroFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      index = emptyLCarrier := by
  simp only [historyIndexIsZeroFormula, FOFormula.Satisfies,
    stageHistoryStateLAssignment_index,
    stageHistoryStateLAssignment_emptyParameter]

@[simp]
theorem satisfies_historyIndexHasPredecessorFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyIndexHasPredecessorFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      ∃ predecessor : LCarrier.{u},
      index.1 = insert predecessor.1 predecessor.1 := by
  simp only [historyIndexHasPredecessorFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier]
  apply exists_congr
  intro predecessor
  rw [historyIndexPredecessorAssignment_index,
    historyIndexPredecessorAssignment_predecessor]

/-- The exact external condition expressed by the limit-state formula. -/
def HistoryLimitState
    (history index stage relation : LCarrier.{u}) : Prop :=
  (∀ z : LCarrier.{u}, z.1 ∈ stage.1 ↔
    ∃ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 ∧
        ∃ earlierStage earlierRelation : LCarrier.{u},
          HistoryEntry history earlierIndex earlierStage earlierRelation ∧
            z.1 ∈ earlierStage.1) ∧
  (∀ z : LCarrier.{u}, z.1 ∈ relation.1 ↔
    ∃ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 ∧
        ∃ earlierStage earlierRelation : LCarrier.{u},
          HistoryEntry history earlierIndex earlierStage earlierRelation ∧
            z.1 ∈ earlierRelation.1)

theorem satisfies_renamed_historyLimitStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (FOFormula.rename historyLimitStateRename historyLimitStateFormula)
        (stageHistoryStateLAssignment history index stage relation) ↔
      HistoryLimitState history index stage relation := by
  simp only [FOFormula.satisfies_rename, comp_historyLimitStateRename,
    satisfies_historyLimitStateFormula, HistoryLimitState]

/-- The exact external condition expressed by the unified local rule. -/
def HistoryLocalState
    (history index stage relation : LCarrier.{u}) : Prop :=
  (index = emptyLCarrier ∧
    stage = emptyLCarrier ∧ relation = emptyLCarrier) ∨
  (∃ predecessorIndex predecessorStage predecessorRelation : LCarrier.{u},
    index.1 = insert predecessorIndex.1 predecessorIndex.1 ∧
      HistoryEntry history predecessorIndex
        predecessorStage predecessorRelation ∧
      stage.1 = Godel.godelDef predecessorStage.1 ∧
      relation = canonicalSuccessorStateRelation
        predecessorStage predecessorRelation stage) ∨
  (index ≠ emptyLCarrier ∧
    ¬ ∃ predecessor : LCarrier.{u},
      index.1 = insert predecessor.1 predecessor.1) ∧
        HistoryLimitState history index stage relation



/-- Zero, successor, or guarded nonzero-limit recursion at one history entry.
The guards make the three cases disjoint whenever the index is an ordinal. -/
def historyLocalStateFormula : FOFormula 17 :=
  .disj
    historyBaseStateFormula
    (.disj
      historySuccessorStateFormula
      (.conj
        (.conj
          (.neg historyIndexIsZeroFormula)
          (.neg historyIndexHasPredecessorFormula))
        (FOFormula.rename historyLimitStateRename
          historyLimitStateFormula)))

@[simp]
theorem satisfies_historyLocalStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyLocalStateFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      HistoryLocalState history index stage relation := by
  simp only [historyLocalStateFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_historyBaseStateFormula,
    satisfies_historySuccessorStateFormula_iff_outputs,
    satisfies_historyIndexIsZeroFormula,
    satisfies_historyIndexHasPredecessorFormula,
    satisfies_renamed_historyLimitStateFormula, HistoryLocalState,
    insert_self_eq_union_singleton]

/-! ## Total functional validity through a bound -/

/-- Assignment layout `(fixed13, history, bound)`. -/
def validStageHistoryLAssignment
    (history bound : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters history) bound

/-- Assignment after adjoining `(index, stage, relation)`. -/
def validStageHistoryWitnessLAssignment
    (history bound index stage relation : LCarrier.{u}) :
    Tuple LCarrier.{u} 18 :=
  snoc
    (snoc
      (snoc (validStageHistoryLAssignment history bound) index)
      stage)
      relation

 lemma validHistoryLocal_fixed
    (history bound index stage relation : LCarrier.{u}) (i : Fin 13) :
      validStageHistoryWitnessLAssignment history bound index stage relation
        (Fin.castLE (by decide) i) =
      stageHistoryStateLAssignment history index stage relation
        i.castSucc.castSucc.castSucc.castSucc := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [validStageHistoryWitnessLAssignment,
    validStageHistoryLAssignment, stageHistoryStateLAssignment,
    snoc_castSucc]

 lemma validHistoryLocal_history
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (13 : Fin 18) =
      stageHistoryStateLAssignment history index stage relation (13 : Fin 17) := by
  rfl

 lemma validHistoryWitnessAssignment_expanded_eq
    (history bound index stage relation : LCarrier.{u}) :
    snoc (snoc (snoc (validStageHistoryLAssignment history bound) index) stage)
        relation =
      validStageHistoryWitnessLAssignment history bound index stage relation := by
  rfl

@[simp]  lemma validHistoryWitness_history
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (13 : Fin 18) = history := by
  rw [show (13 : Fin 18) =
      (13 : Fin 15).castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [validStageHistoryWitnessLAssignment,
    validStageHistoryLAssignment, snoc_castSucc]
  rw [show (13 : Fin 15) = (Fin.last 13).castSucc by
    apply Fin.ext
    rfl]
  rw [snoc_castSucc]
  exact snoc_last _ _

@[simp]  lemma validHistoryWitness_index
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (15 : Fin 18) = index := by
  rw [show (15 : Fin 18) =
      (Fin.last 15).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [validStageHistoryWitnessLAssignment, snoc_castSucc]
  exact snoc_last _ _

@[simp]  lemma validHistoryWitness_stage
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (16 : Fin 18) = stage := by
  rw [show (16 : Fin 18) = (16 : Fin 17).castSucc by
    apply Fin.ext
    rfl]
  simp only [validStageHistoryWitnessLAssignment, snoc_castSucc]
  exact snoc_last _ _

@[simp]  lemma validHistoryWitness_relation
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (17 : Fin 18) = relation := by
  rw [show (17 : Fin 18) = Fin.last 17 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

/-- Select `(history, index, stage, relation)` from a global validity
witness assignment. -/
def validHistoryUniqueRename : Fin 4 → Fin 18 :=
  ![(13 : Fin 18), (15 : Fin 18), (16 : Fin 18), (17 : Fin 18)]

/-- Drop the bound coordinate from a global validity witness assignment,
obtaining the shared local-rule layout. -/
def validHistoryLocalRename : Fin 17 → Fin 18 :=
  Fin.lastCases
    (17 : Fin 18)
    (fun i15 => Fin.lastCases
      (16 : Fin 18)
      (fun i14 => Fin.lastCases
        (15 : Fin 18)
        (fun i13 => Fin.castLE (by decide) i13)
        i14)
      i15)

theorem comp_validHistoryUniqueRename
    (history bound index stage relation : LCarrier.{u}) :
    (fun i => validStageHistoryWitnessLAssignment
      history bound index stage relation (validHistoryUniqueRename i)) =
      ![history, index, stage, relation] := by
  funext i
  fin_cases i <;> rfl

theorem comp_validHistoryLocalRename
    (history bound index stage relation : LCarrier.{u}) :
    (fun i => validStageHistoryWitnessLAssignment
      history bound index stage relation (validHistoryLocalRename i)) =
      stageHistoryStateLAssignment history index stage relation := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · refine Fin.lastCases ?_ (fun j => ?_) i13
        · exact validHistoryLocal_history history bound index stage relation
        · simp only [validHistoryLocalRename, Fin.lastCases_castSucc]
          have hcast :
              (Fin.castLE (by decide) j.castSucc : Fin 18) =
                Fin.castLE (by decide) j := by
            apply Fin.ext
            rfl
          rw [hcast]
          exact validHistoryLocal_fixed history bound index stage relation j

@[simp]  lemma validStageHistoryAssignment_bound
    (history bound : LCarrier.{u}) :
    validStageHistoryLAssignment history bound (14 : Fin 15) = bound := by
  rw [show (14 : Fin 15) = Fin.last 14 by
    apply Fin.ext
    rfl]
  rw [validStageHistoryLAssignment]
  exact snoc_last _ _

@[simp]  lemma validStageHistoryWitness_bound
    (history bound index : LCarrier.{u}) :
    snoc (validStageHistoryLAssignment history bound) index (14 : Fin 16) =
      bound := by
  rw [show (14 : Fin 16) = (Fin.last 14).castSucc by
    apply Fin.ext
    rfl]
  rw [snoc_castSucc]
  exact validStageHistoryAssignment_bound history bound

@[simp]  lemma validStageHistoryWitness_index
    (history bound index : LCarrier.{u}) :
    snoc (validStageHistoryLAssignment history bound) index (15 : Fin 16) =
      index := by
  rw [show (15 : Fin 16) = Fin.last 15 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

/-- At the selected index there is a unique history state and that state
obeys the unified local recursion rule.  The layout before choosing the two
outputs is `(fixed13, history, bound, index)`. -/
def validStageHistoryIndexBody : FOFormula 16 :=
  .ex (.ex
    (.conj
      (historyEntryAt
        (13 : Fin 18) (15 : Fin 18) (16 : Fin 18) (17 : Fin 18))
      (.conj
        (FOFormula.rename validHistoryUniqueRename
          historyStateUniqueBody)
        (FOFormula.rename validHistoryLocalRename
          historyLocalStateFormula))))

/-- A history is total, functional, and locally correct at every index at
most the supplied bound. -/
def validStageHistoryFormula : FOFormula 15 :=
  FOFormula.all
    (FOFormula.imp
      (FOFormula.disj
        (.mem (15 : Fin 16) (14 : Fin 16))
        (.eq (15 : Fin 16) (14 : Fin 16)))
      validStageHistoryIndexBody)

/-- Exact semantics of the body at one bounded index. -/
theorem satisfies_validStageHistoryIndexBody
    (history bound index : LCarrier.{u}) :
    FOFormula.Satisfies LMem validStageHistoryIndexBody
        (snoc (validStageHistoryLAssignment history bound) index) ↔
      ∃ stage relation : LCarrier.{u},
        HistoryEntry history index stage relation ∧
        (∀ otherStage otherRelation : LCarrier.{u},
          HistoryEntry history index otherStage otherRelation →
            otherStage = stage ∧ otherRelation = relation) ∧
        HistoryLocalState history index stage relation := by
  simp only [validStageHistoryIndexBody, FOFormula.Satisfies,
    satisfies_historyEntryAt_iff, HistoryEntry,
    FOFormula.satisfies_rename,
    validHistoryWitnessAssignment_expanded_eq,
    comp_validHistoryUniqueRename, comp_validHistoryLocalRename,
    validHistoryWitness_history, validHistoryWitness_index,
    validHistoryWitness_stage, validHistoryWitness_relation,
    satisfies_historyStateUniqueBody, satisfies_historyLocalStateFormula]

/-- Exact `LCarrier` semantics of bounded valid-stage histories.  No
ordinalhood assumption on `bound` is hidden in this statement. -/
@[simp]
theorem satisfies_validStageHistoryFormula
    (history bound : LCarrier.{u}) :
    FOFormula.Satisfies LMem validStageHistoryFormula
        (validStageHistoryLAssignment history bound) ↔
      ∀ index : LCarrier.{u},
        (index.1 ∈ bound.1 ∨ index = bound) →
          ∃ stage relation : LCarrier.{u},
            HistoryEntry history index stage relation ∧
            (∀ otherStage otherRelation : LCarrier.{u},
              HistoryEntry history index otherStage otherRelation →
                otherStage = stage ∧ otherRelation = relation) ∧
            HistoryLocalState history index stage relation := by
  simp only [validStageHistoryFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_validStageHistoryIndexBody,
    validStageHistoryWitness_bound, validStageHistoryWitness_index]

/-- Named semantic predicate for a history which is total, functional, and
locally correct through `bound`. -/
def ValidStageHistory (history bound : LCarrier.{u}) : Prop :=
  ∀ index : LCarrier.{u},
    (index.1 ∈ bound.1 ∨ index = bound) →
      ∃ stage relation : LCarrier.{u},
        HistoryEntry history index stage relation ∧
        (∀ otherStage otherRelation : LCarrier.{u},
          HistoryEntry history index otherStage otherRelation →
            otherStage = stage ∧ otherRelation = relation) ∧
        HistoryLocalState history index stage relation

theorem satisfies_validStageHistoryFormula_iff
    (history bound : LCarrier.{u}) :
    FOFormula.Satisfies LMem validStageHistoryFormula
        (validStageHistoryLAssignment history bound) ↔
      ValidStageHistory history bound := by
  rw [satisfies_validStageHistoryFormula]
  rfl

end

end Constructible.Model
end CUAdapterModule87



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryOrdinal -/
section CUAdapterModule88
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Constructible ordinal indices for stage histories

Every ambient ordinal has a canonical von Neumann code in `L`.  Packaging
that code once keeps the history and Replacement interfaces on `LCarrier`.
-/


universe u

namespace Constructible.Model

noncomputable section

/-- The canonical constructible carrier element coding an ordinal. -/
def ordinalLCarrier (alpha : Ordinal.{u}) : LCarrier.{u} :=
  ⟨alpha.toZFSet, ordinal_toZFSet_mem_L alpha⟩

@[simp]
theorem ordinalLCarrier_val (alpha : Ordinal.{u}) :
    (ordinalLCarrier alpha).1 = alpha.toZFSet :=
  rfl

theorem ordinalLCarrier_mem_ordinalLCarrier_iff
    (alpha beta : Ordinal.{u}) :
    (ordinalLCarrier beta).1 ∈ (ordinalLCarrier alpha).1 ↔ beta < alpha := by
  exact Ordinal.toZFSet_mem_toZFSet_iff

@[simp]
theorem ordinalLCarrier_zero :
    ordinalLCarrier (0 : Ordinal.{u}) = emptyLCarrier := by
  apply Subtype.ext
  exact Ordinal.toZFSet_zero

theorem ordinalLCarrier_succ_val (alpha : Ordinal.{u}) :
    (ordinalLCarrier (Order.succ alpha)).1 =
      insert (ordinalLCarrier alpha).1 (ordinalLCarrier alpha).1 := by
  rw [Order.succ_eq_add_one]
  change (alpha + 1).toZFSet = insert alpha.toZFSet alpha.toZFSet
  exact Ordinal.toZFSet_add_one alpha

theorem ordinalLCarrier_injective :
    Function.Injective (ordinalLCarrier : Ordinal.{u} → LCarrier.{u}) := by
  intro alpha beta h
  have hcodes : alpha.toZFSet = beta.toZFSet :=
    congrArg Subtype.val h
  exact Ordinal.toZFSet_injective hcodes

/-- Von Neumann successor is injective on all well-founded `ZFSet`s. -/
theorem insert_self_injective {x y : ZFSet.{u}}
    (h : insert x x = insert y y) : x = y := by
  have hrankSucc : Order.succ x.rank = Order.succ y.rank := by
    have hrank := congrArg ZFSet.rank h
    simpa only [ZFSet.rank_insert, max_eq_left (Order.le_succ x.rank),
      max_eq_left (Order.le_succ y.rank)] using hrank
  have hrank : x.rank = y.rank :=
    Order.succ_injective hrankSucc
  have hx : x ∈ insert y y := by
    rw [← h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  rcases ZFSet.mem_insert_iff.mp hx with hxy | hxy
  · exact hxy
  · have hrankLt := ZFSet.rank_lt_of_mem hxy
    rw [hrank] at hrankLt
    exact (lt_irrefl _ hrankLt).elim

/-- The only predecessor whose von Neumann successor is the canonical code
of `alpha + 1` is the canonical code of `alpha`. -/
theorem ordinalLCarrier_successor_predecessor_iff
    (alpha : Ordinal.{u}) (predecessor : LCarrier.{u}) :
    (ordinalLCarrier (Order.succ alpha)).1 =
        insert predecessor.1 predecessor.1 ↔
      predecessor = ordinalLCarrier alpha := by
  constructor
  · intro h
    apply Subtype.ext
    apply insert_self_injective
    rw [← h, ordinalLCarrier_succ_val]
  · rintro rfl
    exact ordinalLCarrier_succ_val alpha

/-- A nonzero limit ordinal code is not the von Neumann successor of any
constructible set. -/
theorem ordinalLCarrier_limit_no_predecessor
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    ¬ ∃ predecessor : LCarrier.{u},
      (ordinalLCarrier limit).1 =
        insert predecessor.1 predecessor.1 := by
  rintro ⟨predecessor, hsuccessor⟩
  have hpredecessorMem : predecessor.1 ∈ limit.toZFSet := by
    rw [← ordinalLCarrier_val limit, hsuccessor]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  rcases Ordinal.mem_toZFSet_iff.mp hpredecessorMem with
    ⟨beta, _hbeta, hbetaCode⟩
  have hpredecessor : predecessor = ordinalLCarrier beta := by
    apply Subtype.ext
    exact hbetaCode.symm
  subst predecessor
  have hcodes : limit.toZFSet = (Order.succ beta).toZFSet := by
    calc
      limit.toZFSet = (ordinalLCarrier limit).1 := rfl
      _ = insert (ordinalLCarrier beta).1 (ordinalLCarrier beta).1 :=
        hsuccessor
      _ = (ordinalLCarrier (Order.succ beta)).1 :=
        (ordinalLCarrier_succ_val beta).symm
      _ = (Order.succ beta).toZFSet := rfl
  have hlimit : limit = Order.succ beta :=
    Ordinal.toZFSet_injective hcodes
  exact hl.succ_ne beta hlimit.symm

end

end Constructible.Model
end CUAdapterModule88



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageStateAtFormula -/
section CUAdapterModule89
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Fixed output formulas for constructible-stage recursion

The formulas in this file hide a valid history witness and expose the forms
needed by Replacement.  Their thirteen leading coordinates are always the
fixed evaluator parameters.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## A stage/relation state at one index -/

/-- Layout `(fixed13, index, stage, relation)`. -/
def stageStateAtLAssignment
    (index stage relation : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc (snoc stageHistoryFixedParameters index) stage) relation

/-- After adjoining the hidden history witness. -/
def stageStateAtWitnessLAssignment
    (index stage relation history : LCarrier.{u}) :
    Tuple LCarrier.{u} 17 :=
  snoc (stageStateAtLAssignment index stage relation) history

 lemma stageStateAtWitnessAssignment_expanded_eq
    (index stage relation history : LCarrier.{u}) :
    snoc (stageStateAtLAssignment index stage relation) history =
      stageStateAtWitnessLAssignment index stage relation history := by
  rfl

@[simp]  lemma stageStateAtWitness_index
    (index stage relation history : LCarrier.{u}) :
    stageStateAtWitnessLAssignment index stage relation history
        (13 : Fin 17) = index := by
  rw [show (13 : Fin 17) = (13 : Fin 16).castSucc by
    apply Fin.ext
    rfl]
  simp only [stageStateAtWitnessLAssignment, snoc_castSucc,
    stageStateAtLAssignment]
  exact snoc_last _ _

@[simp]  lemma stageStateAtWitness_stage
    (index stage relation history : LCarrier.{u}) :
    stageStateAtWitnessLAssignment index stage relation history
        (14 : Fin 17) = stage := by
  rw [show (14 : Fin 17) = (14 : Fin 16).castSucc by
    apply Fin.ext
    rfl]
  simp only [stageStateAtWitnessLAssignment, snoc_castSucc,
    stageStateAtLAssignment]
  exact snoc_last _ _

@[simp]  lemma stageStateAtWitness_relation
    (index stage relation history : LCarrier.{u}) :
    stageStateAtWitnessLAssignment index stage relation history
        (15 : Fin 17) = relation := by
  rw [show (15 : Fin 17) = (Fin.last 15).castSucc by
    apply Fin.ext
    rfl]
  simp only [stageStateAtWitnessLAssignment, snoc_castSucc,
    stageStateAtLAssignment]
  exact snoc_last _ _

@[simp]  lemma stageStateAtWitness_history
    (index stage relation history : LCarrier.{u}) :
    stageStateAtWitnessLAssignment index stage relation history
        (16 : Fin 17) = history := by
  rw [show (16 : Fin 17) = Fin.last 16 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

/-- Select `(fixed13, history, bound)` from the hidden-history layout. -/
def stageStateAtValidHistoryRename : Fin 15 → Fin 17 :=
  Fin.lastCases
    (13 : Fin 17)
    (fun i13 => Fin.lastCases
      (16 : Fin 17)
      (fun i12 => Fin.castLE (by decide) i12)
      i13)

 lemma stageStateAtValidHistory_fixed
    (index stage relation history : LCarrier.{u}) (i : Fin 13) :
    stageStateAtWitnessLAssignment index stage relation history
        i.castSucc.castSucc.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  simp only [stageStateAtWitnessLAssignment, stageStateAtLAssignment,
    snoc_castSucc]

 lemma stageStateAtValidHistory_fixed_castLE
    (index stage relation history : LCarrier.{u}) (i : Fin 13) :
    stageStateAtWitnessLAssignment index stage relation history
        (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  exact stageStateAtValidHistory_fixed index stage relation history i

 lemma stageStateAtValidHistoryRename_fixed (i : Fin 13) :
    stageStateAtValidHistoryRename i.castSucc.castSucc =
      Fin.castLE (by decide) i := by
  simp only [stageStateAtValidHistoryRename, Fin.lastCases_castSucc]

theorem comp_stageStateAtValidHistoryRename
    (index stage relation history : LCarrier.{u}) :
    (fun i => stageStateAtWitnessLAssignment index stage relation history
      (stageStateAtValidHistoryRename i)) =
      validStageHistoryLAssignment history index := by
  funext i
  refine Fin.lastCases ?_ (fun i13 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i12 => ?_) i13
    · rfl
    · rw [stageStateAtValidHistoryRename_fixed,
        stageStateAtValidHistory_fixed_castLE]
      simp only [validStageHistoryLAssignment, snoc_castSucc]

/-- There is a valid history through `index` containing the stated output. -/
def StageStateAt
    (index stage relation : LCarrier.{u}) : Prop :=
  ∃ history : LCarrier.{u},
    ValidStageHistory history index ∧
      HistoryEntry history index stage relation

/-- A fixed formula defining the pair of state outputs at one index. -/
def stageStateAtFormula : FOFormula 16 :=
  .ex (.conj
    (FOFormula.rename stageStateAtValidHistoryRename
      validStageHistoryFormula)
    (historyEntryAt
      (16 : Fin 17) (13 : Fin 17) (14 : Fin 17) (15 : Fin 17)))

@[simp]
theorem satisfies_stageStateAtFormula
    (index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageStateAtFormula
        (stageStateAtLAssignment index stage relation) ↔
      StageStateAt index stage relation := by
  simp only [stageStateAtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    stageStateAtWitnessAssignment_expanded_eq,
    comp_stageStateAtValidHistoryRename,
    satisfies_validStageHistoryFormula_iff,
    satisfies_historyEntryAt_iff, StageStateAt, HistoryEntry,
    stageStateAtWitness_index, stageStateAtWitness_stage,
    stageStateAtWitness_relation, stageStateAtWitness_history]

/-! ## A relation-only output for Replacement -/

/-- Layout `(fixed13, index, relation)`. -/
def stageRelationAtLAssignment
    (index relation : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters index) relation

 lemma stageRelationAt_fixed
    (index relation : LCarrier.{u}) (i : Fin 13) :
    stageRelationAtLAssignment index relation i.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  simp only [stageRelationAtLAssignment, snoc_castSucc]



 lemma stageRelationWitness_fixed_castLE
    (index relation stage : LCarrier.{u}) (i : Fin 13) :
    snoc (stageRelationAtLAssignment index relation) stage
        (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, stageRelationAt_fixed]

/-- Reorder the two output coordinates after binding the hidden stage. -/
def stageRelationAtRename : Fin 16 → Fin 16 :=
  Fin.lastCases
    (14 : Fin 16)
    (fun i14 => Fin.lastCases
      (15 : Fin 16)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

 lemma stageRelationAtRename_fixed (i : Fin 13) :
    stageRelationAtRename i.castSucc.castSucc.castSucc =
      Fin.castLE (by decide) i := by
  simp only [stageRelationAtRename, Fin.lastCases_castSucc]
  apply Fin.ext
  rfl

theorem comp_stageRelationAtRename
    (index relation stage : LCarrier.{u}) :
    (fun i => snoc (stageRelationAtLAssignment index relation) stage
      (stageRelationAtRename i)) =
      stageStateAtLAssignment index stage relation := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · rw [stageRelationAtRename_fixed,
          stageRelationWitness_fixed_castLE]
        simp only [stageStateAtLAssignment, snoc_castSucc]

/-- The relation coordinate of the unique state at an index. -/
def StageRelationAt (index relation : LCarrier.{u}) : Prop :=
  ∃ stage : LCarrier.{u}, StageStateAt index stage relation

/-- Replacement-ready formula whose input is `index` and output is the
relation graph. -/
def stageRelationAtFormula : FOFormula 15 :=
  .ex (FOFormula.rename stageRelationAtRename stageStateAtFormula)

@[simp]
theorem satisfies_stageRelationAtFormula
    (index relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageRelationAtFormula
        (stageRelationAtLAssignment index relation) ↔
      StageRelationAt index relation := by
  simp only [stageRelationAtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, comp_stageRelationAtRename,
    satisfies_stageStateAtFormula, StageRelationAt]

/-! ## A canonical triple output for Replacement -/

/-- Layout `(fixed13, index, entry)`. -/
def stageEntryAtLAssignment
    (index entry : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters index) entry

@[simp]  lemma stageEntryWitness_index
    (index entry stage relation : LCarrier.{u}) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (13 : Fin 17) = index := by
  rw [show (13 : Fin 17) = (13 : Fin 15).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, stageEntryAtLAssignment]
  rw [show (13 : Fin 15) = (Fin.last 13).castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, snoc_last]

@[simp]  lemma stageEntryWitness_entry
    (index entry stage relation : LCarrier.{u}) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (14 : Fin 17) = entry := by
  rw [show (14 : Fin 17) = (Fin.last 14).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, stageEntryAtLAssignment, snoc_last]

@[simp]  lemma stageEntryWitness_stage
    (index entry stage relation : LCarrier.{u}) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (15 : Fin 17) = stage := by
  rw [show (15 : Fin 17) = (Fin.last 15).castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, snoc_last]

@[simp]  lemma stageEntryWitness_relation
    (index entry stage relation : LCarrier.{u}) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (16 : Fin 17) = relation := by
  rw [show (16 : Fin 17) = Fin.last 16 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

 lemma stageEntryState_fixed
    (index entry stage relation : LCarrier.{u}) (i : Fin 13) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        i.castSucc.castSucc.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  simp only [stageEntryAtLAssignment, snoc_castSucc]

 lemma stageEntryState_fixed_castLE
    (index entry stage relation : LCarrier.{u}) (i : Fin 13) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  exact stageEntryState_fixed index entry stage relation i

/-- Select `(fixed13, index, stage, relation)` after binding both state
coordinates behind the entry output. -/
def stageEntryStateRename : Fin 16 → Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i14 => Fin.lastCases
      (15 : Fin 17)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

 lemma stageEntryStateRename_fixed (i : Fin 13) :
    stageEntryStateRename i.castSucc.castSucc.castSucc =
      Fin.castLE (by decide) i := by
  simp only [stageEntryStateRename, Fin.lastCases_castSucc]
  apply Fin.ext
  rfl

theorem comp_stageEntryStateRename
    (index entry stage relation : LCarrier.{u}) :
    (fun i => snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
      (stageEntryStateRename i)) =
      stageStateAtLAssignment index stage relation := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · rw [stageEntryStateRename_fixed,
          stageEntryState_fixed_castLE]
        simp only [stageStateAtLAssignment, snoc_castSucc]

/-- The canonical triple encoding a state at one index. -/
def StageEntryAt (index entry : LCarrier.{u}) : Prop :=
  ∃ stage relation : LCarrier.{u},
    StageStateAt index stage relation ∧
      entry.1 = Godel.triple index.1 stage.1 relation.1

/-- Replacement-ready formula whose output is the canonical history entry. -/
def stageEntryAtFormula : FOFormula 15 :=
  .ex (.ex (.conj
    (FOFormula.rename stageEntryStateRename stageStateAtFormula)
    (Delta0Formula.tripleEqAt
      (14 : Fin 17) (13 : Fin 17) (15 : Fin 17) (16 : Fin 17)).toFO))

@[simp]
theorem satisfies_stageEntryAtFormula
    (index entry : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageEntryAtFormula
        (stageEntryAtLAssignment index entry) ↔
      StageEntryAt index entry := by
  simp only [stageEntryAtFormula, FOFormula.Satisfies, StageEntryAt]
  apply exists_congr
  intro stage
  apply exists_congr
  intro relation
  rw [FOFormula.satisfies_rename, comp_stageEntryStateRename,
    satisfies_stageStateAtFormula]
  apply and_congr_right
  intro _hstate
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt]
  simp only [stageEntryWitness_entry, stageEntryWitness_index,
    stageEntryWitness_stage, stageEntryWitness_relation]

end

end Constructible.Model
end CUAdapterModule89



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryOperations -/
section CUAdapterModule90
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal operations on constructible stage histories

A history is an actual member of `L`, not an external Lean set.  This file
constructs the internal operation which adjoins one canonical triple and
records its exact lookup behavior.
-/


universe u

namespace Constructible.Model

noncomputable section

/-- The constructible singleton containing `x`. -/
def singletonLCarrier (x : LCarrier.{u}) : LCarrier.{u} :=
  pairLCarrier x x

@[simp]
theorem mem_singletonLCarrier_iff (x z : LCarrier.{u}) :
    z.1 ∈ (singletonLCarrier x).1 ↔ z = x := by
  simp only [singletonLCarrier, mem_pairLCarrier_iff, or_self]

/-- Binary union, constructed internally from Pairing and Union. -/
def unionLCarrier (x y : LCarrier.{u}) : LCarrier.{u} :=
  sUnionLCarrier (pairLCarrier x y)

@[simp]
theorem mem_unionLCarrier_iff (x y z : LCarrier.{u}) :
    z.1 ∈ (unionLCarrier x y).1 ↔ z.1 ∈ x.1 ∨ z.1 ∈ y.1 := by
  rw [unionLCarrier, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨member, hmember, hz⟩
    rcases (mem_pairLCarrier_iff x y member).mp hmember with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨x, (mem_pairLCarrier_iff x y x).mpr (Or.inl rfl), hz⟩
    · exact ⟨y, (mem_pairLCarrier_iff x y y).mpr (Or.inr rfl), hz⟩

/-- Adjoin the canonical code of one state to an internal history. -/
def addHistoryEntry
    (history index stage relation : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier history
    (singletonLCarrier (tripleLCarrier index stage relation))

@[simp]
theorem mem_addHistoryEntry_iff
    (history index stage relation entry : LCarrier.{u}) :
    entry.1 ∈ (addHistoryEntry history index stage relation).1 ↔
      entry.1 ∈ history.1 ∨
        entry = tripleLCarrier index stage relation := by
  simp only [addHistoryEntry, mem_unionLCarrier_iff,
    mem_singletonLCarrier_iff]

/-- Looking up an extended history either finds an old state or exactly the
newly adjoined state. -/
@[simp]
theorem historyEntry_addHistoryEntry_iff
    (history index stage relation queryIndex queryStage queryRelation :
      LCarrier.{u}) :
    HistoryEntry (addHistoryEntry history index stage relation)
        queryIndex queryStage queryRelation ↔
      HistoryEntry history queryIndex queryStage queryRelation ∨
        (queryIndex = index ∧ queryStage = stage ∧
          queryRelation = relation) := by
  change
    Godel.triple queryIndex.1 queryStage.1 queryRelation.1 ∈
        (addHistoryEntry history index stage relation).1 ↔ _
  let queryEntry := tripleLCarrier queryIndex queryStage queryRelation
  have hquery :
      queryEntry.1 =
        Godel.triple queryIndex.1 queryStage.1 queryRelation.1 :=
    tripleLCarrier_val queryIndex queryStage queryRelation
  rw [← hquery, mem_addHistoryEntry_iff]
  constructor
  · rintro (hold | hnew)
    · exact Or.inl hold
    · right
      have hcoordinates := triple_injective
        (congrArg Subtype.val hnew)
      exact
        ⟨Subtype.ext hcoordinates.1,
          Subtype.ext hcoordinates.2.1,
          Subtype.ext hcoordinates.2.2⟩
  · rintro (hold | ⟨rfl, rfl, rfl⟩)
    · exact Or.inl hold
    · exact Or.inr rfl

end

end Constructible.Model
end CUAdapterModule90



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryReplacement -/
section CUAdapterModule91
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal replacement families for constructible-stage recursion

Assuming that every earlier ordinal index has a unique stage/relation state,
the fixed formulas from `StageStateAtFormula` turn the earlier history entries
and relation graphs into actual members of `L` by Replacement.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- Unique stage/relation outputs at every ordinal strictly below `bound`. -/
def UniqueStageStatesBelow (bound : Ordinal.{u}) : Prop :=
  ∀ index < bound,
    ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt (ordinalLCarrier index) output.1 output.2

/-- Every member of a von Neumann ordinal code is the canonical code of a
unique smaller ordinal. -/
theorem exists_eq_ordinalLCarrier_of_mem
    {bound : Ordinal.{u}} {index : LCarrier.{u}}
    (hindex : index.1 ∈ (ordinalLCarrier bound).1) :
    ∃ ordinal < bound, index = ordinalLCarrier ordinal := by
  have hraw : index.1 ∈ bound.toZFSet := by
    simpa only [ordinalLCarrier_val] using hindex
  rcases Ordinal.mem_toZFSet_iff.mp hraw with
    ⟨ordinal, hordinal, hcode⟩
  refine ⟨ordinal, hordinal, ?_⟩
  apply Subtype.ext
  exact hcode.symm

/-- Uniqueness of the state pair gives uniqueness of its canonical triple. -/
theorem existsUnique_stageEntryAt_of_uniqueState
    (index : LCarrier.{u})
    (hstate : ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt index output.1 output.2) :
    ∃! entry : LCarrier.{u}, StageEntryAt index entry := by
  rcases hstate with ⟨⟨stage, relation⟩, hstate, hunique⟩
  let entry := tripleLCarrier index stage relation
  refine ⟨entry, ?_, ?_⟩
  · exact ⟨stage, relation, hstate,
      tripleLCarrier_val index stage relation⟩
  · intro other hother
    rcases hother with ⟨otherStage, otherRelation,
      hotherState, hotherCode⟩
    have houtputs :
        (otherStage, otherRelation) = (stage, relation) :=
      hunique (otherStage, otherRelation) hotherState
    have hstage : otherStage = stage := congrArg Prod.fst houtputs
    have hrelation : otherRelation = relation :=
      congrArg Prod.snd houtputs
    subst otherStage
    subst otherRelation
    apply Subtype.ext
    exact hotherCode.trans
      (tripleLCarrier_val index stage relation).symm

/-- Uniqueness of the state pair also gives a unique relation coordinate. -/
theorem existsUnique_stageRelationAt_of_uniqueState
    (index : LCarrier.{u})
    (hstate : ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt index output.1 output.2) :
    ∃! relation : LCarrier.{u}, StageRelationAt index relation := by
  rcases hstate with ⟨⟨stage, relation⟩, hstate, hunique⟩
  refine ⟨relation, ⟨stage, hstate⟩, ?_⟩
  intro otherRelation hother
  rcases hother with ⟨otherStage, hotherState⟩
  have houtputs :
      (otherStage, otherRelation) = (stage, relation) :=
    hunique (otherStage, otherRelation) hotherState
  exact congrArg Prod.snd houtputs

/-- Replacement constructs the internal set of all canonical history entries
strictly below `bound`. -/
theorem exists_stageEntryFamily
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound) :
    ∃ history : LCarrier.{u}, ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageEntryAt index entry := by
  have hfun : ∀ index : LCarrier.{u},
      index.1 ∈ (ordinalLCarrier bound).1 →
        ∃! entry : LCarrier.{u},
          FOFormula.Satisfies LMem stageEntryAtFormula
            (snoc (snoc stageHistoryFixedParameters index) entry) := by
    intro index hindex
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    rcases existsUnique_stageEntryAt_of_uniqueState
      (ordinalLCarrier ordinal) (hstates ordinal hordinal)
      with ⟨entry, hentry, hunique⟩
    refine ⟨entry, ?_, ?_⟩
    · change FOFormula.Satisfies LMem stageEntryAtFormula
        (stageEntryAtLAssignment (ordinalLCarrier ordinal) entry)
      exact (satisfies_stageEntryAtFormula
        (ordinalLCarrier ordinal) entry).mpr hentry
    · intro other hother
      apply hunique other
      apply (satisfies_stageEntryAtFormula
        (ordinalLCarrier ordinal) other).mp
      exact hother
  rcases exists_replacementLCarrier stageEntryAtFormula
      stageHistoryFixedParameters (ordinalLCarrier bound) hfun with
    ⟨history, hhistory⟩
  refine ⟨history, ?_⟩
  intro entry
  rw [hhistory]
  apply exists_congr
  intro index
  apply and_congr_right
  intro _hindex
  exact satisfies_stageEntryAtFormula index entry

/-- Replacement constructs the internal family of all relation graphs
strictly below `bound`. -/
theorem exists_stageRelationFamily
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound) :
    ∃ family : LCarrier.{u}, ∀ relation : LCarrier.{u},
      relation.1 ∈ family.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageRelationAt index relation := by
  have hfun : ∀ index : LCarrier.{u},
      index.1 ∈ (ordinalLCarrier bound).1 →
        ∃! relation : LCarrier.{u},
          FOFormula.Satisfies LMem stageRelationAtFormula
            (snoc (snoc stageHistoryFixedParameters index) relation) := by
    intro index hindex
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    rcases existsUnique_stageRelationAt_of_uniqueState
      (ordinalLCarrier ordinal) (hstates ordinal hordinal)
      with ⟨relation, hrelation, hunique⟩
    refine ⟨relation, ?_, ?_⟩
    · change FOFormula.Satisfies LMem stageRelationAtFormula
        (stageRelationAtLAssignment (ordinalLCarrier ordinal) relation)
      exact (satisfies_stageRelationAtFormula
        (ordinalLCarrier ordinal) relation).mpr hrelation
    · intro other hother
      apply hunique other
      apply (satisfies_stageRelationAtFormula
        (ordinalLCarrier ordinal) other).mp
      exact hother
  rcases exists_replacementLCarrier stageRelationAtFormula
      stageHistoryFixedParameters (ordinalLCarrier bound) hfun with
    ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro relation
  rw [hfamily]
  apply exists_congr
  intro index
  apply and_congr_right
  intro _hindex
  exact satisfies_stageRelationAtFormula index relation

/-- A chosen internal history containing exactly the earlier canonical
entries.  Its specification, not the metatheoretic choice of witness, is the
public interface. -/
noncomputable def stageEntryFamily
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound) :
    LCarrier.{u} :=
  Classical.choose (exists_stageEntryFamily bound hstates)

@[simp]
theorem mem_stageEntryFamily_iff
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound)
    (entry : LCarrier.{u}) :
    entry.1 ∈ (stageEntryFamily bound hstates).1 ↔
      ∃ index : LCarrier.{u},
        index.1 ∈ (ordinalLCarrier bound).1 ∧
          StageEntryAt index entry :=
  Classical.choose_spec (exists_stageEntryFamily bound hstates) entry

/-- A chosen internal set containing exactly the earlier relation outputs. -/
noncomputable def stageRelationFamily
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound) :
    LCarrier.{u} :=
  Classical.choose (exists_stageRelationFamily bound hstates)

@[simp]
theorem mem_stageRelationFamily_iff
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound)
    (relation : LCarrier.{u}) :
    relation.1 ∈ (stageRelationFamily bound hstates).1 ↔
      ∃ index : LCarrier.{u},
        index.1 ∈ (ordinalLCarrier bound).1 ∧
          StageRelationAt index relation :=
  Classical.choose_spec (exists_stageRelationFamily bound hstates) relation

/-- Exact lookup semantics of a Replacement-generated history.  In
particular, the internal history contains no entries at or above `bound`. -/
theorem historyEntry_iff_of_stageEntryFamily
    {bound : Ordinal.{u}} {history : LCarrier.{u}}
    (hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageEntryAt index entry)
    (index stage relation : LCarrier.{u}) :
    HistoryEntry history index stage relation ↔
      index.1 ∈ (ordinalLCarrier bound).1 ∧
        StageStateAt index stage relation := by
  let entry := tripleLCarrier index stage relation
  have hentry :
      entry.1 = Godel.triple index.1 stage.1 relation.1 :=
    tripleLCarrier_val index stage relation
  constructor
  · intro hlookup
    have hmem : entry.1 ∈ history.1 := by
      rw [hentry]
      exact hlookup
    rcases (hhistory entry).mp hmem with
      ⟨otherIndex, hotherIndex, otherStage, otherRelation,
        hotherState, hotherCode⟩
    have hcodes :
        Godel.triple index.1 stage.1 relation.1 =
          Godel.triple otherIndex.1 otherStage.1 otherRelation.1 :=
      hentry.symm.trans hotherCode
    have hcoordinates := triple_injective hcodes
    have hindex : index = otherIndex := Subtype.ext hcoordinates.1
    have hstage : stage = otherStage :=
      Subtype.ext hcoordinates.2.1
    have hrelation : relation = otherRelation :=
      Subtype.ext hcoordinates.2.2
    subst otherIndex
    subst otherStage
    subst otherRelation
    exact ⟨hotherIndex, hotherState⟩
  · rintro ⟨hindex, hstate⟩
    have hmem : entry.1 ∈ history.1 := (hhistory entry).mpr
      ⟨index, hindex, stage, relation, hstate, hentry⟩
    change Godel.triple index.1 stage.1 relation.1 ∈ history.1
    rw [← hentry]
    exact hmem

/-- Appending the top state to a Replacement-generated history gives an
exact old-or-top lookup split. -/
theorem historyEntry_addTop_iff_of_stageEntryFamily
    {bound : Ordinal.{u}} {history : LCarrier.{u}}
    (hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageEntryAt index entry)
    (topStage topRelation index stage relation : LCarrier.{u}) :
    HistoryEntry
        (addHistoryEntry history (ordinalLCarrier bound)
          topStage topRelation)
        index stage relation ↔
      (index.1 ∈ (ordinalLCarrier bound).1 ∧
        StageStateAt index stage relation) ∨
      (index = ordinalLCarrier bound ∧ stage = topStage ∧
        relation = topRelation) := by
  rw [historyEntry_addHistoryEntry_iff,
    historyEntry_iff_of_stageEntryFamily hhistory]

end

end Constructible.Model
end CUAdapterModule91


