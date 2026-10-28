-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library02
-- name    : CH_ConstructibleGCH_Library02
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:06:44.611561+00:00
-- url     : https://prove2.me/theorems/c4a8831a-2fbc-40e9-b3c9-6b691bc05939
-- title:
--   Bare stage histories and the selected V=L predicate
-- statement:
--   A bare stage history records the constructible stages below an ordinal using set-coded entries. This library supplies the history data and the fixed first-order predicates used to recognize constructible stages and the selected V=L history specification.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/BareStageHistory.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/VEqualsL.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library01
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_BareStageHistory -/
section GCHSource_Work_CUGCH_BareStageHistory
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Relation-free histories for the constructible hierarchy

This file is a proof tool; it does not define a different constructible
hierarchy.  In ordinary set-theoretic language, a bare history through an
ordinal `a` is a set-coded partial function `h` whose value at every
`i <= a` is a set `S_i`, with

* `S_0 = empty`;
* `S_(i+1) = Def(S_i)`;
* `S_l = union (i < l) S_i` when `l` is a nonzero limit ordinal.

The Lean representation uses Kuratowski pairs: `BareHistoryEntry h i s`
means exactly that `<i,s>` belongs to the internal `ZFSet` underlying `h`.
Unlike `ValidStageHistory`, no canonical well-order relation is stored in an
entry or mentioned by the local recursion rule.

The formula interfaces below use the exact quantifiers displayed by the
semantic predicates.  They still reuse `godelDefOutputFormula` at successor
steps, so their first thirteen coordinates are the existing evaluator
parameters `(varTag, appTag, empty, op0, ..., op8, omega)`.  Consequently this
file, by itself, does not assert that those parameters belong to `L_omega`,
nor does it claim absoluteness in every limit level.  The special `L_omega`
case must be handled separately before this tool can support the unrestricted
Condensation Lemma.
-/

section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Pair-coded history entries -/

/-- In an arbitrary context, the selected history contains the Kuratowski
pair made from the selected index and stage. -/
def bareHistoryEntryAt {n : Nat}
    (history index stage : Fin n) : FOFormula n :=
  .ex (.conj
    (.mem (Fin.last n) history.castSucc)
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) index.castSucc stage.castSucc).toFO)

/-- Free-variable layout `(history, index, stage)`. -/
def bareHistoryEntryFormula : FOFormula 3 :=
  bareHistoryEntryAt (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)

/-- A direct assignment for the three exposed entry coordinates. -/
def bareHistoryEntryAssignment
    (history index stage : LCarrier.{u}) : Tuple LCarrier.{u} 3 :=
  ![history, index, stage]

/-- The ordinary mathematical meaning of a bare history entry. -/
def BareHistoryEntry
    (history index stage : LCarrier.{u}) : Prop :=
  ZFSet.pair index.1 stage.1 ∈ history.1

@[simp]
theorem satisfies_bareHistoryEntryAt_components {n : Nat}
    (history index stage : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (bareHistoryEntryAt history index stage) s ↔
      ∃ entry : LCarrier.{u},
        entry.1 ∈ (s history).1 ∧
        entry.1 = ZFSet.pair (s index).1 (s stage).1 := by
  simp only [bareHistoryEntryAt, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _hentry
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  simp only [snoc_last, snoc_castSucc]

@[simp]
theorem satisfies_bareHistoryEntryAt_iff {n : Nat}
    (history index stage : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (bareHistoryEntryAt history index stage) s ↔
      ZFSet.pair (s index).1 (s stage).1 ∈ (s history).1 := by
  rw [satisfies_bareHistoryEntryAt_components]
  constructor
  · rintro ⟨entry, hentry, heq⟩
    simpa only [heq] using hentry
  · intro hentry
    exact
      ⟨orderedPairLCarrier (s index) (s stage),
        by simpa only [orderedPairLCarrier_val] using hentry,
        orderedPairLCarrier_val (s index) (s stage)⟩

@[simp]
theorem satisfies_bareHistoryEntryFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryEntryFormula
        (bareHistoryEntryAssignment history index stage) ↔
      BareHistoryEntry history index stage := by
  rw [bareHistoryEntryFormula,
    satisfies_bareHistoryEntryAt_iff]
  rfl

/-! ## The exact zero, successor, and limit clauses -/

/-- Layout `(fixed13, history, index, stage)`. -/
def bareHistoryStateLAssignment
    (history index stage : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc (snoc stageHistoryFixedParameters history) index) stage

/-- Select `(history,index,stage)` from the shared local-state layout. -/
def bareHistoryStateRename : Fin 3 → Fin 16 :=
  ![13, 14, 15]

theorem comp_bareHistoryStateRename
    (history index stage : LCarrier.{u}) :
    (fun i => bareHistoryStateLAssignment history index stage
      (bareHistoryStateRename i)) =
      bareHistoryEntryAssignment history index stage := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem bareHistoryStateLAssignment_history
    (history index stage : LCarrier.{u}) :
    bareHistoryStateLAssignment history index stage (13 : Fin 16) =
      history := by
  rfl

@[simp] theorem bareHistoryStateLAssignment_index
    (history index stage : LCarrier.{u}) :
    bareHistoryStateLAssignment history index stage (14 : Fin 16) =
      index := by
  rfl

@[simp] theorem bareHistoryStateLAssignment_stage
    (history index stage : LCarrier.{u}) :
    bareHistoryStateLAssignment history index stage (15 : Fin 16) =
      stage := by
  rfl

@[simp] theorem bareHistoryStateLAssignment_empty
    (history index stage : LCarrier.{u}) :
    bareHistoryStateLAssignment history index stage (2 : Fin 16) =
      emptyLCarrier := by
  change stageHistoryFixedParameters (2 : Fin 13) = emptyLCarrier
  exact stageHistoryFixedParameters_empty

/-- The local rule at index zero.  Coordinate `2` of the fixed prefix is the
canonical empty set. -/
def bareHistoryBaseStateFormula : FOFormula 16 :=
  .conj
    (.eq (14 : Fin 16) (2 : Fin 16))
    (.eq (15 : Fin 16) (2 : Fin 16))

@[simp]
theorem satisfies_bareHistoryBaseStateFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryBaseStateFormula
        (bareHistoryStateLAssignment history index stage) ↔
      index = emptyLCarrier ∧ stage = emptyLCarrier := by
  simp only [bareHistoryBaseStateFormula, FOFormula.Satisfies,
    bareHistoryStateLAssignment_index,
    bareHistoryStateLAssignment_stage,
    bareHistoryStateLAssignment_empty]

/-- After the two successor witnesses the layout is
`(fixed13, history, index, stage, predecessorIndex, predecessorStage)`.
This permutation selects the existing output-formula layout
`(predecessorStage, fixed13, stage)`. -/
def bareHistorySuccessorDefRename : Fin 15 → Fin 18 :=
  Fin.lastCases
    (15 : Fin 18)
    (fun i14 => Fin.cases
      (17 : Fin 18)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

/-- Assignment after adjoining the predecessor index and predecessor stage. -/
def bareHistorySuccessorWitnessAssignment
    (history index stage predecessorIndex predecessorStage : LCarrier.{u}) :
    Tuple LCarrier.{u} 18 :=
  snoc (snoc (bareHistoryStateLAssignment history index stage)
    predecessorIndex) predecessorStage

 theorem bareHistorySuccessorDefRename_fixed (k : Fin 12) :
    bareHistorySuccessorDefRename k.castSucc.succ.castSucc =
      Fin.castLE (by decide) k.castSucc := by
  unfold bareHistorySuccessorDefRename
  rw [Fin.lastCases_castSucc, Fin.cases_succ]

theorem comp_bareHistorySuccessorDefRename
    (history index stage predecessorIndex predecessorStage : LCarrier.{u}) :
    (fun i => bareHistorySuccessorWitnessAssignment history index stage
      predecessorIndex predecessorStage
      (bareHistorySuccessorDefRename i)) =
      Godel.RudimentaryTerm.godelDefOutputLAssignment
        predecessorStage stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · change stage = stage
    rfl
  · refine Fin.cases ?_ (fun i13 => ?_) i14
    · change predecessorStage = predecessorStage
      rfl
    · refine Fin.lastCases ?_ (fun k => ?_) i13
      · change stageHistoryFixedParameters (Fin.last 12) =
          (⟨Ordinal.omega0.toZFSet, omega_mem_L⟩ : LCarrier.{u})
        exact stageHistoryFixedParameters_last
      · rw [bareHistorySuccessorDefRename_fixed]
        rw [show Fin.castLE (by decide) k.castSucc =
            k.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc by
          apply Fin.ext
          rfl]
        rw [show k.castSucc.succ.castSucc =
            k.succ.castSucc.castSucc by
          apply Fin.ext
          rfl]
        simp only [bareHistorySuccessorWitnessAssignment,
          bareHistoryStateLAssignment,
          Godel.RudimentaryTerm.godelDefOutputLAssignment,
          snoc_castSucc]
        exact stageHistoryFixedParameters_init predecessorStage k

/-- The local successor clause: the previous entry exists and the new stage
is exactly `godelDef` of its stage coordinate. -/
def bareHistorySuccessorStateFormula : FOFormula 16 :=
  .ex (.ex
    (.conj
      (Delta0Formula.successorFOAt (14 : Fin 18) (16 : Fin 18))
      (.conj
        (bareHistoryEntryAt
          (13 : Fin 18) (16 : Fin 18) (17 : Fin 18))
        (FOFormula.rename bareHistorySuccessorDefRename
          Godel.RudimentaryTerm.godelDefOutputFormula))))

@[simp]
theorem satisfies_bareHistorySuccessorStateFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistorySuccessorStateFormula
        (bareHistoryStateLAssignment history index stage) ↔
      ∃ predecessorIndex predecessorStage : LCarrier.{u},
        index.1 = insert predecessorIndex.1 predecessorIndex.1 ∧
        BareHistoryEntry history predecessorIndex predecessorStage ∧
        stage.1 = Godel.godelDef predecessorStage.1 := by
  simp only [bareHistorySuccessorStateFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    satisfies_bareHistoryEntryAt_iff, BareHistoryEntry,
    FOFormula.satisfies_rename]
  apply exists_congr
  intro predecessorIndex
  apply exists_congr
  intro predecessorStage
  rw [show
    snoc (snoc (bareHistoryStateLAssignment history index stage)
      predecessorIndex) predecessorStage =
        bareHistorySuccessorWitnessAssignment history index stage
          predecessorIndex predecessorStage by rfl]
  rw [comp_bareHistorySuccessorDefRename,
    Godel.RudimentaryTerm.satisfies_godelDefOutputFormula_iff]
  rfl

/-- Free-variable layout `(history,index,stage)`.  At a limit index, `stage`
is the union of all earlier stage values. -/
def bareHistoryLimitStateFormula : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (3 : Fin 4) (2 : Fin 4))
      (FOFormula.boundedEx (1 : Fin 4)
        (.ex
          (.conj
            (bareHistoryEntryAt
              (0 : Fin 6) (4 : Fin 6) (5 : Fin 6))
            (.mem (3 : Fin 6) (5 : Fin 6))))))

/-- Exact external meaning of the limit-union clause. -/
def BareHistoryLimitState
    (history index stage : LCarrier.{u}) : Prop :=
  ∀ z : LCarrier.{u}, z.1 ∈ stage.1 ↔
    ∃ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 ∧
      ∃ earlierStage : LCarrier.{u},
        BareHistoryEntry history earlierIndex earlierStage ∧
        z.1 ∈ earlierStage.1

@[simp]
theorem satisfies_bareHistoryLimitStateFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryLimitStateFormula
        (bareHistoryEntryAssignment history index stage) ↔
      BareHistoryLimitState history index stage := by
  simp only [bareHistoryLimitStateFormula, BareHistoryLimitState,
    bareHistoryEntryAssignment, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies, satisfies_bareHistoryEntryAt_iff,
    BareHistoryEntry]
  rfl

/-- The current index is the empty set. -/
def bareHistoryIndexIsZeroFormula : FOFormula 16 :=
  .eq (14 : Fin 16) (2 : Fin 16)

/-- The current index is a von Neumann successor. -/
def bareHistoryIndexHasPredecessorFormula : FOFormula 16 :=
  .ex (Delta0Formula.successorFOAt (14 : Fin 17) (16 : Fin 17))

@[simp]
theorem satisfies_bareHistoryIndexIsZeroFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryIndexIsZeroFormula
        (bareHistoryStateLAssignment history index stage) ↔
      index = emptyLCarrier := by
  simp only [bareHistoryIndexIsZeroFormula, FOFormula.Satisfies,
    bareHistoryStateLAssignment_index,
    bareHistoryStateLAssignment_empty]

@[simp]
theorem satisfies_bareHistoryIndexHasPredecessorFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryIndexHasPredecessorFormula
        (bareHistoryStateLAssignment history index stage) ↔
      ∃ predecessor : LCarrier.{u},
        index.1 = insert predecessor.1 predecessor.1 := by
  simp only [bareHistoryIndexHasPredecessorFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier]
  apply exists_congr
  intro predecessor
  change (index.1 = insert predecessor.1 predecessor.1) ↔ _
  rfl

/-- The ordinary three-way recursion rule, with no order-relation output. -/
def BareHistoryLocalState
    (history index stage : LCarrier.{u}) : Prop :=
  (index = emptyLCarrier ∧ stage = emptyLCarrier) ∨
  (∃ predecessorIndex predecessorStage : LCarrier.{u},
    index.1 = insert predecessorIndex.1 predecessorIndex.1 ∧
    BareHistoryEntry history predecessorIndex predecessorStage ∧
    stage.1 = Godel.godelDef predecessorStage.1) ∨
  (index ≠ emptyLCarrier ∧
    ¬ ∃ predecessor : LCarrier.{u},
      index.1 = insert predecessor.1 predecessor.1) ∧
    BareHistoryLimitState history index stage

/-- Formula for the ordinary three-way recursion rule. -/
def bareHistoryLocalStateFormula : FOFormula 16 :=
  .disj
    bareHistoryBaseStateFormula
    (.disj
      bareHistorySuccessorStateFormula
      (.conj
        (.conj
          (.neg bareHistoryIndexIsZeroFormula)
          (.neg bareHistoryIndexHasPredecessorFormula))
        (FOFormula.rename bareHistoryStateRename
          bareHistoryLimitStateFormula)))

@[simp]
theorem satisfies_bareHistoryLocalStateFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryLocalStateFormula
        (bareHistoryStateLAssignment history index stage) ↔
      BareHistoryLocalState history index stage := by
  simp only [bareHistoryLocalStateFormula, BareHistoryLocalState,
    FOFormula.satisfies_disj, FOFormula.Satisfies,
    satisfies_bareHistoryBaseStateFormula,
    satisfies_bareHistorySuccessorStateFormula,
    satisfies_bareHistoryIndexIsZeroFormula,
    satisfies_bareHistoryIndexHasPredecessorFormula,
    FOFormula.satisfies_rename, comp_bareHistoryStateRename,
    satisfies_bareHistoryLimitStateFormula]

/-! ## Bounded total functional histories -/

/-- Layout `(fixed13,history,bound)`. -/
def bareValidStageHistoryLAssignment
    (history bound : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters history) bound

/-- Select `(fixed13,history,index,stage)` after the index and stage witnesses
have been appended to `(fixed13,history,bound)`. -/
def bareValidHistoryLocalRename : Fin 16 → Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i15 => Fin.lastCases
      (15 : Fin 17)
      (fun i14 => Fin.lastCases
        (13 : Fin 17)
        (fun i13 => Fin.castLE (by decide) i13)
        i14)
      i15)

 theorem bareValidHistoryLocalRename_fixed (i : Fin 13) :
    bareValidHistoryLocalRename i.castSucc.castSucc.castSucc =
      Fin.castLE (by decide) i := by
  simp [bareValidHistoryLocalRename]

/-- At one selected index there is one unique stage, and it obeys the local
recursion rule.  Before choosing the stage, the layout is
`(fixed13,history,bound,index)`. -/
def bareValidStageHistoryIndexBody : FOFormula 16 :=
  .ex
    (.conj
      (bareHistoryEntryAt
        (13 : Fin 17) (15 : Fin 17) (16 : Fin 17))
      (.conj
        (FOFormula.all
          (FOFormula.imp
            (bareHistoryEntryAt
              (13 : Fin 18) (15 : Fin 18) (17 : Fin 18))
            (.eq (17 : Fin 18) (16 : Fin 18))))
        (FOFormula.rename bareValidHistoryLocalRename
          bareHistoryLocalStateFormula)))

/-- A history is total, stage-functional, and locally correct through the
supplied bound.  Extra members not encoding entries are harmless. -/
def bareValidStageHistoryFormula : FOFormula 15 :=
  FOFormula.all
    (FOFormula.imp
      (FOFormula.disj
        (.mem (15 : Fin 16) (14 : Fin 16))
        (.eq (15 : Fin 16) (14 : Fin 16)))
      bareValidStageHistoryIndexBody)

/-- Exact external predicate expressed by `bareValidStageHistoryFormula`. -/
def BareValidStageHistory (history bound : LCarrier.{u}) : Prop :=
  ∀ index : LCarrier.{u},
    (index.1 ∈ bound.1 ∨ index = bound) →
      ∃ stage : LCarrier.{u},
        BareHistoryEntry history index stage ∧
        (∀ otherStage : LCarrier.{u},
          BareHistoryEntry history index otherStage →
            otherStage = stage) ∧
        BareHistoryLocalState history index stage

 theorem comp_bareValidHistoryLocalRename
    (history bound index stage : LCarrier.{u}) :
    (fun i =>
      snoc (snoc (bareValidStageHistoryLAssignment history bound) index)
        stage (bareValidHistoryLocalRename i)) =
      bareHistoryStateLAssignment history index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · change stage = stage
    rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · change index = index
      rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · change history = history
        rfl
      · rw [bareValidHistoryLocalRename_fixed]
        rw [show Fin.castLE (by decide) i13 =
            i13.castSucc.castSucc.castSucc.castSucc by
          apply Fin.ext
          rfl]
        simp only [bareValidStageHistoryLAssignment,
          bareHistoryStateLAssignment, snoc_castSucc]

@[simp]
theorem satisfies_bareValidStageHistoryIndexBody
    (history bound index : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareValidStageHistoryIndexBody
        (snoc (bareValidStageHistoryLAssignment history bound) index) ↔
      ∃ stage : LCarrier.{u},
        BareHistoryEntry history index stage ∧
        (∀ otherStage : LCarrier.{u},
          BareHistoryEntry history index otherStage →
            otherStage = stage) ∧
        BareHistoryLocalState history index stage := by
  simp only [bareValidStageHistoryIndexBody, FOFormula.Satisfies,
    satisfies_bareHistoryEntryAt_iff, BareHistoryEntry,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_rename]
  apply exists_congr
  intro stage
  rw [comp_bareValidHistoryLocalRename,
    satisfies_bareHistoryLocalStateFormula]
  rfl

@[simp]
theorem satisfies_bareValidStageHistoryFormula
    (history bound : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareValidStageHistoryFormula
        (bareValidStageHistoryLAssignment history bound) ↔
      BareValidStageHistory history bound := by
  simp only [bareValidStageHistoryFormula, BareValidStageHistory,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_disj, FOFormula.Satisfies]
  apply forall_congr'
  intro index
  change
    ((index.1 ∈ bound.1 ∨ index = bound) →
      FOFormula.Satisfies LMem bareValidStageHistoryIndexBody
        (snoc (bareValidStageHistoryLAssignment history bound) index)) ↔ _
  rw [satisfies_bareValidStageHistoryIndexBody]

/-! ## A history-independent stage-output formula -/

/-- Layout `(fixed13,index,stage)`. -/
def bareStageAtLAssignment
    (index stage : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters index) stage

/-- Select `(fixed13,history,bound=index)` after binding a hidden history. -/
def bareStageAtValidHistoryRename : Fin 15 → Fin 16 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 13]

/-- There is a valid bare history through `index` with the stated stage at
its top entry. -/
def BareStageAt (index stage : LCarrier.{u}) : Prop :=
  ∃ history : LCarrier.{u},
    BareValidStageHistory history index ∧
    BareHistoryEntry history index stage

/-- Formula exposing only an index and its constructible-stage output. -/
def bareStageAtFormula : FOFormula 15 :=
  .ex
    (.conj
      (FOFormula.rename bareStageAtValidHistoryRename
        bareValidStageHistoryFormula)
      (bareHistoryEntryAt
        (15 : Fin 16) (13 : Fin 16) (14 : Fin 16)))

 theorem comp_bareStageAtValidHistoryRename
    (index stage history : LCarrier.{u}) :
    (fun i => snoc (bareStageAtLAssignment index stage) history
      (bareStageAtValidHistoryRename i)) =
      bareValidStageHistoryLAssignment history index := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_bareStageAtFormula
    (index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareStageAtFormula
        (bareStageAtLAssignment index stage) ↔
      BareStageAt index stage := by
  simp only [bareStageAtFormula, BareStageAt, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  apply exists_congr
  intro history
  rw [comp_bareStageAtValidHistoryRename,
    satisfies_bareValidStageHistoryFormula,
    satisfies_bareHistoryEntryAt_iff]
  rfl

/-! ## Full-`L` existence via a relation-forgetting projection -/

/-- Auxiliary Replacement output.  Its layout is `(fixed13,index,pair)`;
the two hidden witnesses are the stage and the old relation coordinate.  The
relation is used only to invoke the already verified existence theorem and
is forgotten from the output pair. -/
def bareStagePairAtFormula : FOFormula 15 :=
  .ex (.ex
    (.conj
      (FOFormula.rename stageEntryStateRename stageStateAtFormula)
      (Delta0Formula.kuratowskiPairEqAt
        (14 : Fin 17) (13 : Fin 17) (15 : Fin 17)).toFO))

/-- Exact external semantics of the projection formula. -/
def BareStagePairAt (index pair : LCarrier.{u}) : Prop :=
  ∃ stage relation : LCarrier.{u},
    StageStateAt index stage relation ∧
    pair.1 = ZFSet.pair index.1 stage.1

@[simp]
theorem satisfies_bareStagePairAtFormula
    (index pair : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareStagePairAtFormula
        (stageEntryAtLAssignment index pair) ↔
      BareStagePairAt index pair := by
  simp only [bareStagePairAtFormula, BareStagePairAt,
    FOFormula.Satisfies]
  apply exists_congr
  intro stage
  apply exists_congr
  intro relation
  rw [FOFormula.satisfies_rename,
    comp_stageEntryStateRename,
    satisfies_stageStateAtFormula,
    Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  rfl

/-- Replacement in `L` constructs the pair graph of all stage outputs below
the successor of `bound`, hence through `bound` itself. -/
theorem exists_bareStagePairFamily (bound : Ordinal.{u}) :
    ∃ history : LCarrier.{u}, ∀ pair : LCarrier.{u},
      pair.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (Order.succ bound)).1 ∧
          BareStagePairAt index pair := by
  have hfun : ∀ index : LCarrier.{u},
      index.1 ∈ (ordinalLCarrier (Order.succ bound)).1 →
        ∃! pair : LCarrier.{u},
          FOFormula.Satisfies LMem bareStagePairAtFormula
            (snoc (snoc stageHistoryFixedParameters index) pair) := by
    intro index hindex
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, _hordinal, rfl⟩
    rcases exists_stageStateAt_ordinal ordinal with
      ⟨relation, hstate⟩
    let pair := orderedPairLCarrier
      (ordinalLCarrier ordinal) (stageLCarrier ordinal)
    refine ⟨pair, ?_, ?_⟩
    · change FOFormula.Satisfies LMem bareStagePairAtFormula
        (stageEntryAtLAssignment (ordinalLCarrier ordinal) pair)
      apply (satisfies_bareStagePairAtFormula
        (ordinalLCarrier ordinal) pair).mpr
      exact ⟨stageLCarrier ordinal, relation, hstate,
        orderedPairLCarrier_val
          (ordinalLCarrier ordinal) (stageLCarrier ordinal)⟩
    · intro other hother
      have hother' :=
        (satisfies_bareStagePairAtFormula
          (ordinalLCarrier ordinal) other).mp hother
      rcases hother' with
        ⟨otherStage, otherRelation, hotherState, hotherCode⟩
      have houtputs := stageStateAt_ordinal_outputs_unique ordinal
        hotherState hstate
      apply Subtype.ext
      calc
        other.1 = ZFSet.pair (ordinalLCarrier ordinal).1
            otherStage.1 := hotherCode
        _ = ZFSet.pair (ordinalLCarrier ordinal).1
            (stageLCarrier ordinal).1 := by rw [houtputs.1]
        _ = pair.1 := (orderedPairLCarrier_val
          (ordinalLCarrier ordinal) (stageLCarrier ordinal)).symm
  rcases exists_replacementLCarrier bareStagePairAtFormula
      stageHistoryFixedParameters
      (ordinalLCarrier (Order.succ bound)) hfun with
    ⟨history, hhistory⟩
  refine ⟨history, ?_⟩
  intro pair
  rw [hhistory]
  apply exists_congr
  intro index
  apply and_congr_right
  intro _hindex
  exact satisfies_bareStagePairAtFormula index pair











/-! ## Identification with the previously defined hierarchy -/

























/-! ## Raw semantics over a transitive set -/



/-- Raw counterpart of `BareHistoryEntry`. -/
def BareHistoryEntryIn
    (history index stage : ZFSet.{u}) : Prop :=
  ZFSet.pair index stage ∈ history









/-- Raw local-state assignment with an arbitrary thirteen-coordinate prefix. -/
def bareHistoryStateRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (snoc (snoc fixed history) index) stage









/-- Raw assignment for the relation-free limit clause. -/
def bareHistoryLimitRawAssignment
    (history index stage : ZFSet.{u}) : Tuple ZFSet.{u} 3 :=
  ![history, index, stage]



/-- The usual internally relativized limit-stage condition: every displayed
quantifier ranges over `U`, and entries are ordinary Kuratowski pairs. -/
def BareHistoryLimitStateIn (U : Set ZFSet.{u})
    (history index stage : ZFSet.{u}) : Prop :=
  ∀ z : ZFSet.{u}, z ∈ U →
    (z ∈ stage ↔
      ∃ earlierIndex : ZFSet.{u},
        earlierIndex ∈ U ∧ earlierIndex ∈ index ∧
        ∃ earlierStage : ZFSet.{u},
          earlierStage ∈ U ∧
          BareHistoryEntryIn history earlierIndex earlierStage ∧
          z ∈ earlierStage)



/-! ### The isolated successor obligation -/

/-- Raw assignment of the existing `godelDef` output formula, with an
arbitrary thirteen-coordinate evaluator prefix. -/
def bareGodelDefOutputRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (predecessorStage stage : ZFSet.{u}) :
    Tuple ZFSet.{u} 15 :=
  snoc (tupleCons predecessorStage fixed) stage

/-- What the current object-language evaluator says internally.  This is
kept as a satisfaction statement rather than silently identified with the
ambient `godelDef`. -/
def BareGodelDefOutputIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (predecessorStage stage : ZFSet.{u}) : Prop :=
  SatisfiesIn U Godel.RudimentaryTerm.godelDefOutputFormula
    (bareGodelDefOutputRawAssignment fixed predecessorStage stage)

/-- The precise missing absoluteness obligation for successor steps.  Later
uses may assume this predicate only after proving it for the relevant
transitive stage; its name does not assert that the obligation already holds. -/
def BareGodelDefOutputCorrectIn (U : ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13) : Prop :=
  ∀ predecessorStage stage : ZFSet.{u},
    predecessorStage ∈ U → stage ∈ U →
      (BareGodelDefOutputIn (U : Set ZFSet.{u}) fixed
          predecessorStage stage ↔
        stage = Godel.godelDef predecessorStage)

/-- Raw successor-witness assignment. -/
def bareHistorySuccessorWitnessRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage predecessorIndex predecessorStage : ZFSet.{u}) :
    Tuple ZFSet.{u} 18 :=
  snoc (snoc (bareHistoryStateRawAssignment fixed history index stage)
    predecessorIndex) predecessorStage







/-- Exact internally relativized successor clause.  Notice that the final
conjunct remains `BareGodelDefOutputIn`; replacing it by ambient `godelDef`
requires `BareGodelDefOutputCorrectIn`. -/
def BareHistorySuccessorStateIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) : Prop :=
  ∃ predecessorIndex : ZFSet.{u}, predecessorIndex ∈ U ∧
    ∃ predecessorStage : ZFSet.{u}, predecessorStage ∈ U ∧
      index = insert predecessorIndex predecessorIndex ∧
      BareHistoryEntryIn history predecessorIndex predecessorStage ∧
      BareGodelDefOutputIn U fixed predecessorStage stage



/-! ### The complete raw local-state semantics -/









/-- The ordinary three-way recursion rule interpreted inside `U`:

* at zero, both the index and stage are the supplied empty-set parameter;
* at a successor, the preceding entry is present and the internally
  evaluated Goedel-definability formula yields the new stage;
* at a nonzero nonsuccessor, the stage is the union of earlier values, with
  every displayed quantifier restricted to `U`.

No ambient `godelDef` equality is asserted in this definition. -/
def BareHistoryLocalStateIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) : Prop :=
  (index = fixed (2 : Fin 13) ∧ stage = fixed (2 : Fin 13)) ∨
  BareHistorySuccessorStateIn U fixed history index stage ∨
  ((index ≠ fixed (2 : Fin 13) ∧
      ¬ ∃ predecessor : ZFSet.{u}, predecessor ∈ U ∧
        index = insert predecessor predecessor) ∧
    BareHistoryLimitStateIn U history index stage)

/-- The usual ambient mathematical reading of the successor clause, while
the two witnesses are still required to lie in `U`. -/
def BareHistorySuccessorStateAmbientIn (U : Set ZFSet.{u})
    (history index stage : ZFSet.{u}) : Prop :=
  ∃ predecessorIndex : ZFSet.{u}, predecessorIndex ∈ U ∧
    ∃ predecessorStage : ZFSet.{u}, predecessorStage ∈ U ∧
      index = insert predecessorIndex predecessorIndex ∧
      BareHistoryEntryIn history predecessorIndex predecessorStage ∧
      stage = Godel.godelDef predecessorStage



/-- The standard ambient three-way recursion, with witnesses restricted to
`U` but the successor output identified with the actual `godelDef`. -/
def BareHistoryLocalStateAmbientIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) : Prop :=
  (index = fixed (2 : Fin 13) ∧ stage = fixed (2 : Fin 13)) ∨
  BareHistorySuccessorStateAmbientIn U history index stage ∨
  ((index ≠ fixed (2 : Fin 13) ∧
      ¬ ∃ predecessor : ZFSet.{u}, predecessor ∈ U ∧
        index = insert predecessor predecessor) ∧
    BareHistoryLimitStateIn U history index stage)







/-! ### Raw valid histories -/





/-- Raw layout `(fixed13,history,bound)`. -/
def bareValidStageHistoryRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (history bound : ZFSet.{u}) :
    Tuple ZFSet.{u} 15 :=
  snoc (snoc fixed history) bound

/-- Raw layout after adjoining the index selected by the outer universal
quantifier. -/
def bareValidStageHistoryIndexRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (history bound index : ZFSet.{u}) :
    Tuple ZFSet.{u} 16 :=
  snoc (bareValidStageHistoryRawAssignment fixed history bound) index

/-- Raw layout after adjoining the stage selected by the index body. -/
def bareValidStageHistoryStageRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (history bound index stage : ZFSet.{u}) : Tuple ZFSet.{u} 17 :=
  snoc (bareValidStageHistoryIndexRawAssignment fixed history bound index)
    stage











/-- The exact internally relativized condition imposed at one selected
index of a bare history. -/
def BareValidStageHistoryIndexIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history index : ZFSet.{u}) : Prop :=
  ∃ stage : ZFSet.{u}, stage ∈ U ∧
    BareHistoryEntryIn history index stage ∧
    (∀ otherStage : ZFSet.{u}, otherStage ∈ U →
      BareHistoryEntryIn history index otherStage → otherStage = stage) ∧
    BareHistoryLocalStateIn U fixed history index stage





/-- A raw pair-coded history is total, stage-functional, and locally correct
through `bound`, with every quantified index and stage restricted to `U`.
Members of `history` that are not relevant pair entries remain harmless, just
as in `bareValidStageHistoryFormula`. -/
def BareValidStageHistoryIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history bound : ZFSet.{u}) : Prop :=
  ∀ index : ZFSet.{u}, index ∈ U →
    (index ∈ bound ∨ index = bound) →
      BareValidStageHistoryIndexIn U fixed history index



/-! ### Raw history-independent stage output -/

/-- Raw layout `(fixed13,index,stage)`. -/
def bareStageAtRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (index stage : ZFSet.{u}) :
    Tuple ZFSet.{u} 15 :=
  snoc (snoc fixed index) stage

/-- Raw layout after adjoining the hidden history witness. -/
def bareStageAtHistoryRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (index stage history : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (bareStageAtRawAssignment fixed index stage) history







/-- Inside `U`, `stage` is the output at `index` when some history in `U` is
valid through `index` and contains the top pair `(index,stage)`. -/
def BareStageAtIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (index stage : ZFSet.{u}) : Prop :=
  ∃ history : ZFSet.{u}, history ∈ U ∧
    BareValidStageHistoryIn U fixed history index ∧
    BareHistoryEntryIn history index stage



/-! ### Soundness of internal ordinal outputs -/

/-- Raw canonical evaluator parameters. -/
def stageHistoryFixedParametersRaw : Tuple ZFSet.{u} 13 :=
  fun i => (stageHistoryFixedParameters.{u} i).1

@[simp]
theorem stageHistoryFixedParametersRaw_empty :
    stageHistoryFixedParametersRaw (2 : Fin 13) = (∅ : ZFSet.{u}) := by
  change (stageHistoryFixedParameters (2 : Fin 13)).1 = (∅ : ZFSet.{u})
  rw [stageHistoryFixedParameters_empty]
  rfl

















end

end Constructible.Model

end
end GCHSource_Work_CUGCH_BareStageHistory


/- Source module: Solutions.Work_CUGCH_VEqualsL -/
section GCHSource_Work_CUGCH_VEqualsL
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The constructible universe satisfies an evaluator-coded `V = L` sentence

This file internalizes the constructible hierarchy in the membership structure
carried by `L`.  The constants used by the stage-history evaluator are first
characterized without parameters.  The resulting unary formula says that its
argument belongs to a stage produced by a valid internal history.

The main comparison theorem identifies that internal hierarchy, externalized
back to `ZFSet`, with the original class `L`. The final sentence is therefore
proved to express this property for `LCarrier`. This file does not assert the
separate, stronger adequacy theorem that the same evaluator-coded sentence is
equivalent to an independently defined internal constructible universe in
every arbitrary ZFC model.
-/

section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Parameter-free canonical constants -/

/-- `s i` has no members. -/
def emptySetAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.all (.neg (.mem (Fin.last n) i.castSucc))

@[simp]
theorem satisfies_emptySetAt {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (emptySetAt i) s <->
      s i = emptyLCarrier := by
  simp only [emptySetAt, FOFormula.satisfies_all,
    FOFormula.Satisfies, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply lCarrier_extensionality
    intro z
    constructor
    · intro hz
      exact (h z hz).elim
    · intro hz
      exact (not_mem_emptyLCarrier z hz).elim
  · intro h z hz
    rw [h] at hz
    exact not_mem_emptyLCarrier z hz

/-- The von Neumann successor of `x`, packaged as an element of `L`. -/
def successorLCarrier (x : LCarrier.{u}) : LCarrier.{u} :=
  ⟨insert x.1 x.1, by
    rw [ZFSet.insert_eq]
    exact union_mem_L (singleton_mem_L x.2) x.2⟩

@[simp]
theorem successorLCarrier_val (x : LCarrier.{u}) :
    (successorLCarrier x).1 = insert x.1 x.1 :=
  rfl

@[simp]
theorem successorLCarrier_ordinalLCarrier (alpha : Ordinal.{u}) :
    successorLCarrier (ordinalLCarrier alpha) =
      ordinalLCarrier (Order.succ alpha) := by
  rw [Order.succ_eq_add_one]
  apply Subtype.ext
  simp only [successorLCarrier_val, ordinalLCarrier_val,
    Ordinal.toZFSet_add_one]

@[simp]
theorem successorLCarrier_natOrdinal (n : Nat) :
    successorLCarrier (ordinalLCarrier (n : Ordinal.{u})) =
      ordinalLCarrier ((n + 1 : Nat) : Ordinal.{u}) := by
  simpa only [Nat.cast_add, Nat.cast_one, Order.succ_eq_add_one] using
    successorLCarrier_ordinalLCarrier (n : Ordinal.{u})

/-- `s succ` is the von Neumann successor of `s index`. -/
def successorSetAt {n : Nat} (succ index : Fin n) : FOFormula n :=
  Delta0Formula.successorFOAt succ index

@[simp]
theorem satisfies_successorSetAt {n : Nat} (succ index : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (successorSetAt succ index) s <->
      s succ = successorLCarrier (s index) := by
  rw [successorSetAt,
    Delta0Formula.satisfies_successorFOAt_lCarrier]
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg Subtype.val h

/-- External semantics of the object-language predicate for inductive sets. -/
def IsInductiveSet (w : LCarrier.{u}) : Prop :=
  emptyLCarrier.1 ∈ w.1 /\
    forall x : LCarrier.{u}, x.1 ∈ w.1 ->
      (successorLCarrier x).1 ∈ w.1

/-- `s i` is inductive: it contains the empty set and is successor-closed. -/
def inductiveSetAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (.ex (.conj
      (emptySetAt (Fin.last n))
      (.mem (Fin.last n) i.castSucc)))
    (FOFormula.all
      (FOFormula.imp
        (.mem (Fin.last n) i.castSucc)
        (.ex (.conj
          (successorSetAt
            (Fin.last (n + 1)) (Fin.last n).castSucc)
          (.mem (Fin.last (n + 1)) i.castSucc.castSucc)))))

@[simp]
theorem satisfies_inductiveSetAt {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (inductiveSetAt i) s <->
      IsInductiveSet (s i) := by
  simp only [inductiveSetAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_emptySetAt, satisfies_successorSetAt,
    snoc_last, snoc_castSucc, IsInductiveSet]
  constructor
  · rintro ⟨⟨e, he, hemem⟩, hsucc⟩
    constructor
    · simpa only [he] using hemem
    · intro x hx
      rcases hsucc x hx with ⟨next, hnext, hnextMem⟩
      simpa only [hnext] using hnextMem
  · rintro ⟨hempty, hsucc⟩
    constructor
    · exact ⟨emptyLCarrier, rfl, hempty⟩
    · intro x hx
      exact ⟨successorLCarrier x, rfl, hsucc x hx⟩

/-- The standard `omega` in `L` is inductive. -/
theorem omegaLCarrier_isInductiveSet :
    IsInductiveSet (omegaLCarrier : LCarrier.{u}) := by
  constructor
  · exact empty_mem_omegaLCarrier
  · intro x hx
    rcases successor_mem_omegaLCarrier x hx with
      ⟨next, hnextMem, hnext⟩
    have hnextEq : next = successorLCarrier x := by
      apply lCarrier_extensionality
      intro z
      rw [hnext z, successorLCarrier_val, ZFSet.mem_insert_iff]
      simp only [Subtype.ext_iff, or_comm]
    simpa only [hnextEq] using hnextMem

/-- Every standard finite ordinal belongs to every internally inductive set. -/
theorem ordinalLCarrier_nat_mem_of_isInductiveSet
    {w : LCarrier.{u}} (hw : IsInductiveSet w) (n : Nat) :
    (ordinalLCarrier (n : Ordinal.{u})).1 ∈ w.1 := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, ordinalLCarrier_zero] using hw.1
  | succ n ih =>
      have hnext := hw.2 (ordinalLCarrier (n : Ordinal.{u})) ih
      simpa only [Nat.cast_add, Nat.cast_one, Order.succ_eq_add_one,
        successorLCarrier_ordinalLCarrier] using hnext

/-- The standard `omega` is contained in every internally inductive set. -/
theorem omegaLCarrier_subset_of_isInductiveSet
    {w : LCarrier.{u}} (hw : IsInductiveSet w) :
    forall x : LCarrier.{u}, x.1 ∈ omegaLCarrier.1 -> x.1 ∈ w.1 := by
  intro x hx
  change x.1 ∈ Ordinal.omega0.toZFSet at hx
  rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨alpha, halpha, hx⟩
  rcases Ordinal.lt_omega0.mp halpha with ⟨n, hn⟩
  have hxEq : x = ordinalLCarrier (n : Ordinal.{u}) := by
    apply Subtype.ext
    calc
      x.1 = alpha.toZFSet := hx.symm
      _ = (n : Ordinal.{u}).toZFSet := congrArg Ordinal.toZFSet hn
      _ = (ordinalLCarrier (n : Ordinal.{u})).1 := rfl
  rw [hxEq]
  exact ordinalLCarrier_nat_mem_of_isInductiveSet hw n

/-- `s i` is the least inductive set, hence the model's `omega`. -/
def omegaSetAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (inductiveSetAt i)
    (FOFormula.all
      (FOFormula.imp
        (inductiveSetAt (Fin.last n))
        (FOFormula.boundedAll i.castSucc
          (.mem (Fin.last (n + 1)) (Fin.last n).castSucc))))

@[simp]
theorem satisfies_omegaSetAt {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (omegaSetAt i) s <->
      s i = omegaLCarrier := by
  simp only [omegaSetAt, FOFormula.Satisfies,
    satisfies_inductiveSetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.satisfies_boundedAll,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨homegaInd, hminimal⟩
    apply lCarrier_extensionality
    intro z
    constructor
    · intro hz
      exact hminimal omegaLCarrier omegaLCarrier_isInductiveSet z hz
    · intro hz
      exact omegaLCarrier_subset_of_isInductiveSet homegaInd z hz
  · intro h
    rw [h]
    refine ⟨omegaLCarrier_isInductiveSet, ?_⟩
    intro w hw x hx
    exact omegaLCarrier_subset_of_isInductiveSet hw x hx

/-! ## The canonical evaluator parameters -/

/-- A transparent presentation of the thirteen canonical parameters. -/
def canonicalStageParameters : Tuple LCarrier.{u} 13 :=
  ![ordinalLCarrier ((0 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((1 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((0 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((0 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((1 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((2 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((3 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((4 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((5 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((6 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((7 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((8 : Nat) : Ordinal.{u}),
    omegaLCarrier]

theorem canonicalStageParameters_eq_fixed :
    (canonicalStageParameters : Tuple LCarrier.{u} 13) =
      stageHistoryFixedParameters := by
  funext i
  fin_cases i <;>
    apply Subtype.ext <;>
    norm_num [canonicalStageParameters, stageHistoryFixedParameters,
      emptyLCarrier, omegaLCarrier,
      Godel.RudimentaryTerm.varTag,
      Godel.RudimentaryTerm.appTag,
      Godel.RudimentaryTerm.operationCode,
      Ordinal.toZFSet_add_one]

/--
The thirteen evaluator parameters are, in order,
`0, 1, 0, 0, 1, ..., 8, omega`.
-/
def canonicalStageParametersFormula : FOFormula 13 :=
  .conj (emptySetAt (0 : Fin 13))
    (.conj (successorSetAt (1 : Fin 13) (0 : Fin 13))
      (.conj (.eq (2 : Fin 13) (0 : Fin 13))
        (.conj (.eq (3 : Fin 13) (0 : Fin 13))
          (.conj (successorSetAt (4 : Fin 13) (3 : Fin 13))
            (.conj (successorSetAt (5 : Fin 13) (4 : Fin 13))
              (.conj (successorSetAt (6 : Fin 13) (5 : Fin 13))
                (.conj (successorSetAt (7 : Fin 13) (6 : Fin 13))
                  (.conj (successorSetAt (8 : Fin 13) (7 : Fin 13))
                    (.conj (successorSetAt (9 : Fin 13) (8 : Fin 13))
                      (.conj (successorSetAt (10 : Fin 13) (9 : Fin 13))
                        (.conj (successorSetAt (11 : Fin 13) (10 : Fin 13))
                          (omegaSetAt (12 : Fin 13)))))))))))))

/-- The parameter specification has exactly the evaluator tuple as a model. -/
@[simp]
theorem satisfies_canonicalStageParametersFormula
    (s : Tuple LCarrier.{u} 13) :
    FOFormula.Satisfies LMem canonicalStageParametersFormula s <->
      s = stageHistoryFixedParameters := by
  simp only [canonicalStageParametersFormula, FOFormula.Satisfies,
    satisfies_emptySetAt, satisfies_successorSetAt,
    satisfies_omegaSetAt]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12⟩
    have e0 : s 0 = ordinalLCarrier ((0 : Nat) : Ordinal.{u}) := by
      simpa only [Nat.cast_zero, ordinalLCarrier_zero] using h0
    have e1 : s 1 = ordinalLCarrier ((1 : Nat) : Ordinal.{u}) := by
      calc
        s 1 = successorLCarrier (s 0) := h1
        _ = successorLCarrier
            (ordinalLCarrier ((0 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e0
        _ = ordinalLCarrier ((0 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 0
        _ = ordinalLCarrier ((1 : Nat) : Ordinal.{u}) := by norm_num
    have e2 : s 2 = ordinalLCarrier ((0 : Nat) : Ordinal.{u}) := h2.trans e0
    have e3 : s 3 = ordinalLCarrier ((0 : Nat) : Ordinal.{u}) := h3.trans e0
    have e4 : s 4 = ordinalLCarrier ((1 : Nat) : Ordinal.{u}) := by
      calc
        s 4 = successorLCarrier (s 3) := h4
        _ = successorLCarrier
            (ordinalLCarrier ((0 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e3
        _ = ordinalLCarrier ((0 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 0
        _ = ordinalLCarrier ((1 : Nat) : Ordinal.{u}) := by norm_num
    have e5 : s 5 = ordinalLCarrier ((2 : Nat) : Ordinal.{u}) := by
      calc
        s 5 = successorLCarrier (s 4) := h5
        _ = successorLCarrier
            (ordinalLCarrier ((1 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e4
        _ = ordinalLCarrier ((1 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 1
        _ = ordinalLCarrier ((2 : Nat) : Ordinal.{u}) := by norm_num
    have e6 : s 6 = ordinalLCarrier ((3 : Nat) : Ordinal.{u}) := by
      calc
        s 6 = successorLCarrier (s 5) := h6
        _ = successorLCarrier
            (ordinalLCarrier ((2 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e5
        _ = ordinalLCarrier ((2 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 2
        _ = ordinalLCarrier ((3 : Nat) : Ordinal.{u}) := by norm_num
    have e7 : s 7 = ordinalLCarrier ((4 : Nat) : Ordinal.{u}) := by
      calc
        s 7 = successorLCarrier (s 6) := h7
        _ = successorLCarrier
            (ordinalLCarrier ((3 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e6
        _ = ordinalLCarrier ((3 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 3
        _ = ordinalLCarrier ((4 : Nat) : Ordinal.{u}) := by norm_num
    have e8 : s 8 = ordinalLCarrier ((5 : Nat) : Ordinal.{u}) := by
      calc
        s 8 = successorLCarrier (s 7) := h8
        _ = successorLCarrier
            (ordinalLCarrier ((4 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e7
        _ = ordinalLCarrier ((4 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 4
        _ = ordinalLCarrier ((5 : Nat) : Ordinal.{u}) := by norm_num
    have e9 : s 9 = ordinalLCarrier ((6 : Nat) : Ordinal.{u}) := by
      calc
        s 9 = successorLCarrier (s 8) := h9
        _ = successorLCarrier
            (ordinalLCarrier ((5 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e8
        _ = ordinalLCarrier ((5 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 5
        _ = ordinalLCarrier ((6 : Nat) : Ordinal.{u}) := by norm_num
    have e10 : s 10 = ordinalLCarrier ((7 : Nat) : Ordinal.{u}) := by
      calc
        s 10 = successorLCarrier (s 9) := h10
        _ = successorLCarrier
            (ordinalLCarrier ((6 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e9
        _ = ordinalLCarrier ((6 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 6
        _ = ordinalLCarrier ((7 : Nat) : Ordinal.{u}) := by norm_num
    have e11 : s 11 = ordinalLCarrier ((8 : Nat) : Ordinal.{u}) := by
      calc
        s 11 = successorLCarrier (s 10) := h11
        _ = successorLCarrier
            (ordinalLCarrier ((7 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e10
        _ = ordinalLCarrier ((7 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 7
        _ = ordinalLCarrier ((8 : Nat) : Ordinal.{u}) := by norm_num
    have hs : s = canonicalStageParameters := by
      funext i
      fin_cases i
      all_goals assumption
    exact hs.trans canonicalStageParameters_eq_fixed
  · rintro rfl
    rw [← canonicalStageParameters_eq_fixed]
    simp [canonicalStageParameters]
    refine ⟨?_, ?_⟩
    · simpa only [ordinalLCarrier_zero, Order.succ_eq_add_one,
        zero_add] using
        (successorLCarrier_ordinalLCarrier (0 : Ordinal.{u})).symm
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals congr 1 <;> norm_num

/-! ## Internal stages -/

/-- The stage coordinate of a valid internal history at `index`. -/
def InternalLStageAt (index stage : LCarrier.{u}) : Prop :=
  ∃ relation : LCarrier.{u}, StageStateAt index stage relation

/-- Layout `(fixed13, index, stage)`.  The relation coordinate is hidden. -/
def internalLStageAtLAssignment
    (index stage : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters index) stage

/-- A formula defining the internal constructible stage at one index. -/
def internalLStageAtFormula : FOFormula 15 :=
  .ex stageStateAtFormula

@[simp]
theorem satisfies_internalLStageAtFormula
    (index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem internalLStageAtFormula
        (internalLStageAtLAssignment index stage) ↔
      InternalLStageAt index stage := by
  simp only [internalLStageAtFormula, FOFormula.Satisfies,
    InternalLStageAt]
  change (∃ relation : LCarrier.{u},
      FOFormula.Satisfies LMem stageStateAtFormula
        (stageStateAtLAssignment index stage relation)) ↔ _
  simp only [satisfies_stageStateAtFormula]

/-- At a canonical ordinal index, the internally evaluated stage is exactly
the externally constructed level `L_alpha`. -/
theorem internalLStageAt_ordinal_iff
    (alpha : Ordinal.{u}) (stage : LCarrier.{u}) :
    InternalLStageAt (ordinalLCarrier alpha) stage ↔
      stage = stageLCarrier alpha := by
  constructor
  · rintro ⟨relation, hstate⟩
    rcases exists_stageStateAt_ordinal alpha with
      ⟨canonicalRelation, hcanonical⟩
    exact (stageStateAt_ordinal_outputs_unique
      alpha hstate hcanonical).1
  · rintro rfl
    exact exists_stageStateAt_ordinal alpha

/-! ## Ordinals of the internal model -/

/-- Transitivity has the expected semantics when quantifiers range over `L`.
The only extra step compared with set-sized carriers is closure of `L` under
membership. -/
theorem satisfies_ordinalTransitive_lCarrier (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem OrdinalFormula.transitive ![x] ↔
      x.1.IsTransitive := by
  simp only [OrdinalFormula.transitive,
    FOFormula.satisfies_boundedAll, FOFormula.Satisfies,
    Matrix.cons_val_zero, snoc_last]
  constructor
  · intro h y hy z hz
    have hyL : y ∈ L := mem_L_of_mem hy x.2
    have hzL : z ∈ L := mem_L_of_mem hz hyL
    exact h ⟨y, hyL⟩ hy ⟨z, hzL⟩ hz
  · intro hx y hy z hz
    exact hx.mem_trans hz hy

/-- Every member being transitive also has its ambient semantics in `L`. -/
theorem satisfies_ordinalMembersTransitive_lCarrier
    (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem OrdinalFormula.membersTransitive ![x] ↔
      ∀ y ∈ x.1, y.IsTransitive := by
  simp only [OrdinalFormula.membersTransitive,
    FOFormula.satisfies_boundedAll, FOFormula.Satisfies,
    Matrix.cons_val_zero, snoc_last]
  constructor
  · intro h y hy z hz w hw
    have hyL : y ∈ L := mem_L_of_mem hy x.2
    have hzL : z ∈ L := mem_L_of_mem hz hyL
    have hwL : w ∈ L := mem_L_of_mem hw hzL
    exact h ⟨y, hyL⟩ hy ⟨z, hzL⟩ hz ⟨w, hwL⟩ hw
  · intro h y hy z hz w hw
    exact (h y.1 hy).mem_trans hw hz

/-- The parameter-free ordinal formula is absolute to `LCarrier`. -/
@[simp]
theorem satisfies_isOrdinal_lCarrier (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem OrdinalFormula.isOrdinal ![x] ↔
      x.1.IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  simp only [OrdinalFormula.isOrdinal, FOFormula.Satisfies,
    satisfies_ordinalTransitive_lCarrier,
    satisfies_ordinalMembersTransitive_lCarrier]

/-- Every internally recognized ordinal is a unique canonical ordinal code. -/
theorem exists_eq_ordinalLCarrier_of_isOrdinal
    (index : LCarrier.{u}) (hindex : index.1.IsOrdinal) :
    ∃ alpha : Ordinal.{u}, index = ordinalLCarrier alpha := by
  refine ⟨index.1.rank, ?_⟩
  apply Subtype.ext
  exact hindex.toZFSet_rank_eq.symm

/-- Put the one-variable ordinal predicate at coordinate `i`. -/
def ordinalAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.rename (fun _ : Fin 1 => i) OrdinalFormula.isOrdinal

@[simp]
theorem satisfies_ordinalAt {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (ordinalAt i) s ↔
      (s i).1.IsOrdinal := by
  rw [ordinalAt, FOFormula.satisfies_rename]
  have hassignment : (fun _ : Fin 1 => s i) = ![s i] := by
    funext j
    exact Fin.eq_zero j ▸ rfl
  rw [hassignment, satisfies_isOrdinal_lCarrier]

/-! ## The internally constructible class -/

/-- Layout `(fixed13, x)`. -/
def constructibleWithParametersLAssignment
    (x : LCarrier.{u}) : Tuple LCarrier.{u} 14 :=
  snoc stageHistoryFixedParameters x

/-- The assignment after adjoining witnesses for the stage index and stage. -/
def constructibleWitnessLAssignment
    (x index stage : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc (constructibleWithParametersLAssignment x) index) stage

/-- Select `(fixed13, index, stage)` from `(fixed13, x, index, stage)`. -/
def constructibleInternalStageRename : Fin 15 → Fin 16 :=
  Fin.lastCases
    (15 : Fin 16)
    (fun i14 => Fin.lastCases
      (14 : Fin 16)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

 theorem comp_constructibleInternalStageRename
    (x index stage : LCarrier.{u}) :
    (fun i => constructibleWitnessLAssignment x index stage
      (constructibleInternalStageRename i)) =
      internalLStageAtLAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · rw [show constructibleInternalStageRename
          i13.castSucc.castSucc =
          i13.castSucc.castSucc.castSucc by
        simp only [constructibleInternalStageRename,
          Fin.lastCases_castSucc]
        apply Fin.ext
        rfl]
      simp only [constructibleWitnessLAssignment,
        constructibleWithParametersLAssignment,
        internalLStageAtLAssignment, snoc_castSucc]

/-- With the thirteen evaluator constants supplied, `x` belongs to a stage
at an internally recognized ordinal index.  Layout: `(fixed13, x)`. -/
def constructibleWithParametersFormula : FOFormula 14 :=
  .ex (.ex
    (.conj
      (ordinalAt (14 : Fin 16))
      (.conj
        (FOFormula.rename constructibleInternalStageRename
          internalLStageAtFormula)
        (.mem (13 : Fin 16) (15 : Fin 16)))))

/-- The internal stage predicate defines exactly membership in some external
level of the constructible hierarchy. -/
@[simp]
theorem satisfies_constructibleWithParametersFormula
    (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem constructibleWithParametersFormula
        (constructibleWithParametersLAssignment x) ↔
      ∃ alpha : Ordinal.{u}, x.1 ∈ LStageZF alpha := by
  simp only [constructibleWithParametersFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨index, stage, hindexFormula, hstageFormula, hxstage⟩
    have hindex : index.1.IsOrdinal := by
      exact (satisfies_ordinalAt (14 : Fin 16)
        (constructibleWitnessLAssignment x index stage)).mp
        hindexFormula
    have hstage : InternalLStageAt index stage := by
      apply (satisfies_internalLStageAtFormula index stage).mp
      rw [← comp_constructibleInternalStageRename x index stage]
      exact (FOFormula.satisfies_rename LMem internalLStageAtFormula
        constructibleInternalStageRename
        (constructibleWitnessLAssignment x index stage)).mp
        hstageFormula
    change x.1 ∈ stage.1 at hxstage
    rcases exists_eq_ordinalLCarrier_of_isOrdinal index hindex with
      ⟨alpha, rfl⟩
    have hstageEq :=
      (internalLStageAt_ordinal_iff alpha stage).mp hstage
    subst stage
    exact ⟨alpha, by
      simpa only [stageLCarrier_val] using hxstage⟩
  · rintro ⟨alpha, hxstage⟩
    refine ⟨ordinalLCarrier alpha, stageLCarrier alpha, ?_, ?_, ?_⟩
    · apply (satisfies_ordinalAt (14 : Fin 16)
        (constructibleWitnessLAssignment x
          (ordinalLCarrier alpha) (stageLCarrier alpha))).mpr
      exact ZFSet.isOrdinal_toZFSet alpha
    · apply (FOFormula.satisfies_rename LMem internalLStageAtFormula
        constructibleInternalStageRename
        (constructibleWitnessLAssignment x
          (ordinalLCarrier alpha) (stageLCarrier alpha))).mpr
      rw [comp_constructibleInternalStageRename,
        satisfies_internalLStageAtFormula]
      exact (internalLStageAt_ordinal_iff
        alpha (stageLCarrier alpha)).mpr rfl
    · change x.1 ∈ (stageLCarrier alpha).1
      simpa only [stageLCarrier_val] using hxstage

/-- The externalization of the class which `L` internally calls
constructible. -/
def RelativeL : Set ZFSet.{u} :=
  {x | ∃ hx : x ∈ L,
    FOFormula.Satisfies LMem constructibleWithParametersFormula
      (constructibleWithParametersLAssignment ⟨x, hx⟩)}

@[simp]
theorem mem_relativeL_iff {x : ZFSet.{u}} :
    x ∈ RelativeL ↔ x ∈ L := by
  constructor
  · rintro ⟨hxL, _hxInternal⟩
    exact hxL
  · intro hxL
    refine ⟨hxL, ?_⟩
    rw [satisfies_constructibleWithParametersFormula]
    exact mem_L_iff.mp hxL



/-! ## A parameter-free evaluator-coded sentence for `V = L` -/

/-- Before closing the evaluator parameters, require that they are the
canonical constants and that every set belongs to an internally computed
constructible stage. -/
def vEqualsLCoreFormula : FOFormula 13 :=
  .conj canonicalStageParametersFormula
    (FOFormula.all constructibleWithParametersFormula)

/-- Over `LCarrier`, the core formula has exactly the canonical parameter
assignment.  Its universal clause follows from the stagewise comparison. -/
@[simp]
theorem satisfies_vEqualsLCoreFormula
    (s : Tuple LCarrier.{u} 13) :
    FOFormula.Satisfies LMem vEqualsLCoreFormula s ↔
      s = stageHistoryFixedParameters := by
  simp only [vEqualsLCoreFormula, FOFormula.Satisfies,
    satisfies_canonicalStageParametersFormula,
    FOFormula.satisfies_all]
  constructor
  · exact fun h => h.1
  · rintro rfl
    refine ⟨rfl, ?_⟩
    intro x
    change FOFormula.Satisfies LMem
      constructibleWithParametersFormula
      (constructibleWithParametersLAssignment x)
    rw [satisfies_constructibleWithParametersFormula]
    exact mem_L_iff.mp x.2





end

end Constructible.Model

end
end GCHSource_Work_CUGCH_VEqualsL


