-- Prove2me | Definitions.Def_CountingMatroid_Analysis_SelectedPairedBijection
-- name    : CountingMatroid_Analysis_SelectedPairedBijection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:09:21.894772+00:00
-- url     : https://prove2.me/theorems/e32824f3-a9ed-4ee6-9f5d-d9ec28db5925
-- title:
--   Ordered occupied and complementary label selection
-- statement:
--   For $E=\{0,\ldots,n-1\}\times\{0,1\}$, the paired-label list is
--   $$
--   [(0,0),(0,1),(1,0),(1,1),\ldots,(n-1,0),(n-1,1)].
--   $$
--   It contains every paired label exactly once. Given a paired state $S\subseteq E$ and a Boolean $b$, the selected list filters this order by the condition $[e\in S]=b$. Its underlying set is
--   $$
--   \operatorname{set}(\operatorname{selectedLabels}(S,b))=
--   \begin{cases}
--   S,&b=\mathrm{true},\\
--   E\setminus S,&b=\mathrm{false}.
--   \end{cases}
--   $$
--   The included lemmas establish that this list has no duplicates, and that either choice has length $n$ when $|S|=n$. Under that cardinality hypothesis, the selected-label function maps each index $k\in\{0,\ldots,n-1\}$ to the $k$th selected label together with its membership in the requested occupied or complementary set.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SelectedPairedBijection.lean#L13-L15

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The charged selector enumerates the occupied and unoccupied labels
without repetition, in the program's fixed x/y order. -/
namespace CountingMatroid.Analysis.SelectedPairedBijection
open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: The complete ordered paired-label list visited by selection. -/
def pairedLabels (n : ℕ) : List (PairedGround n) :=
  (List.finRange n).flatMap (fun i => [(i, false), (i, true)])

/-- INTERNAL: Each paired label occurs in the program's enumeration. -/
theorem mem_pairedLabels {n : ℕ} (a : PairedGround n) : a ∈ pairedLabels n := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [pairedLabels, List.mem_flatMap]

/-- INTERNAL: The complete paired-label enumeration contains no duplicates. -/
theorem pairedLabels_nodup (n : ℕ) : (pairedLabels n).Nodup := by
  have h := (List.nodup_finRange n).product
    (show ([false, true] : List Bool).Nodup by decide)
  simpa [pairedLabels, List.product, SProd.sprod] using h

/-- INTERNAL: Eligible labels in exactly the order of the charged scan. -/
def selectedLabels {n : ℕ} (state : PairedSet n) (occupied : Bool) :
    List (PairedGround n) :=
  (pairedLabels n).filter (fun a => decide (decide (a ∈ state) = occupied))

/-- INTERNAL: The selection list denotes the requested occupied/complement set. -/
theorem selectedLabels_toFinset {n : ℕ} (state : PairedSet n) (occupied : Bool) :
    (selectedLabels state occupied).toFinset = if occupied then state else stateᶜ := by
  classical
  ext a
  cases occupied <;> simp [selectedLabels, mem_pairedLabels]

/-- INTERNAL: The eligible labels also contain no duplicates. -/
theorem selectedLabels_nodup {n : ℕ} (state : PairedSet n) (occupied : Bool) :
    (selectedLabels state occupied).Nodup :=
  (pairedLabels_nodup n).filter _

/-- INTERNAL: Both selection lists have n entries on an n-element paired state. -/
theorem selectedLabels_length {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (hcard : state.card = n) : (selectedLabels state occupied).length = n := by
  have h := List.toFinset_card_of_nodup (selectedLabels_nodup state occupied)
  rw [selectedLabels_toFinset] at h
  cases occupied <;> simp [hcard, Finset.card_compl, PairedGround] at h <;> omega











/-- INTERNAL: Select a label as an element of the actual occupied/complement set. -/
def selectedLabel {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (hcard : state.card = n) (k : Fin n) :
    {a : PairedGround n // a ∈ if occupied then state else stateᶜ} :=
  ⟨(selectedLabels state occupied)[k.val]'(by rw [selectedLabels_length state occupied hcard]; exact k.isLt),
    by
      have h := List.getElem_mem
        (show k.val < (selectedLabels state occupied).length by
          rw [selectedLabels_length state occupied hcard]; exact k.isLt)
      rw [← selectedLabels_toFinset state occupied]
      exact List.mem_toFinset.mpr h⟩







end CountingMatroid.Analysis.SelectedPairedBijection

end


