-- Prove2me | Definitions.Def_CountingMatroid_Analysis_TransversalProjection
-- name    : CountingMatroid_Analysis_TransversalProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:05:09.995028+00:00
-- url     : https://prove2.me/theorems/80b6898d-5344-47e1-8fe4-5f63f9ca59d4
-- title:
--   Projection scan on a transversal
-- statement:
--   Let $n\in\mathbb N$ and $A\subseteq[n]$. Define the paired transversal
--   $$T(A)=\{(i,0):i\in A\}\cup\{(i,1):i\notin A\}.$$
--   The supplied helper theorem evaluates the program's projection scan: its first component collects label-zero indices, its second collects indices where label one is absent, and its third counts label-one indices. It proves
--   $$\operatorname{pairedProjections}(T(A))=(A,A,n-|A|).$$
--   For an index in $A$, both set accumulators receive the index; outside $A$, only the count increases. Scanning all indices yields the displayed value. The theorem concerns returned values and does not establish a concrete-machine charge bound.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TransversalProjection.lean#L9-L68

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.TransversalProjection

open CountingMatroid.Model

/-- INTERNAL: The concrete paired scan selects the same index set twice on a
transversal, and counts its complementary y elements.
TEXLINE: main.tex:270-280,1333-1346 -/
theorem pairedProjections_transversal {n : ℕ} (A : Finset (Fin n)) :
    (CountingMatroid.Model.Subroutines.pairedProjections
      (Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A))))).val =
      (A, A, n - A.card) := by
  classical
  let state : PairedSet n := Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A)))
  let step : (Finset (Fin n) × Finset (Fin n) × ℕ) → Fin n →
      Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
        CountingMatroid.Model.Operations.Cell
        (Finset (Fin n) × Finset (Fin n) × ℕ) := fun acc i => do
    let inX ← CountingMatroid.Model.Operations.containsPaired state (i, false)
    let x ← if inX then CountingMatroid.Model.Operations.insertElement acc.1 i else pure acc.1
    let inY ← CountingMatroid.Model.Operations.containsPaired state (i, true)
    if inY then
      let ysize ← CountingMatroid.Model.Operations.successor acc.2.2
      pure (x, acc.2.1, ysize)
    else
      let complementY ← CountingMatroid.Model.Operations.insertElement acc.2.1 i
      pure (x, complementY, acc.2.2)
  have hstep (x y : Finset (Fin n)) (k : ℕ) (i : Fin n) :
      (step (x, y, k) i).val =
        if i ∈ A then (insert i x, insert i y, k) else (x, y, k + 1) := by
    by_cases h : i ∈ A
    · simp [step, state, CountingMatroid.Model.Operations.containsPaired,
        CountingMatroid.Model.Operations.insertElement,
        CountingMatroid.Model.Operations.successor, h]
    · simp [step, state, CountingMatroid.Model.Operations.containsPaired,
        CountingMatroid.Model.Operations.insertElement,
        CountingMatroid.Model.Operations.successor, h]
  have hfold (l : List (Fin n)) (x y : Finset (Fin n)) (k : ℕ) :
      (Arlib.Computation.Charged.foldl step l (x, y, k)).val =
      (x ∪ (l.filter (fun i => i ∈ A)).toFinset,
       y ∪ (l.filter (fun i => i ∈ A)).toFinset,
       k + (l.filter (fun i => i ∉ A)).length) := by
    induction l generalizing x y k with
    | nil => simp
    | cons i l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, hstep]
      by_cases h : i ∈ A
      · simp [h, ih, Finset.union_insert, Finset.insert_union]
      · simp [h, ih, Nat.add_assoc, Nat.add_comm]
  change (Arlib.Computation.Charged.foldl step (List.finRange n)
    ((∅ : Finset (Fin n)), (∅ : Finset (Fin n)), 0)).val = _
  rw [hfold]
  have hfilter : (List.filter (fun i => i ∈ A) (List.finRange n)).toFinset = A := by
    ext i
    simp
  have hlen : (List.filter (fun i => i ∈ A) (List.finRange n)).length = A.card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter (fun i => i ∈ A)), hfilter]
  have htotal := List.length_eq_length_filter_add
    (l := List.finRange n) (f := fun i : Fin n => decide (i ∈ A))
  have hnot : (List.filter (fun i => !decide (i ∈ A)) (List.finRange n)).length = n - A.card := by
    have h : n = (List.filter (fun i => i ∈ A) (List.finRange n)).length +
        (List.filter (fun i => !decide (i ∈ A)) (List.finRange n)).length := by
      simpa using htotal
    omega
  simp [hfilter, hnot]

end CountingMatroid.Analysis.TransversalProjection

end


