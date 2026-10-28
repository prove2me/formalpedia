-- Prove2me | Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
-- name    : CountingMatroid_Analysis_TransversalClassPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:07:04.923973+00:00
-- url     : https://prove2.me/theorems/5a16830e-1823-4112-a48c-2c14d2b6f649
-- title:
--   Pair classification and the transversal partition identity
-- statement:
--   For a paired state $S\subseteq[n]\times\{0,1\}$, the scan accumulator records an optional empty pair, an optional full pair, and a duplicate flag. A singly occupied pair leaves it unchanged; the first empty or full pair fills its corresponding field, while a further occurrence sets the flag. The bundle supplies the ordinary scan, its charged counterpart, and identities equating the returned values of both one visit and a list fold.
--
--   For any scan list, both optional fields are empty afterward exactly when they were empty initially and every visited pair was singly occupied. This equivalence does not require the initial duplicate flag to be false. Starting from empty fields and a false flag, the final classifier is invalid when the flag is true, transversal when both fields are empty, and a defect when the two fields contain distinct empty/full indices; all other cases are invalid. Consequently,
--   $$\operatorname{classifyState}(S)=\mathrm{transversal}
--   \iff \forall i\in[n],\ \bigl((i,0)\in S\iff(i,1)\notin S\bigr).$$
--   For natural rank parameter $r$, arbitrary independence oracles $o_1,o_2$, and $q\in\mathbb Q$, the included partition identity is
--   $$\sum_{\operatorname{classifyState}(S)=\mathrm{transversal}}
--   q^{\,n-\operatorname{pairedRank}_{r,o_1,o_2}(S)}
--   =\operatorname{partitionSum}_{r,o_1,o_2}(q).$$
--   The right side sums the same operational weights over original-ground subsets: a subset chooses label $0$ on its members and label $1$ elsewhere. Reindexing by this bijection proves the identity, including $n=0$, without exact-oracle or positivity hypotheses. The charged helpers concern abstract operation accounting.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TransversalClassPartition.lean#L11-L22

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
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
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

namespace CountingMatroid.Analysis.TransversalClassPartition

open CountingMatroid.Model CountingMatroid.Analysis.TransversalPartition
open CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: The return value of one pair-classification visit. -/
 def scanPair {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
    Option (Fin n) × Option (Fin n) × Bool :=
  if (i, false) ∈ state then
    if (i, true) ∈ state then
      if acc.2.1.isSome then (acc.1, acc.2.1, true)
      else (acc.1, some i, acc.2.2)
    else acc
  else if (i, true) ∈ state then acc
  else if acc.1.isSome then (acc.1, acc.2.1, true)
  else (some i, acc.2.1, acc.2.2)

/-- INTERNAL: The charged pair-classification visit, identical to the
anonymous visit used by `Program.classifyState`. -/
 def classifierVisit {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
    Arlib.Computation.Charged Op Cell (Option (Fin n) × Option (Fin n) × Bool) := do
  let x ← containsPaired state (i, false)
  let y ← containsPaired state (i, true)
  if x then
    if y then
      let seen ← isSome acc.2.1
      if seen then pure (acc.1, acc.2.1, true)
      else pure (acc.1, some i, acc.2.2)
    else pure acc
  else if y then pure acc
  else
    let seen ← isSome acc.1
    if seen then pure (acc.1, acc.2.1, true)
    else pure (some i, acc.2.1, acc.2.2)

/-- INTERNAL: Evaluate one charged visit, preserving all duplicate flags. -/
 theorem classifier_visit_value {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
    (classifierVisit state acc i).val = scanPair state acc i := by
  rcases acc with ⟨empty, full, flag⟩
  by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
    cases empty <;> cases full <;>
    simp [classifierVisit, scanPair, containsPaired, isSome, hx, hy]

/-- INTERNAL: Evaluate a classifier fold as the ordinary fold of its
per-pair return values. -/
 theorem classifier_fold_value {n : ℕ} (state : PairedSet n)
    (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
    (Arlib.Computation.Charged.foldl (classifierVisit state) l acc).val =
      l.foldl (scanPair state) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons i l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, classifier_visit_value,
        List.foldl_cons, ih]

/-- INTERNAL: No recorded empty/full pair after one visit means there was
none before it and the visited pair has exactly one occupied element. -/
 theorem scan_pair_no_defect {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
    ((scanPair state acc i).1 = none ∧ (scanPair state acc i).2.1 = none) ↔
      (acc.1 = none ∧ acc.2.1 = none) ∧
        ((i, false) ∈ state ↔ (i, true) ∉ state) := by
  rcases acc with ⟨empty, full, flag⟩
  by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
    cases empty <;> cases full <;> simp [scanPair, hx, hy]

/-- INTERNAL: A successful full scan contains no missing or full pair.
This invariant records both Option fields; the duplicate flag need not be
assumed false to establish this implication. -/
 theorem scan_fold_no_defect {n : ℕ} (state : PairedSet n)
    (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
    ((l.foldl (scanPair state) acc).1 = none ∧
      (l.foldl (scanPair state) acc).2.1 = none) ↔
      (acc.1 = none ∧ acc.2.1 = none) ∧
        ∀ i ∈ l, ((i, false) ∈ state ↔ (i, true) ∉ state) := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih, scan_pair_no_defect, List.forall_mem_cons]
      exact and_assoc

/-- INTERNAL: Evaluate the final classifier decision after its pair scan.
The last off-diagonal check is retained as ordinary index equality. -/
 theorem classify_value {n : ℕ} (state : PairedSet n) :
    let result := (List.finRange n).foldl (scanPair state) (none, none, false)
    (classifyState state).val =
      if result.2.2 then .invalid else
        match result.1, result.2.1 with
        | none, none => .transversal
        | some i, some j => if i = j then .invalid else .defect i j
        | _, _ => .invalid := by
  unfold classifyState
  change ((do
    let result ← Arlib.Computation.Charged.foldl (classifierVisit state)
      (List.finRange n) (none, none, false)
    if result.2.2 then pure .invalid else
      match result.1, result.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid) : Arlib.Computation.Charged Op Cell (StateKind n)).val = _
  rw [Arlib.Computation.Charged.val_bind, classifier_fold_value]
  generalize (List.finRange n).foldl (scanPair state) (none, none, false) = result
  rcases result with ⟨empty, full, flag⟩
  cases flag <;> cases empty <;> cases full <;> simp [indexEqual, apply_ite]

/-- INTERNAL: The charged classifier accepts precisely the paired sets
with exactly one occupied element at every pair, including the empty ground.
TEXLINE: main.tex:270-281,712-735 -/
 theorem classify_transversal_iff {n : ℕ} (state : PairedSet n) :
    (classifyState state).val = .transversal ↔
      ∀ i : Fin n, ((i, false) ∈ state ↔ (i, true) ∉ state) := by
  constructor
  · intro hclass
    have hvalue := classify_value state
    rw [hclass] at hvalue
    have hnone :
        ((List.finRange n).foldl (scanPair state) (none, none, false)).1 = none ∧
        ((List.finRange n).foldl (scanPair state) (none, none, false)).2.1 = none := by
      generalize (List.finRange n).foldl (scanPair state) (none, none, false) = result
        at hvalue ⊢
      rcases result with ⟨empty, full, flag⟩
      cases flag <;> cases empty <;> cases full
      all_goals simp only [Bool.false_eq_true, if_true, if_false]
        at hvalue ⊢
      all_goals first
        | trivial
        | cases hvalue
        | split_ifs at hvalue
    have hall := ((scan_fold_no_defect state (List.finRange n)
      (none, none, false)).mp hnone).2
    intro i
    exact hall i (List.mem_finRange i)
  · intro hall
    have hstep (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
        scanPair state acc i = acc := by
      by_cases hx : (i, false) ∈ state
      · have hy := (hall i).mp hx
        simp [scanPair, hx, hy]
      · have hy : (i, true) ∈ state := by
          by_contra hny
          exact hx ((hall i).mpr hny)
        simp [scanPair, hx, hy]
    have hfold (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
        l.foldl (scanPair state) acc = acc := by
      induction l generalizing acc with
      | nil => rfl
      | cons i l ih => rw [List.foldl_cons, hstep, ih]
    rw [classify_value, hfold]
    rfl

/-- INTERNAL: Reindex the operational classifier's transversal class by
original-ground subsets. This identifies the transversal mass and annealing
observable mean of the finite state-weight law with `partitionSum`.
TEXLINE: main.tex:270-281,712-735,1241-1247 -/
theorem transversal_class_partition {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) :
    (∑ state : PairedSet n,
      if (CountingMatroid.Program.classifyState state).val = .transversal then
        q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
      else 0) = partitionSum r o₁ o₂ q := by
  classical
  rw [← Finset.sum_filter]
  symm
  unfold partitionSum
  refine Finset.sum_bij (fun A _ => transversalState A) ?_ ?_ ?_ ?_
  · intro A _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply (classify_transversal_iff _).mpr
    intro i
    simp [transversalState]
  · intro A _ B _ h
    have hp := congrArg (fun state : PairedSet n =>
      (CountingMatroid.Model.Subroutines.pairedProjections state).val.1) h
    simpa only [transversalState,
      TransversalProjection.pairedProjections_transversal] using hp
  · intro state hstate
    have hpair := (classify_transversal_iff state).mp (Finset.mem_filter.mp hstate).2
    let A := Finset.univ.filter (fun i : Fin n => (i, false) ∈ state)
    refine ⟨A, Finset.mem_univ _, ?_⟩
    ext element
    rcases element with ⟨i, bit⟩
    cases bit with
    | false => simp [transversalState, A]
    | true =>
        have hp : (i, true) ∈ state ↔ (i, false) ∉ state := by
          simpa only [not_not] using (not_congr (hpair i)).symm
        simp [transversalState, A, hp]
  · intro A _
    rfl

end CountingMatroid.Analysis.TransversalClassPartition

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · after mechanical handoff rejection, proved the pair-scan no-defect invariant and full classifier characterization locally; the finite reindexing now has no unproved obligations.
* r21 · decomposed · the sum_bij route proved injectivity from paired projections and exact weight agreement, leaving forward classification and reverse reconstruction as an independent scan obligation.
-/

end


