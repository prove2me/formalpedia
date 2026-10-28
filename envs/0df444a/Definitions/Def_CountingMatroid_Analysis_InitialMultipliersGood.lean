-- Prove2me | Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
-- name    : CountingMatroid_Analysis_InitialMultipliersGood
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:14.006824+00:00
-- url     : https://prove2.me/theorems/b3064caa-de22-4e21-9e45-9b141616f337
-- title:
--   Pair-scan semantics and a parameterization of defect states
-- statement:
--   Let $S\subseteq[n]\times\{0,1\}$ be a paired state. A scan accumulator $(e,f,b)$ records an optional empty-pair index, an optional full-pair index, and a duplicate flag. At a visited pair $i$, exactly one occupied label leaves the accumulator unchanged. A full pair records $i$ if no full pair was recorded, and otherwise sets $b$ to true; an empty pair behaves analogously for the empty-pair field. The charged visit carries out this same branching using the model's membership and option tests.
--
--   For a defect index $(e,f)$ with $e\ne f$, define the ordinary pairs $O=[n]\setminus\{e,f\}$. For any subset $A\subseteq[n]$, the corresponding choice state is
--   $$S_{e,f}(A)=\{(i,\mathbf1_{\{i\in A\}}):i\in O\}\ \cup\ \{(f,0),(f,1)\}.$$
--   Thus pair $e$ is empty, pair $f$ is full, and every ordinary pair has one chosen label. Only membership of $A$ on $O$ affects the result. This bundle supplies scan and state-encoding helpers; it does not itself assert goodness of initialized multipliers or concrete-machine cost bounds.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/InitialMultipliersGood.lean#L12-L23

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

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.InitialMultipliersGood

open CountingMatroid.Model CountingMatroid.Analysis
open CountingMatroid.Program CountingMatroid.Model.Operations

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














/-- INTERNAL: Ordinary pairs in one defect class exclude its empty and
full pair. They carry the n-2 free Boolean choices. -/
 def ordinaryPairs {n : ℕ} (index : DefectIndex n) : Finset (Fin n) :=
  (Finset.univ.erase index.emptyPair).erase index.fullPair

/-- INTERNAL: Encode a subset of the ordinary pairs by choosing y on that
subset and x on its complement, with both elements at the full pair. -/
 def defectChoiceState {n : ℕ} (index : DefectIndex n)
    (A : Finset (Fin n)) : PairedSet n :=
  (ordinaryPairs index).image (fun i => (i, decide (i ∈ A))) ∪
    {(index.fullPair, false), (index.fullPair, true)}














end CountingMatroid.Analysis.InitialMultipliersGood

end


