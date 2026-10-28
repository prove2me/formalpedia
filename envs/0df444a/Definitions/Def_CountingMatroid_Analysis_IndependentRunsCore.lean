-- Prove2me | Definitions.Def_CountingMatroid_Analysis_IndependentRunsCore
-- name    : CountingMatroid_Analysis_IndependentRunsCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:42:56.075792+00:00
-- url     : https://prove2.me/theorems/7c3494c7-dbea-497b-a477-be373feee121
-- title:
--   The law of a list of independent repeated samples
-- statement:
--   Let $\alpha$ be a type and let $q$ be a probability mass function on $\alpha$. Define $\operatorname{independentRuns}(q,m)$, for $m\in\mathbb N$, as a probability mass function on finite lists of elements of $\alpha$ by $$\operatorname{independentRuns}(q,0)=\delta_{[]},$$ $$\operatorname{independentRuns}(q,m+1)=\operatorname{bind}_{x\sim q}\operatorname{bind}_{xs\sim\operatorname{independentRuns}(q,m)}\delta_{x::xs}.$$ Here $\delta$ denotes a point mass, bind denotes sampling followed by the indicated conditional distribution, and $x::xs$ prepends $x$ to the list. Thus each recursive step samples one new value from $q$ and prepends it to a recursively sampled list.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IndependentRunsCore.lean#L7-L13

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Interface_Pseudocode
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

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

/-- INTERNAL: Recursively sample the independent outputs used by the median. -/
noncomputable def independentRuns {α : Type} (q : PMF α) : ℕ → PMF (List α)
  | 0 => pure []
  | m + 1 => do
      let x ← q
      let xs ← independentRuns q m
      pure (x :: xs)



end CountingMatroid.Analysis.MedianAmplification

end


