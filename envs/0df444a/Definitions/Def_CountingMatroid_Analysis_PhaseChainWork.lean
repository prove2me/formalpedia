-- Prove2me | Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
-- name    : CountingMatroid_Analysis_PhaseChainWork
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:47:26.89789+00:00
-- url     : https://prove2.me/theorems/1753fa2a-729a-4614-afcf-2a3bae687e75
-- title:
--   Polynomial charge budget for a capped chain step
-- statement:
--   For natural numbers $n,T,K$, interpreted as a ground-set size, a rejection-trial cap, and a rational-length budget, define
--   $$\begin{aligned}
--   B(n,T,K)={}&2+3\bigl(3+T(3(4K+n+1)+2)\bigr)\\
--   &+2\bigl(2n(2n+3)\bigr)+2(2n+1)\\
--   &+2\bigl(n(4n+3)+1\bigr)\\
--   &+2\bigl(8(n+1)^3+(n+4)K^2+n^2+2\bigr)\\
--   &+16K^2+12K+5.
--   \end{aligned}$$
--   This natural-valued expression is `chainBudget`. It collects the intended branch budgets for bounded draws, paired-label selection and updates, classification, weight computation, and rational acceptance arithmetic. The declaration defines the numerical budget; proving that an execution’s charge is at most this value is a separate theorem.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PhaseChainWork.lean#L264-L271

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
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
section


set_option autoImplicit false
namespace CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope


























/-- INTERNAL: Explicit sum of the worst branch costs of a capped chain step.
TEXLINE: main.tex:1333-1421 -/
def chainBudget (n trials K : ℕ) : ℕ :=
  2 + 3 * (3 + trials * (3 * (4 * K + n + 1) + 2)) +
    2 * (2 * n * (2 * n + 3)) + 2 * (2 * n + 1) +
    2 * (n * (4 * n + 3) + 1) +
    2 * (8 * (n + 1) ^ 3 + (n + 4) * K ^ 2 + n * n + 2) +
    16 * K ^ 2 + 12 * K + 5


end CountingMatroid.Analysis.PhaseChainWork

end


