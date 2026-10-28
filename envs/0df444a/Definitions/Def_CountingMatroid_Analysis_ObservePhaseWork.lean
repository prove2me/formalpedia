-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
-- name    : CountingMatroid_Analysis_ObservePhaseWork
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:48:27.349342+00:00
-- url     : https://prove2.me/theorems/95a73369-1811-4a43-9e3c-aede8f9d31e8
-- title:
--   Polynomial budget for recording an observation
-- statement:
--   For natural numbers $n,R,H$, define $$\begin{aligned}\operatorname{recordBudget}(n,R,H)={}&n(4n+3)+1+3(n^2+2)+8(n+1)^3+1\\&+n(4+nR)^2+(2H+2+4+nR)^2.\end{aligned}$$ In the intended observation-cost application, $n$ is the number of paired indices, $R$ is the rational encoding length of the annealing multiplier $\rho$, and $H$ bounds the component height of the current rational numerator accumulator. The definition itself accepts arbitrary natural $n,R,H$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ObservePhaseWork.lean#L13-L17

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
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
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

section


set_option autoImplicit false
namespace CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: An observation's branch costs, including the height-bounded
rational accumulator addition. TEXLINE: main.tex:1362-1378 -/
def recordBudget (n R H : ℕ) : ℕ :=
  n * (4 * n + 3) + 1 + 3 * (n * n + 2) + 8 * (n + 1) ^ 3 + 1 +
    n * (4 + n * R) ^ 2 + (2 * H + 2 + (4 + n * R)) ^ 2






end CountingMatroid.Analysis.ObservePhaseWork

end


