-- Prove2me | Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
-- name    : CountingMatroid_Analysis_BoundedRunPhaseWork
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:01.061703+00:00
-- url     : https://prove2.me/theorems/a670ba95-811c-420f-84c1-15a315060813
-- title:
--   Common charged-work envelopes for one phase
-- statement:
--   For a natural run-size bound $S$, the observation-accumulator encoding envelope is
--   $$
--   A(S)=2\bigl(1+S(4+S^2+1)\bigr)+2.
--   $$
--   The phase-work envelope adds the component bounds after replacing dimensions and schedule caps by $S$. With $C(S)=\operatorname{chainBudget}(S,S,S^{11})$, $R(S)=\operatorname{recordBudget}(S,S,1+S(4+S^2+1))$, and
--   $$
--   F(S)=\operatorname{finishEntryBudget}
--   \bigl(S,S+4,S^{11}+S^2(4(S+4))+S(4(S+4))\bigr),
--   $$
--   its exact formula is
--   $$
--   \begin{aligned}
--   B(S)={}&S(4+S^2)^2\\
--   &+S(2S+3)+S\bigl(1+S(4+S^2)^2+(S^3+1)
--    +S\bigl(S(C(S)+S(4S+3)+3)\bigr)\bigr)\\
--   &+S^2+1+S(1+C(S)+R(S))\\
--   &+S^2+5+2(S+4)+4(S+4)^2
--    +2(A(S)+3(S+4))^2+S^2F(S)\\
--   &+(S^{11}+A(S)+3(S+4))^2+(2+S^3+1).
--   \end{aligned}
--   $$
--   The auxiliary budget functions are the existing chain-step, observation-record, and multiplier-finishing envelopes. These two definitions only specify numerical bounds in the charged-operation model; they do not themselves prove a runtime inequality or supply a concrete bit implementation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunPhaseWork.lean#L30-L32

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
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
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

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
section


/-!
The full nonoracle-work bound for one bounded annealing phase follows from
proved capped-chain, restart, observation, and finishing cost bounds. Each
bound includes abort paths; the observation and finishing scans carry their
reached rational-size invariants. The explicit sum of these component budgets
is absorbed into `runSize ^ 40`, with the original theorem statement retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Analysis.FinishPhaseWork
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: A common encoding bound for the reached observation accumulator. -/
 def phaseWorkSumBudget (S : ℕ) : ℕ :=
  2 * (1 + S * (4 + S * S + 1)) + 2

/-- INTERNAL: Sum the component work envelopes after replacing all schedule
caps and dimensions by their common run-size bound. TEXLINE: main.tex:1348-1440 -/
 def phaseWorkBudget (S : ℕ) : ℕ :=
  S * (4 + S * S) ^ 2 +
  (S * (2 * S + 3) + S *
    (1 + S * (4 + S * S) ^ 2 + (S * S * S + 1) +
      S * (S * (chainBudget S S (S ^ 11) + S * (4 * S + 3) + 3)))) +
  (S * S + 1 + S *
    (1 + chainBudget S S (S ^ 11) +
      recordBudget S S (1 + S * (4 + S * S + 1)))) +
  (S * S + 5 + 2 * (S + 4) + 4 * (S + 4) ^ 2 +
    2 * (phaseWorkSumBudget S + 3 * (S + 4)) ^ 2 +
    S * S * finishEntryBudget S (S + 4)
      (S ^ 11 + S * S * (4 * (S + 4)) + S * (4 * (S + 4)))) +
  (S ^ 11 + phaseWorkSumBudget S + 3 * (S + 4)) ^ 2 +
  (2 + S * S * S + 1)




end CountingMatroid.Analysis.BoundedRunPhase

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · closed phase_otherSteps_le using proved upstream chain/restart/observation/finishing work lemmas and an explicit polynomial envelope; the earlier extraction blocker is resolved.
* current · blocked · confirmed the upstream cost decomposition and unpacked the input size invariant; existing power/count/height support is downstream of this file, and the uniform-fold probe loses the reached-accumulator size bound. No new proof debt was introduced.
-/

end


