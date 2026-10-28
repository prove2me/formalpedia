-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
-- name    : CountingMatroid_Analysis_ScheduleDrawTrialsBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:03:37.738616+00:00
-- url     : https://prove2.me/theorems/04d838fe-9266-474e-883d-384dc4760c57
-- title:
--   The schedule's draw-cap inequality
-- statement:
--   For an annealing schedule $s$, the predicate $\operatorname{drawCapGood}(s)$ is the natural-number inequality
--   $$
--   s.\mathrm{drawTrials}\le
--   \log_2\!\left(3\,s.L\bigl(s.\mathrm{restartCap}+s.\mathrm{observations}\bigr)\right)+9.
--   $$
--   Here $s.L$ is the phase count, $\mathrm{restartCap}$ the attempt cap, $\mathrm{observations}$ the observation count, and $\mathrm{drawTrials}$ the rejection-draw trial limit. The logarithm is the natural-number base-two logarithm, including its value zero at zero. The predicate records this inequality rather than proving it for every schedule.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleDrawTrialsBridge.lean#L52-L54

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
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleDrawTrialsBridge

open CountingMatroid.Model
open CountingMatroid.Model.Operations





/-- INTERNAL: The field relation needed for the schedule trial bound. -/
 def drawCapGood (s : AnnealingSchedule) : Prop :=
  s.drawTrials ≤ (3 * s.L * (s.restartCap + s.observations)).log2 + 9







end CountingMatroid.Analysis.ScheduleDrawTrialsBridge

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · peeled the schedule's charged binds and bounded the final trial counter by its loop cap; full schedule reduction stalled.
-/

end


