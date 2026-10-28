-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ScheduleAbortBudget
-- name    : CountingMatroid_Analysis_ScheduleAbortBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:03:49.197774+00:00
-- url     : https://prove2.me/theorems/5cb173a5-2499-4bce-8ac9-56fabd9314e7
-- title:
--   Doubling step and draw-trial threshold
-- statement:
--   For a target $T\in\mathbb N$ and accumulator $(d,P)\in\mathbb N^2$, the charged doubling step returns
--   $$\operatorname{step}_T(d,P)=\begin{cases}\operatorname{some}(d+1,2P)&P<T,\\\operatorname{none}&P\ge T.\end{cases}$$
--   An additional loop index is ignored. The comparison, increment, and multiplication use the source's abstract operation charges. For a schedule with phase count $L$, restart cap $R$, observation count $N$, and draw-trial cap $D$, the draw-fields predicate is
--   $$32\bigl(3L(R+N)\bigr)\le2^D.$$
--   This records a numerical rejection-budget condition; neither its satisfaction by an arbitrary schedule nor termination of doubling from an arbitrary accumulator is asserted.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleAbortBudget.lean#L17-L25

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

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
The concrete doubling search meets the capped-draw probability threshold.
The schedule budget combines its per-phase draw terms with the restart-tail
term. These are deterministic numerical bounds; operational event bounds
are supplied separately by the conditional abort modules.
-/

namespace CountingMatroid.Analysis.ScheduleAbortBudget

open CountingMatroid.Model CountingMatroid.Model.Operations
open Arlib.Computation (Charged)

/-- INTERNAL: One charged iteration of the actual draw-trial doubling search. -/
 def doublingStep (target : ℕ) (acc : ℕ × ℕ) (_ : ℕ) :
    Charged Op Cell (Option (ℕ × ℕ)) := do
  let needsStep ← lessThan acc.2 target
  if needsStep then
    let d ← successor acc.1
    let power ← natMul acc.2 2
    pure (some (d, power))
  else pure none









/-- INTERNAL: The fields relevant to the rejection probability threshold. -/
 def drawFieldsGood (s : AnnealingSchedule) : Prop :=
  32 * (3 * s.L * (s.restartCap + s.observations)) ≤ 2 ^ s.drawTrials











end CountingMatroid.Analysis.ScheduleAbortBudget

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r24 · proved · the actual capped doubling search meets `32*M ≤ 2^D`; positive phase count and the charged schedule tail give the combined `3/[32(L+1)]` abort budget. Direct field reduction was replaced by continuation-property propagation and separate numerical arithmetic.
-/

end


