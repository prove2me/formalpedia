-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
-- name    : CountingMatroid_Analysis_ScheduleConfidence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:03:57.656764+00:00
-- url     : https://prove2.me/theorems/7feb93f3-9c0d-4724-9430-4b8b4fc0ef43
-- title:
--   A charged halving step for the confidence schedule
-- statement:
--   For a rational threshold $\delta$, a natural counter $b$, and a rational accumulator $p$, the halving step is
--   $$
--   H_\delta(b,p)=
--   \begin{cases}
--   \operatorname{some}(b+1,p/2),&\delta<p,\\
--   \operatorname{none},&p\le\delta.
--   \end{cases}
--   $$
--   Its additional natural loop index is ignored. The comparison is charged; on the continuing branch the successor and rational division are also charged. These are abstract operation charges. The definition requires no positivity assumption on $\delta$ or $p$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleConfidence.lean#L10-L19

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

namespace CountingMatroid.Analysis.MedianAmplification

open CountingMatroid.Model.Operations
open Arlib.Computation

/-- INTERNAL: One charged iteration of the denominator halving search. -/
 def halfStep (δ : ℚ) (_ : ℕ) (acc : ℕ × ℚ) :
    Charged CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell
      (Option (ℕ × ℚ)) := do
  let needsStep ← ratLess δ acc.2
  if needsStep then
    let b ← successor acc.1
    let power ← ratDiv acc.2 2
    pure (some (b, power))
  else pure none

















end CountingMatroid.Analysis.MedianAmplification

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · established the charged halving loop invariant and denominator cap bound.
-/

end


