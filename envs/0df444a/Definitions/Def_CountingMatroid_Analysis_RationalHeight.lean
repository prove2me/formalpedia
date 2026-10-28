-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RationalHeight
-- name    : CountingMatroid_Analysis_RationalHeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:43:28.342851+00:00
-- url     : https://prove2.me/theorems/6601eb71-8d2a-4748-8ac2-72544d9e4576
-- title:
--   Component height of a reduced rational number
-- statement:
--   Let $q=u/v\in\mathbb Q$ be in canonical reduced form, with integer numerator $u$ and positive natural denominator $v$. Define
--   $$H(q)=\max\!\left(\lfloor\log_2|u|\rfloor,\lfloor\log_2v\rfloor\right)+1,$$
--   using the natural-number logarithm convention $\log_2 0=0$. This function is `rationalHeight`. It records the larger of the numerator-magnitude and denominator binary lengths, with one digit assigned to zero. The quantity is used as an arithmetic-size parameter for rational accumulators; growth inequalities are separate results.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RationalHeight.lean#L8-L11

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

namespace CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model

/-- INTERNAL: The larger component length supports additive growth under rational addition.
TEXLINE: main.tex:1362-1378 -/
def rationalHeight (q : ℚ) : ℕ :=
  max q.num.natAbs.log2 q.den.log2 + 1








end CountingMatroid.Analysis.RationalHeight

end


