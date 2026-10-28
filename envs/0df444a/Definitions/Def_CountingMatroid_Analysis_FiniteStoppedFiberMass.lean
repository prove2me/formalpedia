-- Prove2me | Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
-- name    : CountingMatroid_Analysis_FiniteStoppedFiberMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:16.017075+00:00
-- url     : https://prove2.me/theorems/2c78ed60-b92e-4fe1-b39f-ec9b61c6b57f
-- title:
--   Defaulted finite tapes and uniform suffix-event mass
-- statement:
--   For a finite Boolean list $b$, define the infinite tape
--   $$t_b(i)=\begin{cases}b_i&i<|b|,\\\mathrm{false}&i\ge|b|.\end{cases}$$
--   Given a fixed Boolean prefix $h$, suffix length $t\in\mathbb N$, and any predicate $A$ on infinite Boolean tapes, define its fair suffix mass by
--   $$\operatorname{fairMass}(h,t,A)=2^{-t}\sum_{b\in\{0,1\}^t}\mathbf1_{A(t_{hb})},$$
--   where $hb$ is concatenation. This is a uniform finite sum with deterministic default bits beyond the list. The predicate need not satisfy a stopping-time, locality, or coverage condition.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteStoppedFiberMass.lean#L12-L13

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic
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
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: The defaulted finite tape associated with a bit list. -/
def finiteTape (bits : List Bool) : ℕ → Bool := fun i => (bits[i]?).getD false

/-- INTERNAL: Uniform mass of an event on the fresh suffix after a fixed head. -/
noncomputable def fairMass (head : List Bool) (t : ℕ) (E : (ℕ → Bool) → Prop) : ℝ := by
  classical
  exact ∑ bits : List.Vector Bool t,
    if E (finiteTape (head ++ bits.val)) then 1 / (2 : ℝ) ^ t else 0

















end CountingMatroid.Analysis.FiniteStoppedFiberMass

end


