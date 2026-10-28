-- Prove2me | Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
-- name    : CountingMatroid_Analysis_AnnealingPartitionDrift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:27.817034+00:00
-- url     : https://prove2.me/theorems/94bbf53a-810c-4e0f-9993-122db40c523b
-- title:
--   The setup cooling factor retains at least half after one ground-size block
-- statement:
--   Let $n\in\mathbb N$ be positive and let the rational input parameters satisfy $0<\varepsilon<1$ and $0<\delta<1$. For the cooling factor $\rho$ returned by the setup schedule, the included helper theorem states
--   $$0<\rho\leq1,\qquad \rho^n\geq\frac12.$$
--   The setup value is $\rho=1-\frac1{2n}$. Positivity follows from $n\geq1$, and Bernoulli's inequality gives
--   $$\left(1-\frac1{2n}\right)^n\geq1-\frac{n}{2n}=\frac12.$$
--   The result is arithmetic about the actual schedule value and requires no matroid, rank, or oracle promise.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/AnnealingPartitionDrift.lean#L10-L45

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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.AnnealingPartitionDrift

open CountingMatroid.Model

/-- PAPER: main.tex:1131-1145
The schedule's cooling factor is positive, at most one, and its nth power
is at least one half. This uses Bernoulli's inequality, not a rank promise. -/
theorem schedule_power_lower (n : ℕ) (p : InputParams) (hn : 0 < n) :
    let ρ := (CountingMatroid.Interface.Pseudocode.setup n p).ρ
    0 < ρ ∧ ρ ≤ 1 ∧ (1 / 2 : ℚ) ≤ ρ ^ n := by
  have hρ : (CountingMatroid.Interface.Pseudocode.setup n p).ρ =
      1 - 1 / (2 * (n : ℚ)) := by
    simp only [CountingMatroid.Interface.Pseudocode.setup,
      CountingMatroid.Program.schedule, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure,
      CountingMatroid.Model.Operations.ratDiv,
      CountingMatroid.Model.Operations.ratSub,
      CountingMatroid.Model.Operations.ratOfNat,
      CountingMatroid.Model.Operations.natMul,
      Arlib.Computation.Charged.val_op,
      Arlib.Computation.Charged.val_opMany]
    norm_cast
  dsimp only
  rw [hρ]
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℚ) < 2 * n := by positivity
  have hinv : (1 : ℚ) / (2 * n) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hpos : (0 : ℚ) < 1 - 1 / (2 * n) := by linarith
  have hle : (1 - 1 / (2 * (n : ℚ))) ≤ 1 :=
    sub_le_self _ (by positivity)
  refine ⟨hpos, hle, ?_⟩
  have hbern := one_add_mul_sub_le_pow
    (show (-1 : ℚ) ≤ 1 - 1 / (2 * n) by linarith) n
  have heq : (1 : ℚ) + n * ((1 - 1 / (2 * n)) - 1) = 1 / 2 := by
    field_simp
    ring
  rwa [heq] at hbern











end CountingMatroid.Analysis.AnnealingPartitionDrift

end


