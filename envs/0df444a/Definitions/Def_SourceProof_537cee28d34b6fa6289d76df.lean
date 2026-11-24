-- Prove2me | Definitions.Def_SourceProof_537cee28d34b6fa6289d76df
-- name    : SourceProof_537cee28d34b6fa6289d76df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:59:17.062378+00:00
-- url     : https://prove2.me/theorems/9705e2fa-1515-4186-a8ec-1bbaead8ef1e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.quadraticVariationSum_real_ge

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_e1f3ecca529106853c30fa13
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Poisson square-increment sums converge to the actual count

For every finite partition, the square sum exceeds the count and its mean
excess is exactly `rate^2 * sum gap^2`. Thus arbitrary vanishing meshes give
L1 and probability convergence, without assuming unit jumps or a bracket.
-/

@[expose] public section

open MeasureTheory Filter Finset StochLean
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate T : ℝ≥0}

namespace IsPoissonProcess
theorem _root_.Prove2MeSourceProof.h_537cee28d34b6fa6289d76df
    (hN : IsPoissonProcess N rate P) (π : TimePartition T) :
    ∀ᵐ ω ∂P, (N T ω : ℝ) ≤ quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) := by
  filter_upwards [hN.monotonePaths, hN.initial] with ω hm h0
  have he : (N T ω : ℝ) = ∑ i, π.increment (fun s ↦ (N s ω : ℝ)) i := by
    rw [(_root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 π), h0, Nat.cast_zero, sub_zero]
  rw [he]
  apply sum_le_sum
  intro i _
  have hn := hm ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)
  change (N (π.right i) ω : ℝ) - N (π.left i) ω ≤
    ((N (π.right i) ω : ℝ) - N (π.left i) ω) ^ 2
  rw [← Nat.cast_sub hn]
  set k := N (π.right i) ω - N (π.left i) ω
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
end IsPoissonProcess

end ProbabilityTheory


