-- Prove2me | Definitions.Def_SourceProof_5e98228d861a52876e6b957f
-- name    : SourceProof_5e98228d861a52876e6b957f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:59.667091+00:00
-- url     : https://prove2.me/theorems/e122a8c7-39e6-5482-bb75-a2e11271b884
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.integral_abs_quadraticVariationSum_real_error_le

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_3a8d856e0bc079367e823342
import Definitions.Def_SourceProof_537cee28d34b6fa6289d76df
import Definitions.Def_SourceProof_62c96c8989b32380830efb77
import Definitions.Def_SourceProof_fceeaea9b85fa3df900b7ecb
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
theorem _root_.Prove2MeSourceProof.h_5e98228d861a52876e6b957f
    (hN : IsPoissonProcess N rate P) (π : TimePartition T) :
    (∫ ω, |quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) - N T ω| ∂P) ≤
      (rate : ℝ) ^ 2 * T * π.mesh := by
  have he : (∫ ω, |StochLean.quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) - N T ω| ∂P) =
      (∫ ω, (StochLean.quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) - N T ω) ∂P) := by
    apply integral_congr_ae
    filter_upwards [(_root_.Prove2MeSourceProof.h_537cee28d34b6fa6289d76df hN) π] with ω hω
    exact abs_of_nonneg (sub_nonneg.mpr hω)
  rw [he, (_root_.Prove2MeSourceProof.h_fceeaea9b85fa3df900b7ecb hN)]
  calc
    (rate : ℝ) ^ 2 * ∑ i, (π.gap i : ℝ) ^ 2 ≤
        (rate : ℝ) ^ 2 * ∑ i, (π.gap i : ℝ) * π.mesh := by
      simp only [pow_two]
      gcongr with i
      exact_mod_cast (_root_.Prove2MeSourceProof.h_62c96c8989b32380830efb77 π) i
    _ = (rate : ℝ) ^ 2 * T * π.mesh := by rw [← sum_mul, (_root_.Prove2MeSourceProof.h_3a8d856e0bc079367e823342 π), mul_assoc]
end IsPoissonProcess

end ProbabilityTheory


