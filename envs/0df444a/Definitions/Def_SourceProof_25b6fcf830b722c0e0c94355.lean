-- Prove2me | Definitions.Def_SourceProof_25b6fcf830b722c0e0c94355
-- name    : SourceProof_25b6fcf830b722c0e0c94355
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:52.463895+00:00
-- url     : https://prove2.me/theorems/79ab27d0-fc2e-572e-bba2-090a15fa1100
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.tendstoInMeasure_quadraticVariationSum_real

import Definitions.Def_SourceProof_5a7cb6f0c408faca4bc77360
import Definitions.Def_SourceProof_5e98228d861a52876e6b957f
import Definitions.Def_SourceProof_f2e2f84d4d570c2c1096a87c

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
theorem _root_.Prove2MeSourceProof.h_25b6fcf830b722c0e0c94355
    (hN : IsPoissonProcess N rate P) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ quadraticVariationSum (π n) (fun s ↦ (N s ω : ℝ)))
      atTop (fun ω ↦ (N T ω : ℝ)) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
    (fun n ↦ ((_root_.Prove2MeSourceProof.h_f2e2f84d4d570c2c1096a87c hN) (π n)).aestronglyMeasurable)
    ((_root_.Prove2MeSourceProof.h_5a7cb6f0c408faca4bc77360 hN) T).aestronglyMeasurable
  have hi (n : ℕ) := ((_root_.Prove2MeSourceProof.h_f2e2f84d4d570c2c1096a87c hN) (π n)).sub ((_root_.Prove2MeSourceProof.h_5a7cb6f0c408faca4bc77360 hN) T)
  have hr : Tendsto
      (fun n ↦ ∫ ω, |StochLean.quadraticVariationSum (π n) (fun s ↦ (N s ω : ℝ)) - N T ω| ∂P)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _)
      (fun n ↦ (_root_.Prove2MeSourceProof.h_5e98228d861a52876e6b957f hN) (π n))
    simpa only [mul_zero] using hmesh.const_mul ((rate : ℝ) ^ 2 * T)
  simp_rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
end IsPoissonProcess

end ProbabilityTheory


