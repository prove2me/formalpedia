-- Prove2me | Definitions.Def_SourceProof_fceeaea9b85fa3df900b7ecb
-- name    : SourceProof_fceeaea9b85fa3df900b7ecb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:51.546098+00:00
-- url     : https://prove2.me/theorems/19c9d53f-028d-50af-a1e1-0cef3cdf4d83
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.integral_quadraticVariationSum_real_error

import Definitions.Def_SourceProof_282b6183b6c4df22c3f01399
import Definitions.Def_SourceProof_3a8d856e0bc079367e823342
import Definitions.Def_SourceProof_5a7cb6f0c408faca4bc77360
import Definitions.Def_SourceProof_d1737e63a4096f0a9b906985
import Definitions.Def_SourceProof_dc59e39708930ceeee4c5f5a
import Definitions.Def_SourceProof_f2e2f84d4d570c2c1096a87c
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

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
theorem _root_.Prove2MeSourceProof.h_fceeaea9b85fa3df900b7ecb
    (hN : IsPoissonProcess N rate P) (π : TimePartition T) :
    (∫ ω, (quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) - N T ω) ∂P) =
      (rate : ℝ) ^ 2 * ∑ i, (π.gap i : ℝ) ^ 2 := by
  rw [integral_sub ((_root_.Prove2MeSourceProof.h_f2e2f84d4d570c2c1096a87c hN) π) ((_root_.Prove2MeSourceProof.h_5a7cb6f0c408faca4bc77360 hN) T),
    (_root_.Prove2MeSourceProof.h_d1737e63a4096f0a9b906985 hN)]
  simp only [StochLean.quadraticVariationSum]
  have hint (i : Fin π.size) :
      Integrable (fun ω ↦ (π.increment (fun s ↦ (N s ω : ℝ)) i) ^ 2) P :=
    (_root_.Prove2MeSourceProof.h_dc59e39708930ceeee4c5f5a hN) ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)
  rw [integral_finsetSum _ (fun i _ ↦ hint i)]
  have he (i : Fin π.size) : (∫ ω, (π.increment (fun s ↦ (N s ω : ℝ)) i) ^ 2 ∂P) =
      (rate : ℝ) ^ 2 * (π.gap i : ℝ) ^ 2 + (rate : ℝ) * π.gap i := by
    simp only [StochLean.TimePartition.increment]
    rw [(_root_.Prove2MeSourceProof.h_282b6183b6c4df22c3f01399 hN) ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)]
    simp only [StochLean.TimePartition.gap, NNReal.coe_sub ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)]
    ring
  simp_rw [he]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, (_root_.Prove2MeSourceProof.h_3a8d856e0bc079367e823342 π)]
  ring
end IsPoissonProcess

end ProbabilityTheory


