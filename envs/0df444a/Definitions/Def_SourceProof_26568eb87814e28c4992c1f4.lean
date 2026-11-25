-- Prove2me | Definitions.Def_SourceProof_26568eb87814e28c4992c1f4
-- name    : SourceProof_26568eb87814e28c4992c1f4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:20.222867+00:00
-- url     : https://prove2.me/theorems/a6b74b26-d42b-4898-9858-2bcb985fd5d1
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.charFun_law

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F000
import Definitions.Def_SourceProof_6f80af65b6d22255a398a6e4
import Definitions.Def_SourceProof_afa4a77c82348c083f81d8eb
import Definitions.Def_SourceProof_f3db01ce3d4c266614f122be

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Compound Poisson laws

The construction is a genuine probability mixture: draw a Poisson count and then use the
corresponding convolution power of the jump law.  The zero-rate branch is proved explicitly and
does not depend on division by the intensity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

namespace CompoundPoisson

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

section CharacteristicFunction


theorem _root_.Prove2MeSourceProof.h_26568eb87814e28c4992c1f4 (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (law r μ : Measure ℝ) t =
      Complex.exp ((r : ℂ) * (charFun (μ : Measure ℝ) t - 1)) := by
  rw [charFun_apply, _root_.Prove2MeSourceProof.h_afa4a77c82348c083f81d8eb, poissonMeasure]
  rw [Measure.bind_sum]
  · rw [integral_sum_measure]
    · have hcoeff (n : ℕ) :
          (ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial)).toReal =
            Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial :=
        ENNReal.toReal_ofReal (by positivity)
      simp_rw [Measure.bind_smul, Measure.dirac_bind (_root_.Prove2MeSourceProof.h_f3db01ce3d4c266614f122be μ),
        MeasureTheory.integral_smul_measure, hcoeff, ← charFun_apply, _root_.Prove2MeSourceProof.h_6f80af65b6d22255a398a6e4]
      change (∑' n : ℕ,
          ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial : ℝ) : ℂ) *
            charFun (μ : Measure ℝ) t ^ n) = _
      calc
        ∑' n : ℕ,
            ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial : ℝ) : ℂ) *
              charFun (μ : Measure ℝ) t ^ n =
            (Real.exp (-r) : ℂ) *
              ∑' n : ℕ, (((r : ℂ) * charFun (μ : Measure ℝ) t) ^ n /
                n.factorial) := by
          rw [← tsum_mul_left]
          congr 1
          funext n
          push_cast
          rw [mul_pow]
          ring
        _ = (Real.exp (-r) : ℂ) *
            Complex.exp ((r : ℂ) * charFun (μ : Measure ℝ) t) := by
          rw [(NormedSpace.expSeries_div_hasSum_exp
            ((r : ℂ) * charFun (μ : Measure ℝ) t)).tsum_eq, ← Complex.exp_eq_exp_ℂ]
        _ = Complex.exp ((r : ℂ) * (charFun (μ : Measure ℝ) t - 1)) := by
          rw [Complex.ofReal_exp, ← Complex.exp_add]
          push_cast
          congr 1
          ring
    · letI : IsFiniteMeasure
          (Measure.sum fun i =>
            (fun n => (MeasureTheory.ProbabilityMeasure.convPow μ n : Measure ℝ)) ∘ₘ
              (ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ i / i.factorial) •
                Measure.dirac i)) := by
        rw [← Measure.bind_sum]
        · rw [← poissonMeasure, ← _root_.Prove2MeSourceProof.h_afa4a77c82348c083f81d8eb]
          infer_instance
        · exact (_root_.Prove2MeSourceProof.h_f3db01ce3d4c266614f122be μ).aemeasurable
      exact (integrable_const (1 : ℂ)).mono (by fun_prop) <|
        ae_of_all _ fun x => by
          rw [Complex.norm_exp]
          simp [mul_comm]
  · exact (_root_.Prove2MeSourceProof.h_f3db01ce3d4c266614f122be μ).aemeasurable
end CharacteristicFunction

end CompoundPoisson

end ProbabilityTheory


