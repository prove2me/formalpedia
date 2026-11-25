-- Prove2me | Definitions.Def_SourceProof_aad21b11daf6930ca2e3b912
-- name    : SourceProof_aad21b11daf6930ca2e3b912
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:59.104369+00:00
-- url     : https://prove2.me/theorems/79b3d87d-65d4-4360-81d6-334d992a1ab8
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.charFun_secondDifferenceMeasure

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F009
import Definitions.Def_SourceProof_ad0628f973de439b357972c1
import Definitions.Def_SourceProof_b4d891d3664459c406f9bd64

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

theorem _root_.Prove2MeSourceProof.h_aad21b11daf6930ca2e3b912 (η : LevyTriplet) (s t : ℝ) :
    charFun (secondDifferenceMeasure η s) t =
      -(η.exponent (t + s) + η.exponent (t - s) - 2 * η.exponent t) := by
  have hdirac : Integrable (fun x : ℝ =>
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (Measure.dirac 0) := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) (ae_of_all _ fun x => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
      norm_num)
  have hscaled := hdirac.smul_measure
    (c := ENNReal.ofReal ((η.gaussianVariance : ℝ) * s ^ 2)) ENNReal.ofReal_ne_top
  have hweighted : Integrable
      (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (ProbabilityTheory.LevyTriplet.weightedJumpMeasure η s) := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) (ae_of_all _ fun x => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
      norm_num)
  rw [_root_.Prove2MeSourceProof.h_b4d891d3664459c406f9bd64, charFun_apply_real,
    ProbabilityTheory.LevyTriplet.secondDifferenceMeasure, integral_add_measure]
  · rw [integral_smul_measure, integral_dirac]
    have hcf : (∫ x, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
        ∂ProbabilityTheory.LevyTriplet.weightedJumpMeasure η s) = charFun (ProbabilityTheory.LevyTriplet.weightedJumpMeasure η s) t := by
      rw [charFun_apply_real]
    rw [hcf, _root_.Prove2MeSourceProof.h_ad0628f973de439b357972c1]
    simp only [ENNReal.toReal_ofReal (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)),
      zero_mul, Complex.ofReal_zero, Complex.exp_zero, Complex.real_smul, mul_one]
    push_cast
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
    ring
  · exact hscaled
  · exact hweighted
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


