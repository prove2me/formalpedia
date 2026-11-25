-- Prove2me | Definitions.Def_SourceProof_3dc6ba7e718cde1be7f01e13
-- name    : SourceProof_3dc6ba7e718cde1be7f01e13
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:39.199127+00:00
-- url     : https://prove2.me/theorems/0213c299-c4fe-4c5a-9906-e58530cec747
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.exponent_triplet

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F019
import Definitions.Def_SourceProof_01d024834e530b53330407ce
import Definitions.Def_SourceProof_a0955a4e2c3724551cc21f56
import Definitions.Def_SourceProof_c3b700cf3e07c09b0f6a6eee

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

end LevyTriplet

namespace CompoundPoisson


theorem _root_.Prove2MeSourceProof.h_3dc6ba7e718cde1be7f01e13 (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) (t : ℝ) :
    (triplet r μ hzero).exponent t =
      (r : ℂ) * (charFun (μ : Measure ℝ) t - 1) := by
  have htruncμ : Integrable ProbabilityTheory.levyTruncation (μ : Measure ℝ) :=
    _root_.Prove2MeSourceProof.h_01d024834e530b53330407ce _
  have hlevyμ : Integrable (ProbabilityTheory.levyExponentIntegrand t) (μ : Measure ℝ) :=
    (_root_.Prove2MeSourceProof.h_c3b700cf3e07c09b0f6a6eee (_root_.Prove2MeSourceProof.h_a0955a4e2c3724551cc21f56 hzero)) t
  have hcorrμ : Integrable
      (fun x => (((t * ProbabilityTheory.levyTruncation x : ℝ) : ℂ) * Complex.I)) (μ : Measure ℝ) :=
    ((htruncμ.const_mul t).ofReal.mul_const Complex.I)
  have hpoint (x : ℝ) :
      ProbabilityTheory.levyExponentIntegrand t x + (((t * ProbabilityTheory.levyTruncation x : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) - 1 := by
    rw [Real.inner_apply]
    unfold ProbabilityTheory.levyExponentIntegrand
    have harg : (((t * x : ℝ) : ℂ) * Complex.I) =
        (((x * t : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [harg]
    ring
  have hchar : Integrable
      (fun x => Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I)) (μ : Measure ℝ) := by
    apply ((hlevyμ.add hcorrμ).add (integrable_const 1)).congr
    exact ae_of_all _ fun x => by
      change ProbabilityTheory.levyExponentIntegrand t x +
          (((t * ProbabilityTheory.levyTruncation x : ℝ) : ℂ) * Complex.I) + 1 = _
      rw [hpoint x]
      ring
  have hsum :
      (∫ x, ProbabilityTheory.levyExponentIntegrand t x ∂(μ : Measure ℝ)) +
          (∫ x, (((t * ProbabilityTheory.levyTruncation x : ℝ) : ℂ) * Complex.I) ∂(μ : Measure ℝ)) =
        (∫ x, Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) ∂(μ : Measure ℝ)) - 1 := by
    rw [← integral_add hlevyμ hcorrμ]
    rw [integral_congr_ae (ae_of_all _ hpoint)]
    rw [integral_sub hchar (integrable_const 1)]
    simp
  have hcast :
      (∫ x, ((t * ProbabilityTheory.levyTruncation x : ℝ) : ℂ) ∂(μ : Measure ℝ)) =
        ((∫ x, t * ProbabilityTheory.levyTruncation x ∂(μ : Measure ℝ) : ℝ) : ℂ) :=
    integral_ofReal
  have hreal :
      (∫ x, t * ProbabilityTheory.levyTruncation x ∂(μ : Measure ℝ)) =
        t * ∫ x, ProbabilityTheory.levyTruncation x ∂(μ : Measure ℝ) :=
    integral_const_mul _ _
  simp only [ProbabilityTheory.LevyTriplet.exponent, ProbabilityTheory.CompoundPoisson.triplet, NNReal.coe_zero, zero_div, zero_mul,
    Complex.ofReal_zero, neg_zero, zero_add]
  rw [MeasureTheory.integral_smul_nnreal_measure,
    MeasureTheory.integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [charFun_apply]
  push_cast
  rw [← hsum]
  rw [integral_mul_const, hcast, hreal]
  push_cast
  simp only [smul_eq_mul]
  rw [Complex.ofReal_mul]
  ring
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


