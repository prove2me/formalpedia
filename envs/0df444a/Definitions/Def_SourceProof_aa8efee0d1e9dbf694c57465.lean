-- Prove2me | Definitions.Def_SourceProof_aa8efee0d1e9dbf694c57465
-- name    : SourceProof_aa8efee0d1e9dbf694c57465
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:00.027348+00:00
-- url     : https://prove2.me/theorems/9ef38844-880a-479c-95b1-8fed930c56a2
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.secondDifferenceWeight_coe

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F008

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

theorem _root_.Prove2MeSourceProof.h_aa8efee0d1e9dbf694c57465 (s x : ℝ) :
    (secondDifferenceWeight s x : ℝ) = 2 * (1 - Real.cos (s * x)) := by
  unfold ProbabilityTheory.LevyTriplet.secondDifferenceWeight
  rw [show ProbabilityTheory.levyExponentIntegrand s x + ProbabilityTheory.levyExponentIntegrand (-s) x =
      ((2 * (Real.cos (s * x) - 1) : ℝ) : ℂ) by
    simp only [ProbabilityTheory.levyExponentIntegrand, neg_mul, neg_neg]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_neg]
    push_cast
    ring]
  simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonpos]
  · ring
  · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (sub_nonpos.mpr (Real.cos_le_one _))
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


