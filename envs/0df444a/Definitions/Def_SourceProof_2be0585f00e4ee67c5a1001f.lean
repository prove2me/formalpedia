-- Prove2me | Definitions.Def_SourceProof_2be0585f00e4ee67c5a1001f
-- name    : SourceProof_2be0585f00e4ee67c5a1001f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:58.919777+00:00
-- url     : https://prove2.me/theorems/47fe351a-a7e4-464e-8051-8687abcb55a3
-- title:
--   StochLean source theorem: ProbabilityTheory.norm_levyExponentIntegrand_le

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001
import Definitions.Def_SourceProof_3dc2531cd43d82b26dd002fe
import Definitions.Def_SourceProof_7e961aa121c5246639f2cd81
import Definitions.Def_SourceProof_a9854b69af6573818338f60b
import Definitions.Def_SourceProof_be9018e17092c495219a7cc4

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


theorem _root_.Prove2MeSourceProof.h_2be0585f00e4ee67c5a1001f (t x : ℝ) :
    ‖levyExponentIntegrand t x‖ ≤ levyExponentBound t * (levyIntegrand x).toReal := by
  by_cases hx : |x| < 1
  · rw [_root_.Prove2MeSourceProof.h_3dc2531cd43d82b26dd002fe hx]
    have htrunc : ProbabilityTheory.levyTruncation x = x := _root_.Prove2MeSourceProof.h_7e961aa121c5246639f2cd81 hx
    rw [ProbabilityTheory.levyExponentIntegrand, htrunc]
    by_cases hz : ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ≤ 1
    · have hTaylor := Complex.norm_exp_sub_one_sub_id_le hz
      have htx : ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 = t ^ 2 * x ^ 2 := by
        simp only [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
        rw [Real.norm_eq_abs, abs_mul, mul_pow, sq_abs, sq_abs]
      calc
        ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            ((t * x : ℝ) : ℂ) * Complex.I‖ ≤
            ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 := hTaylor
        _ = t ^ 2 * x ^ 2 := htx
        _ ≤ ProbabilityTheory.levyExponentBound t * x ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
          unfold ProbabilityTheory.levyExponentBound
          nlinarith [sq_nonneg t, abs_nonneg t]
    · have hz' : 1 < |t * x| := by
        simpa [abs_mul] using lt_of_not_ge hz
      have hsq : 1 < t ^ 2 * x ^ 2 := by
        calc
          (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
          _ < |t * x| ^ 2 := (sq_lt_sq₀ zero_le_one (abs_nonneg (t * x))).mpr hz'
          _ = t ^ 2 * x ^ 2 := by rw [abs_mul, mul_pow, sq_abs, sq_abs]
      have hrough :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              ((t * x : ℝ) : ℂ) * Complex.I‖ ≤ 2 + |t| := by
        calc
          _ ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ +
              ‖((t * x : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
          _ ≤ (1 + 1) + |t * x| := by
            gcongr
            · calc
                ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
                    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ :=
                  norm_sub_le _ _
                _ = 1 + 1 := by
                  rw [Complex.norm_exp]
                  simp [Complex.mul_re]
            · simp
          _ ≤ 2 + |t| := by
            rw [abs_mul]
            nlinarith [mul_le_mul_of_nonneg_left hx.le (abs_nonneg t)]
      calc
        _ ≤ 2 + |t| := hrough
        _ ≤ (2 + |t|) * (t ^ 2 * x ^ 2) := by
          exact le_mul_of_one_le_right (by positivity) hsq.le
        _ = ((2 + |t|) * t ^ 2) * x ^ 2 := by ring
        _ ≤ ProbabilityTheory.levyExponentBound t * x ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
          unfold ProbabilityTheory.levyExponentBound
          nlinarith [sq_nonneg t, abs_nonneg t]
  · have hx' : 1 ≤ |x| := le_of_not_gt hx
    rw [_root_.Prove2MeSourceProof.h_be9018e17092c495219a7cc4 hx']
    have htrunc : ProbabilityTheory.levyTruncation x = 0 := _root_.Prove2MeSourceProof.h_a9854b69af6573818338f60b hx'
    rw [ProbabilityTheory.levyExponentIntegrand, htrunc]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, sub_zero, mul_one]
    calc
      ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re]
        norm_num
      _ ≤ ProbabilityTheory.levyExponentBound t := by
        unfold ProbabilityTheory.levyExponentBound
        nlinarith [mul_nonneg (by positivity : 0 ≤ 3 + |t|) (sq_nonneg t)]
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


