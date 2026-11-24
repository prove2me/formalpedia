-- Prove2me | Definitions.Def_SourceProof_7f578536210b5439b655b536
-- name    : SourceProof_7f578536210b5439b655b536
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:20.140467+00:00
-- url     : https://prove2.me/theorems/633e338c-6fed-4fdc-a704-73cbb1e0030a
-- title:
--   StochLean source theorem: ProbabilityTheory.norm_affineDriftIntegrand_le

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F002
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


theorem _root_.Prove2MeSourceProof.h_7f578536210b5439b655b536 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖affineDriftIntegrand a x‖ ≤ max 1 (a ^ 2) * (levyIntegrand x).toReal := by
  by_cases hx : |x| < 1
  · rw [_root_.Prove2MeSourceProof.h_3dc2531cd43d82b26dd002fe hx]
    rw [ProbabilityTheory.affineDriftIntegrand, _root_.Prove2MeSourceProof.h_7e961aa121c5246639f2cd81 hx]
    by_cases hax : |a * x| < 1
    · rw [_root_.Prove2MeSourceProof.h_7e961aa121c5246639f2cd81 hax]
      simp [sq_nonneg]
    · rw [_root_.Prove2MeSourceProof.h_a9854b69af6573818338f60b (le_of_not_gt hax)]
      simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos ha]
      have hone : 1 ≤ a * |x| := by
        simpa [abs_mul, abs_of_pos ha] using le_of_not_gt hax
      have hself : a * |x| ≤ (a * |x|) ^ 2 := by nlinarith
      have hmain : a * |x| ≤ a ^ 2 * x ^ 2 := by
        calc
          a * |x| ≤ (a * |x|) ^ 2 := hself
          _ = a ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
      exact hmain.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg x))
  · rw [_root_.Prove2MeSourceProof.h_be9018e17092c495219a7cc4 (le_of_not_gt hx)]
    rw [ProbabilityTheory.affineDriftIntegrand, _root_.Prove2MeSourceProof.h_a9854b69af6573818338f60b (le_of_not_gt hx)]
    simp only [mul_zero, sub_zero, Real.norm_eq_abs]
    by_cases hax : |a * x| < 1
    · rw [_root_.Prove2MeSourceProof.h_7e961aa121c5246639f2cd81 hax]
      simpa using (le_of_lt hax).trans (le_max_left (1 : ℝ) (a ^ 2))
    · rw [_root_.Prove2MeSourceProof.h_a9854b69af6573818338f60b (le_of_not_gt hax)]
      simp
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


