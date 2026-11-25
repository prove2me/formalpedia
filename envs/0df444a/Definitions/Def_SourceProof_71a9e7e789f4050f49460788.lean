-- Prove2me | Definitions.Def_SourceProof_71a9e7e789f4050f49460788
-- name    : SourceProof_71a9e7e789f4050f49460788
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:22:44.976266+00:00
-- url     : https://prove2.me/theorems/c1f6e061-e865-4717-a524-19b52b4eb14c
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.continuous_exponentJump

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_SourceProof_0c6d3685872c502bae901cb3
import Definitions.Def_SourceProof_153d33725319d021bbb878c0
import Definitions.Def_SourceProof_2be0585f00e4ee67c5a1001f
import Definitions.Def_SourceProof_f9b33963924eb7ac5401881f

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


theorem _root_.Prove2MeSourceProof.h_71a9e7e789f4050f49460788 (η : LevyTriplet) :
    Continuous (fun t : ℝ ↦ ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure) := by
  rw [continuous_iff_seqContinuous]
  intro u t hut
  let K : ℝ := |t| + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have huNear : ∀ᶠ n in Filter.atTop, dist (u n) t < 1 := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hut) 1 zero_lt_one
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  have huK : ∀ᶠ n in Filter.atTop, |u n| ≤ K := by
    filter_upwards [huNear] with n hn
    have hdiff : |u n - t| < 1 := by simpa [Real.dist_eq] using hn
    calc
      |u n| = |(u n - t) + t| := by ring_nf
      _ ≤ |u n - t| + |t| := abs_add_le _ _
      _ ≤ K := by dsimp [K]; linarith
  let C : ℝ := ProbabilityTheory.levyExponentBound K
  have hbase : Integrable (fun x ↦ (ProbabilityTheory.levyIntegrand x).toReal) η.jumpMeasure :=
    integrable_toReal_of_lintegral_ne_top _root_.Prove2MeSourceProof.h_0c6d3685872c502bae901cb3.aemeasurable
      (_root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 η.isLevyMeasure_jumpMeasure).ne
  apply tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ C * (ProbabilityTheory.levyIntegrand x).toReal)
  · exact Filter.Eventually.of_forall fun n ↦
      (_root_.Prove2MeSourceProof.h_f9b33963924eb7ac5401881f (u n)).aestronglyMeasurable
  · filter_upwards [huK] with n hn
    exact ae_of_all _ fun x ↦ by
      refine (_root_.Prove2MeSourceProof.h_2be0585f00e4ee67c5a1001f (u n) x).trans ?_
      apply mul_le_mul_of_nonneg_right _ (ENNReal.toReal_nonneg)
      dsimp [C]
      unfold ProbabilityTheory.levyExponentBound
      have hsquare : (u n) ^ 2 ≤ K ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hK).mpr hn
      have hcoef : 3 + |u n| ≤ 3 + K := by linarith
      simpa [abs_of_nonneg hK, add_comm] using
        add_le_add_left (mul_le_mul hcoef hsquare (sq_nonneg _) (by positivity)) 2
  · exact hbase.const_mul C
  · exact ae_of_all _ fun x ↦ by
      have hx : Continuous (fun s : ℝ ↦ ProbabilityTheory.levyExponentIntegrand s x) := by
        unfold ProbabilityTheory.levyExponentIntegrand
        fun_prop
      exact hx.continuousAt.tendsto.comp hut
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


