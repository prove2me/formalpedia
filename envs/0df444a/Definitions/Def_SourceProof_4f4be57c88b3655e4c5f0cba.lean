-- Prove2me | Definitions.Def_SourceProof_4f4be57c88b3655e4c5f0cba
-- name    : SourceProof_4f4be57c88b3655e4c5f0cba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:26.893535+00:00
-- url     : https://prove2.me/theorems/50a36b99-110f-4f0e-a266-bada5445a396
-- title:
--   StochLean source theorem: ProbabilityTheory.continuous_eq_of_exp_eq_of_eq_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F002
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real

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


theorem _root_.Prove2MeSourceProof.h_4f4be57c88b3655e4c5f0cba
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hzero : f 0 = g 0) (hexp : ∀ t, Complex.exp (f t) = Complex.exp (g t)) :
    f = g := by
  let S : Set ℝ := {t | f t = g t}
  have hclosed : IsClosed S := isClosed_eq hf hg
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hdiffx : f x - g x = 0 := sub_eq_zero.mpr hx
    have hnear : (fun y ↦ f y - g y) ⁻¹' Metric.ball 0 (2 * Real.pi) ∈ 𝓝 x := by
      apply (hf.sub hg).continuousAt
      simpa [hdiffx] using Metric.ball_mem_nhds (0 : ℂ) Real.two_pi_pos
    apply Filter.mem_of_superset hnear
    intro y hy
    have hyNorm : ‖f y - g y‖ < 2 * Real.pi := by simpa using hy
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp y)
    have hdiff : f y - g y = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hn]
      ring
    by_contra hne
    have hn0 : n ≠ 0 := by
      intro hnzero
      subst n
      simp at hdiff
      exact hne (sub_eq_zero.mp hdiff)
    have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hnabsInt : (1 : ℤ) ≤ |n| := by
        rcases lt_or_gt_of_ne hn0 with hnneg | hnpos
        · rw [abs_of_neg hnneg]
          omega
        · rw [abs_of_pos hnpos]
          omega
      exact_mod_cast hnabsInt
    have hnorm : 2 * Real.pi ≤ ‖f y - g y‖ := by
      rw [hdiff, norm_mul]
      simp only [Complex.norm_intCast, Complex.norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one]
      norm_num [Real.pi_pos.le]
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    exact (not_le_of_gt hyNorm) hnorm
  have hnonempty : S.Nonempty := ⟨0, hzero⟩
  have hSuniv : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hnonempty
  funext t
  have ht : t ∈ S := by rw [hSuniv]; exact Set.mem_univ t
  exact ht
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


