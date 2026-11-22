-- Prove2me | solution 1 for AlmostPeriodic.bounded_and_uniformContinuous_of_isBohrAlmostPeriodic
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:42:34.016631+00:00
-- url     : https://prove2.me/submissions/13b1c1b4-d205-411a-9929-a0254d4527ff

import Mathlib
import Definitions.Def_AlmostPeriodic_BohrAlmostPeriodic

open AlmostPeriodic Set

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] (f : ℝ → E)
    (hf : IsBohrAlmostPeriodic f) :
    (∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C) ∧ UniformContinuous f := by
  obtain ⟨hCont, hPeriods⟩ := hf
  have hTranslate {ε : ℝ} (hε : 0 < ε) : ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ,
      ∃ τ : ℝ, x - τ ∈ Icc 0 L ∧ ∀ z : ℝ, dist (f z) (f (z - τ)) ≤ ε := by
    obtain ⟨L, hL, hCover⟩ := hPeriods ε hε
    refine ⟨L, hL, fun x => ?_⟩
    obtain ⟨τ, hτ, hInterval⟩ := hCover (x - L)
    refine ⟨τ, ⟨?_, ?_⟩, fun z => ?_⟩
    · linarith [hInterval.2]
    · linarith [hInterval.1]
    · rw [dist_eq_norm]
      simpa only [sub_add_cancel] using hτ (z - τ)
  constructor
  · obtain ⟨L, _, hL⟩ := hTranslate zero_lt_one
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hCont.norm.continuousOn
      (K := Icc (0 : ℝ) L)
    refine ⟨C + 1, fun x => ?_⟩
    obtain ⟨τ, hx, hτ⟩ := hL x
    have hb : ‖f (x - τ)‖ ≤ C := hC ⟨x - τ, hx, rfl⟩
    have h := dist_triangle (f x) (f (x - τ)) 0
    rw [dist_zero_right, dist_zero_right] at h
    linarith [hτ x]
  · refine Metric.uniformContinuous_iff.mpr fun ε hε => ?_
    obtain ⟨L, _, hL⟩ := hTranslate (by linarith : 0 < ε / 4)
    have hUC : UniformContinuousOn f (Icc (-1 : ℝ) (L + 1)) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hCont.continuousOn
    obtain ⟨δ, hδ, hδclose⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) (by linarith)
    refine ⟨min 1 δ, lt_min zero_lt_one hδ, fun x y hxy => ?_⟩
    obtain ⟨τ, hx, hτ⟩ := hL x
    have hx' : x - τ ∈ Icc (-1 : ℝ) (L + 1) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hUnit : |x - y| < 1 := by
      rw [← Real.dist_eq]
      exact hxy.trans_le (min_le_left _ _)
    have hy' : y - τ ∈ Icc (-1 : ℝ) (L + 1) :=
      ⟨by linarith [hx.1, (abs_lt.mp hUnit).2], by linarith [hx.2, (abs_lt.mp hUnit).1]⟩
    have hShift : dist (x - τ) (y - τ) < δ := by
      simpa only [dist_sub_right] using hxy.trans_le (min_le_right 1 δ)
    have hMiddle := hδclose _ hx' _ hy' hShift
    have hFirst := dist_triangle (f x) (f (x - τ)) (f y)
    have hLast := dist_triangle (f (x - τ)) (f (y - τ)) (f y)
    rw [dist_comm (f (y - τ)) (f y)] at hLast
    linarith [hτ x, hτ y]
