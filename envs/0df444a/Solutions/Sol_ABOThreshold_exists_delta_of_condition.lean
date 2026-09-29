-- Prove2me | solution 1 for ABOThreshold.exists_delta_of_condition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:32:41.079859+00:00
-- url     : https://prove2.me/submissions/7107faf6-7350-4d4c-853c-5be81423705f

import Definitions.Def_ABOThreshold_model

open ABOThreshold Finset

theorem solution (A k : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hc : ThresholdCondition A k η) :
    ∃ δ : ℝ, 0 < δ ∧ (A.choose (k + 1) : ℝ) * η ^ (k + 1) < η ^ (1 + δ) := by
  have h1 : Filter.Tendsto (fun δ : ℝ => 1 + δ) (nhds 0) (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := nhds (0 : ℝ))).add
      (Filter.tendsto_id (x := nhds (0 : ℝ)))
    simpa using h
  have h2 : Filter.Tendsto (fun δ : ℝ => η ^ (1 + δ)) (nhds 0) (nhds η) := by
    have := ((Real.continuousAt_const_rpow (b := 1) hη.ne').tendsto).comp h1
    rw [Real.rpow_one] at this
    exact this
  have h3 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (A.choose (k + 1) : ℝ) * η ^ (k + 1) < η ^ (1 + δ) :=
    (h2.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hc)
  have h4 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ1, hδ2⟩ := (h4.and h3).exists
  exact ⟨δ, hδ1, hδ2⟩
