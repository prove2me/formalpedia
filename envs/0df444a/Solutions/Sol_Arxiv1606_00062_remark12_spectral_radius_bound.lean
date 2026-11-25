-- Prove2me | solution 1 for Arxiv1606_00062.remark12_spectral_radius_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:51:19.642603+00:00
-- url     : https://prove2.me/submissions/2f77a3ad-4a9d-489c-b914-ce16dedd3e36

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open Filter Topology Set

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (K : E →L[ℂ] E) (C δ : ℝ) (hC : 0 < C) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (h47 : ∀ l : ℕ, 1 ≤ l → ∀ h : E, ‖(K ^ l) h‖ ≤ C * δ ^ l * ‖h‖) :
    Tendsto (fun l : ℕ => ENNReal.ofReal (‖K ^ l‖ ^ (1 / (l : ℝ)))) atTop
      (𝓝 (spectralRadius ℂ K)) ∧
    spectralRadius ℂ K ≤ ENNReal.ofReal δ ∧
    spectralRadius ℂ K < 1 := by
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius K
  have h2 : spectralRadius ℂ K ≤ ENNReal.ofReal δ := by
    have hlim : Tendsto (fun l : ℕ => ENNReal.ofReal (C ^ (1 / (l : ℝ)) * δ)) atTop
        (𝓝 (ENNReal.ofReal δ)) := by
      apply ENNReal.tendsto_ofReal
      have h0 : Tendsto (fun l : ℕ => (1 : ℝ) / l) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
      have h1 := ((Real.continuousAt_const_rpow hC.ne').tendsto.comp h0)
      simp only [Real.rpow_zero] at h1
      simpa using h1.mul_const δ
    refine le_of_tendsto_of_tendsto hG hlim ?_
    filter_upwards [eventually_ge_atTop 1] with l hl
    apply ENNReal.ofReal_le_ofReal
    have hb : ‖K ^ l‖ ≤ C * δ ^ l :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) (h47 l hl)
    calc ‖K ^ l‖ ^ (1 / (l : ℝ)) ≤ (C * δ ^ l) ^ (1 / (l : ℝ)) :=
          Real.rpow_le_rpow (norm_nonneg _) hb (by positivity)
      _ = C ^ (1 / (l : ℝ)) * δ := by
          rw [Real.mul_rpow hC.le (by positivity), one_div,
            Real.pow_rpow_inv_natCast hδ₀.le (by omega)]
  refine ⟨hG, h2, h2.trans_lt ?_⟩
  exact ENNReal.ofReal_lt_one.mpr hδ₁
