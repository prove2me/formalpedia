-- Prove2me | solution 1 for Arxiv1606_00062.preconditioned_neumann_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:52:41.957051+00:00
-- url     : https://prove2.me/submissions/f894b44e-8a5d-42d0-a4a2-4fb962ed6d9d

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open Filter Topology Set

namespace S69N

lemma summ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (K : E →L[ℂ] E) (hK : spectralRadius ℂ K < 1) :
    Summable (fun l : ℕ => K ^ l) := by
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius K
  set ρ := spectralRadius ℂ K
  have hρ : ρ ≠ ⊤ := ne_top_of_lt hK
  have hρ1 : ρ.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hρ ENNReal.one_ne_top).mpr hK
    simpa using this
  set r := (ρ.toReal + 1) / 2
  have hr0 : 0 < r := by have := ENNReal.toReal_nonneg (a := ρ); positivity
  have hr1 : r < 1 := by simp only [r]; linarith
  have hρr : ρ < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hρ]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr (by simp only [r]; linarith)
  have hev := hG.eventually (gt_mem_nhds hρr)
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0.le hr1) ?_
  filter_upwards [hev, eventually_ge_atTop 1] with l hl hl1
  have h1 : ‖K ^ l‖ ^ (1 / (l : ℝ)) < r := (ENNReal.ofReal_lt_ofReal_iff hr0).mp hl
  have h2 := pow_le_pow_left₀ (by positivity) h1.le l
  rwa [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) (by omega)] at h2

end S69N

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (T K : E →L[ℂ] E) (g : E) (hK : spectralRadius ℂ K < 1) :
    IsUnit (1 - K) ∧
    Summable (fun l : ℕ => K ^ l) ∧
    Ring.inverse (1 - K) = ∑' l : ℕ, K ^ l ∧
    Summable (fun l : ℕ => K ^ l * (T - K)) ∧
    Summable (fun l : ℕ => (K ^ l) g) ∧
    ∀ η : E, (Ring.inverse (1 - K) * (1 - T)) η = Ring.inverse (1 - K) g ↔
      (1 - ∑' l : ℕ, K ^ l * (T - K)) η = ∑' l : ℕ, (K ^ l) g := by
  have hs := S69N.summ K hK
  have hl : (∑' l : ℕ, K ^ l) * (1 - K) = 1 := hs.tsum_pow_mul_one_sub
  have hr : (1 - K) * (∑' l : ℕ, K ^ l) = 1 := hs.one_sub_mul_tsum_pow
  have hu : IsUnit (1 - K) := ⟨⟨1 - K, ∑' l : ℕ, K ^ l, hr, hl⟩, rfl⟩
  have hinv : Ring.inverse (1 - K) = ∑' l : ℕ, K ^ l := by
    let u : (E →L[ℂ] E)ˣ := ⟨1 - K, ∑' l : ℕ, K ^ l, hr, hl⟩
    exact Ring.inverse_unit u
  have hs2 : Summable (fun l : ℕ => K ^ l * (T - K)) := hs.mul_right _
  have hs3 : Summable (fun l : ℕ => (K ^ l) g) :=
    (ContinuousLinearMap.apply ℂ E g).summable hs
  refine ⟨hu, hs, hinv, hs2, hs3, fun η => ?_⟩
  have e1 : ∑' l : ℕ, K ^ l * (T - K) = (∑' l : ℕ, K ^ l) * (T - K) := hs.tsum_mul_right _
  have e2 : ∑' l : ℕ, (K ^ l) g = (∑' l : ℕ, K ^ l) g :=
    ((ContinuousLinearMap.apply ℂ E g).map_tsum hs).symm
  have e3 : Ring.inverse (1 - K) * (1 - T) = 1 - (∑' l : ℕ, K ^ l) * (T - K) := by
    rw [hinv, show (1 : E →L[ℂ] E) - T = (1 - K) - (T - K) by abel, mul_sub, hl]
  rw [e3, e1, e2, hinv]
