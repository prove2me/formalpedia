-- Prove2me | solution 1 for AlgoTransparency.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:43:48.708213+00:00
-- url     : https://prove2.me/submissions/c541e381-ffb4-427b-9f49-d01472585784

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_beta3
import Definitions.Def_AlgoTransparency_betaBar

open AlgoTransparency in
theorem solution (p : Params) (hp : Standing p) :
    ((2 * p.lam - 1) / p.lam * p.θ * (p.α + p.β - p.R) <
        p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R ↔ beta3 p < p.β) ∧
    beta3 p = betaBar p ∧
    p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R <
      (2 * p.lam - 1) / p.lam * p.θ * (p.α + p.β - p.R) := by
  obtain ⟨⟨hθ0, hθ1⟩, ⟨hl0, hl1⟩, -, -, -, hβ2⟩ := hp
  have hl : 0 < p.lam := by linarith
  have hD : 0 < p.lam - 2 * p.θ * p.lam + p.θ := by
    nlinarith [mul_pos hl (sub_pos.mpr hθ1), mul_nonneg hθ0.le (sub_nonneg.mpr hl1)]
  have hD' : 0 < p.θ * (1 - p.lam) + (1 - p.θ) * p.lam := by
    nlinarith [mul_pos hl (sub_pos.mpr hθ1), mul_nonneg hθ0.le (sub_nonneg.mpr hl1)]
  have hc : 0 < (p.lam - 2 * p.θ * p.lam + p.θ) / p.lam := div_pos hD hl
  obtain ⟨D, hDdef⟩ : ∃ D, D = p.lam - 2 * p.θ * p.lam + p.θ := ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ D', D' = p.θ * (1 - p.lam) + (1 - p.θ) * p.lam := ⟨_, rfl⟩
  have hDne : D ≠ 0 := by rw [hDdef]; exact hD.ne'
  have hD'ne : D' ≠ 0 := by rw [hD'def]; exact hD'.ne'
  have hlne : p.lam ≠ 0 := hl.ne'
  have hE : p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R - (2 * p.lam - 1) / p.lam * p.θ * (p.α + p.β - p.R)
      = (p.lam - 2 * p.θ * p.lam + p.θ) / p.lam * (p.β - beta3 p) := by
    unfold beta3
    rw [← hDdef]
    field_simp
    subst hDdef
    ring
  have hbb : beta3 p = betaBar p := by
    unfold beta3 betaBar
    rw [← hDdef, ← hD'def]
    field_simp
    subst hDdef hD'def
    ring
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, hbb, ?_⟩
  · by_contra hne
    push_neg at hne
    have := mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith : p.β - beta3 p ≤ 0)
    linarith
  · have := mul_pos hc (by linarith : 0 < p.β - beta3 p)
    linarith
  · have hlt : p.β < beta3 p := by rw [hbb]; unfold betaBar; exact hβ2
    have := mul_neg_of_pos_of_neg hc (by linarith : p.β - beta3 p < 0)
    linarith
