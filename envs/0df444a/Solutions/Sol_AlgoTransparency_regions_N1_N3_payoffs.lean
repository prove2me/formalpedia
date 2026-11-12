-- Prove2me | solution 1 for AlgoTransparency.regions_N1_N3_payoffs
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:20:26.097952+00:00
-- url     : https://prove2.me/submissions/357d5246-89d9-413d-a7d2-0e600e4aa6d4

import Mathlib
import Definitions.Def_AlgoTransparency_Standing

open AlgoTransparency in
theorem solution (p : Params) (hp : Standing p) :
    0 < p.lam * p.θ * p.α - (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R ∧
    p.θ * (p.α + p.β) - p.θ * p.R = p.θ * (p.α + p.β - p.R) ∧
    (p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R) -
        (p.lam * p.θ * (p.α + p.β) + (1 - p.lam) * (1 - p.θ) * p.β -
          (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R) =
      (1 - p.lam) * p.θ * (p.α + p.β - p.R) - p.lam * (1 - p.θ) * (p.R - p.β) ∧
    (1 - p.lam) * p.θ * (p.α + p.β - p.R) - p.lam * (1 - p.θ) * (p.R - p.β) =
      p.θ * (1 - p.lam) * p.α - (p.θ * (1 - p.lam) + (1 - p.θ) * p.lam) * (p.R - p.β) ∧
    p.θ * (1 - p.lam) * p.α - (p.θ * (1 - p.lam) + (1 - p.θ) * p.lam) * (p.R - p.β) < 0 := by
  obtain ⟨⟨h0, h1⟩, ⟨l0, l1⟩, ⟨b0, bR, Ra⟩, ⟨a1, a2⟩, ⟨c1, c2⟩⟩ := hp
  have hpos : 0 < p.θ * p.lam := mul_pos h0 (by linarith)
  have hq : 0 < (1 - p.θ) * p.lam := mul_pos (by linarith) (by linarith)
  have hr : 0 ≤ p.θ * (1 - p.lam) := mul_nonneg h0.le (by linarith)
  have hD : 0 < p.θ * (1 - p.lam) + (1 - p.θ) * p.lam := by linarith
  refine ⟨?_, by ring, by ring, by ring, ?_⟩
  · rw [div_lt_iff₀ hpos] at a1
    linarith
  · have h5 : p.θ * (1 - p.lam) * p.α / (p.θ * (1 - p.lam) + (1 - p.θ) * p.lam) < p.R - p.β := by
      linarith
    rw [div_lt_iff₀ hD] at h5
    linarith
