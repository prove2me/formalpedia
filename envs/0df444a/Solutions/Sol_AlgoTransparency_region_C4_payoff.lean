-- Prove2me | solution 1 for AlgoTransparency.region_C4_payoff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:08:34.760293+00:00
-- url     : https://prove2.me/submissions/b79080f3-95b2-4b58-8c11-a9fe4c5e75d8

import Mathlib
import Definitions.Def_AlgoTransparency_Standing

open AlgoTransparency in
theorem solution (p : Params) (hp : Standing p) :
    p.lam * p.θ * p.α - (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R <
      p.θ * (p.α + p.β - p.R) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6, h7⟩, _, _⟩ := hp
  have a1 : 0 ≤ (1 - p.lam) * (p.θ * (p.α - p.R)) :=
    mul_nonneg (by linarith) (mul_nonneg h1.le (by linarith))
  have a2 : 0 ≤ (1 - p.lam) * ((1 - p.θ) * p.R) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have a3 : 0 < p.θ * p.β := mul_pos h1 h5
  nlinarith
