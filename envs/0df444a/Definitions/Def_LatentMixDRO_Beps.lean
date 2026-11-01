-- Prove2me | Definitions.Def_LatentMixDRO_Beps
-- name    : LatentMixDRO_Beps
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:39.780993+00:00
-- url     : https://prove2.me/theorems/4df777dc-a888-4de0-96d3-c574abac999e
-- title:
--   The constant $B_\epsilon$ (17)
-- statement:
--   With $q=p/(p-1)$,
--
--   $$
--   B_\epsilon=\epsilon^{-q}2^{q-1}RML^2+\epsilon^{-1}2^{q-1}L\big(2M+(q-1)LR\big)+\epsilon^{q-2}(q-1)2^{q-2}L+LR.
--   $$
--
--   It is the constant in the bound (18) of Theorem 1.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (17), p.11

import Mathlib

namespace LatentMixDRO

/-- The constant (17), with `q = p/(p - 1)`:
`B_ε = ε^{-q} 2^{q-1} R M L² + ε^{-1} 2^{q-1} L (2M + (q - 1) L R) + ε^{q-2} (q - 1) 2^{q-2} L + L R`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (17), p.11. -/
noncomputable def Beps (p ε L R M : ℝ) : ℝ :=
  ε ^ (-(p / (p - 1))) * 2 ^ (p / (p - 1) - 1) * R * M * L ^ 2
    + ε⁻¹ * 2 ^ (p / (p - 1) - 1) * L * (2 * M + (p / (p - 1) - 1) * L * R)
    + ε ^ (p / (p - 1) - 2) * (p / (p - 1) - 1) * 2 ^ (p / (p - 1) - 2) * L
    + L * R

end LatentMixDRO


