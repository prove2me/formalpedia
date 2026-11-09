-- Prove2me | Definitions.Def_AutobidSPPE_rhoMin
-- name    : AutobidSPPE_rhoMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:53.655826+00:00
-- url     : https://prove2.me/theorems/a06022b6-8f33-42c3-84a9-f99fa301714b
-- title:
--   $\rho_{\min}=\min_i\rho_i$
-- statement:
--   The smallest budget,
--   $$
--   \rho_{\min}=\min_i\rho_i .
--   $$
--
--   **Formalization Note** An infimum over `Fin n`, the minimum for $n\ge1$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (10), p.11

import Mathlib

namespace AutobidSPPE

/-- `ρ_min = minᵢ ρᵢ` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (10), p.11).

**Formalization Note** `⨅ i` over `Fin n`, the minimum for `n ≥ 1`. -/
noncomputable def rhoMin {n : ℕ} (ρ : Fin n → ℝ) : ℝ := ⨅ i, ρ i

end AutobidSPPE


