-- Prove2me | Definitions.Def_AutobidSPPE_tauMin
-- name    : AutobidSPPE_tauMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:55.945192+00:00
-- url     : https://prove2.me/theorems/45ac1beb-8e12-4597-9a1d-491c27943a41
-- title:
--   $\tau_{\min}=\min_i\tau_i$
-- statement:
--   The smallest averaging step,
--   $$
--   \tau_{\min}=\min_i\tau_i .
--   $$
--
--   **Formalization Note** An infimum over `Fin n`, the minimum for $n\ge1$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (15), p.12

import Mathlib

namespace AutobidSPPE

/-- `τ_min = minᵢ τᵢ` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (15), p.12; (24), p.14).

**Formalization Note** `⨅ i` over `Fin n`, the minimum for `n ≥ 1`. -/
noncomputable def tauMin {n : ℕ} (τ : Fin n → ℝ) : ℝ := ⨅ i, τ i

end AutobidSPPE


