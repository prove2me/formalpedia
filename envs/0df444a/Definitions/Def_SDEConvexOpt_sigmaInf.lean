-- Prove2me | Definitions.Def_SDEConvexOpt_sigmaInf
-- name    : SDEConvexOpt_sigmaInf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:44.343214+00:00
-- url     : https://prove2.me/theorems/c18dfb3c-6710-4054-b464-d6bd01735bb4
-- title:
--   The noise level $\sigma_\infty(t)=\sup_x\|\sigma(t,x)\|_F$
-- statement:
--   For a diffusion term $\sigma$, the noise level at time $t$ is
--   $$
--   \sigma_\infty(t)=\sup_{x\in\mathbb R^d}\|\sigma(t,x)\|_F .
--   $$
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$, so $\sigma_\infty$ is defined for every $\sigma$ (with value $\infty$ where $\|\sigma(t,\cdot)\|_F$ is unbounded).
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, (1.1), p.3

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SDEConvexOpt_Diffusion

open scoped NNReal ENNReal

namespace SDEConvexOpt

open EthierKurtz

/-- The noise level `σ∞(t) = sup_{x ∈ ℝ^d} ‖σ(t, x)‖_F`
(Maulen S., Fadili, Attouch, arXiv:2207.02750v1, (1.1), p.3).

**Formalization Note** The supremum is taken in `ℝ≥0∞` (`‖·‖ₑ` is the extended Frobenius norm),
so it is defined for every `σ`, with value `∞` when `‖σ(t, ·)‖_F` is unbounded. -/
noncomputable def sigmaInf {d m : ℕ} (σ : ℝ≥0 × SDEState d → Diffusion d m) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨆ x : SDEState d, ‖σ (t, x)‖ₑ

end SDEConvexOpt


