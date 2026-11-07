-- Prove2me | Definitions.Def_StochAutoreg_risk
-- name    : StochAutoreg_risk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:06.711866+00:00
-- url     : https://prove2.me/theorems/2ae4bbc6-d664-470a-b3d3-4121530f3134
-- title:
--   Error $\mathbb E_{X\sim P}\mathrm{KL}(q_\star(X)\|\hat q(X))$, Eq. (1.1)
-- statement:
--   For a prompt law $P$ on $\Sigma^\star$, a target $q_\star$ and a predictor $\hat q:\Sigma^\star\to[0,1]$, the error is
--
--   $$\mathbb E_{X\sim P}\,\mathrm{KL}(q_\star(X)\|\hat q(X)).$$
--
--   **Formalization Note** It is a countable sum in $[0,\infty]$, so it can equal $+\infty$; a prompt of zero $P$-mass contributes $0$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Eq. (1.1), p.3

import Mathlib
import Definitions.Def_StochAutoreg_klBernE

namespace StochAutoreg

/-- The **error of a predictor** `q̂ : Σ⋆ → [0,1]` for a target `q⋆` under a prompt law `P`:
`E_{X∼P} KL(q⋆(X)‖q̂(X))`, Eq. (1.1).
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Eq. (1.1), p.3.

**Formalization Note.** A prompt law is a `PMF` on the countable set `List Bool`. The expectation is a
`tsum` in `ℝ≥0∞`, so it carries the value `+∞`. A prompt with `P x = 0` contributes `0` even when the
divergence there is `+∞` (`0 * ⊤ = 0`), as in the expectation. -/
noncomputable def risk (P : PMF (List Bool)) (q : List Bool → ℝ) (qhat : List Bool → unitInterval) :
    ENNReal :=
  ∑' x, P x * klBernE (q x) (qhat x)

end StochAutoreg


