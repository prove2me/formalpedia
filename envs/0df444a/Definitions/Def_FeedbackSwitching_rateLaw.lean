-- Prove2me | Definitions.Def_FeedbackSwitching_rateLaw
-- name    : FeedbackSwitching_rateLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:15.325222+00:00
-- url     : https://prove2.me/theorems/d4e687c8-6a5b-407a-aab3-1a2687abea79
-- title:
--   Dyadic rate law (Eq. (25)) and mean rate $\mu=\kappa(1+m/2)$ (Eq. (26))
-- statement:
--   Let $\kappa=2^{-m}$. Each block draws a rate $\tau$ from
--   $$
--   \mathbb P(\tau=y)=\frac{\kappa}{2y}\quad\big(y\in\{\kappa,2\kappa,4\kappa,\dots,\tfrac12\}\big),\qquad\mathbb P(\tau=1)=\kappa .
--   $$
--   The $m+1$ probabilities sum to one, and the mean rate is $\mu=\mathbb E\tau=\kappa(1+m/2)$.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Eqs. (25)–(26), p.22 (PDF p.24)

import Mathlib

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

Base rate `κ = 2^{−m}` (§4, p.17). -/
noncomputable def baseRate (m : ℕ) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹

/-- The rates of the dyadic law (25): atom `k < m` is `κ 2^k` (so `κ, 2κ, …, 1/2`), atom `m` is
`1`. -/
noncomputable def rateVal (m : ℕ) (k : Fin (m + 1)) : ℝ :=
  if (k : ℕ) < m then baseRate m * 2 ^ (k : ℕ) else 1

/-- **Dyadic rate law** (Eq. (25), p.22 = PDF p.24): `P(τ = y) = κ/(2y)` for
`y ∈ {κ, 2κ, 4κ, …, 1/2}` and `P(τ = 1) = κ`; weight of atom `k`. -/
noncomputable def rateProb (m : ℕ) (k : Fin (m + 1)) : ℝ :=
  if (k : ℕ) < m then baseRate m / (2 * rateVal m k) else baseRate m

/-- Mean rate `µ = E τ = κ(1 + m/2)` (Eq. (26)). -/
noncomputable def meanRate (m : ℕ) : ℝ :=
  baseRate m * (1 + (m : ℝ) / 2)

end FeedbackSwitching


