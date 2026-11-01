-- Prove2me | Definitions.Def_RandomRateMSQ_SolvesLimitEq
-- name    : RandomRateMSQ_SolvesLimitEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:25.704985+00:00
-- url     : https://prove2.me/theorems/53706026-5ee7-44c0-ba5f-5fbe32d1b37d
-- title:
--   Solutions of the limit integral equation (3.7)
-- statement:
--   Given $x_0\in\mathbb R$, a path $w$, reals $b,\gamma$ and a coefficient path $c$, a measurable path $\xi:[0,\infty)\to\mathbb R$ that is bounded on every $[0,T]$ **solves the limit equation** if for all $t\ge0$
--
--   $$
--   \xi(t)=x_0+w(t)+b\,t+c(t)\int_0^t\xi^-(s)\,ds-\gamma\int_0^t\xi^+(s)\,ds .
--   $$
--
--   In Theorem 5 the noise is $w=\sqrt{\bar\mu(1+\mathrm{var}\,u)}\,W$, the drift is $b=\hat\lambda-\tilde\sigma$ and the coefficient is $c(t)=\langle\!\langle\iota,\eta_t\rangle\!\rangle$.
--
--   **Formalization Note** The coefficient multiplies the whole integral, $c(t)\int_0^t\xi^-$, as printed in (3.7). Measurability and local boundedness make both integrals genuine.
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, Theorem 5, eq. (3.7), p.17

import Mathlib
import Definitions.Def_RandomRateMSQ_StandingData

open MeasureTheory
open scoped NNReal

namespace RandomRateMSQ

/-- `ξ` **solves the limit equation** (3.7) with data `x₀, w, b, γ, c` (Büke–Qin,
arXiv:1905.04198v1, Theorem 5, p.17):
`ξ(t) = x₀ + w(t) + b t + c(t) ∫₀ᵗ ξ⁻(s) ds − γ ∫₀ᵗ ξ⁺(s) ds` for all `t ≥ 0`, with `ξ` measurable
and bounded on every `[0, T]`.

In Theorem 5, `w` is the noise `√(µ̄(1 + var u)) W`, `b = β = λ̂ − σ̃` and `c(t) = ⟨⟨ι, ηₜ⟩⟩`.

**Formalization Note.** The coefficient multiplies the whole integral: `c(t) · ∫₀ᵗ ξ⁻`, not
`∫₀ᵗ c(s) ξ⁻(s) ds`, as printed. `ξ⁻ = max(−ξ, 0)`, `ξ⁺ = max(ξ, 0)`. Measurability and local
boundedness make both integrals genuine (no junk value of the Bochner integral). -/
def SolvesLimitEq (x₀ : ℝ) (w : ℝ≥0 → ℝ) (b γ : ℝ) (c : ℝ≥0 → ℝ) (ξ : ℝ≥0 → ℝ) : Prop :=
  Measurable ξ ∧ (∀ T : ℝ≥0, ∃ K : ℝ, ∀ t : ℝ≥0, t ≤ T → |ξ t| ≤ K) ∧
    ∀ t : ℝ≥0, ξ t = x₀ + w t + b * t + c t * cumInt (fun s => max (-ξ s) 0) t -
      γ * cumInt (fun s => max (ξ s) 0) t

end RandomRateMSQ


