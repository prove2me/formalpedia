-- Prove2me | Definitions.Def_HighDimStat_Minimax_MinimaxRisk
-- name    : HighDimStat_Minimax_MinimaxRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:32:18.437588+00:00
-- url     : https://prove2.me/theorems/04f7d57e-0968-4610-9d0e-bf9860365677
-- title:
--   The minimax risk M(theta(P); Phi o rho)
-- statement:
--   This is the **minimax risk** of Wainwright's Eq. (15.2), the central object of Chapter 15:
--   the smallest achievable worst-case expected loss, over every measurable estimator, for
--   recovering a functional $\theta(P)$ of an unknown distribution $P$ ranging over a class.
--
--   For a measurable sample space $\mathcal X$, parameter space $\Omega$, a distribution class
--   indexed by a type `Idx` with $P_i$ a probability measure on $\mathcal X$ for each $i$,
--   functional $\theta: \mathrm{Idx} \to \Omega$, semi-metric $\rho:\Omega\times\Omega\to
--   [0,\infty)$, and increasing $\Phi:[0,\infty)\to[0,\infty)$,
--
--   $$
--   \mathfrak M(\theta(\mathcal P); \Phi\circ\rho) \;:=\; \inf_{\hat\theta} \sup_{i}
--   \mathbb E_{P_i}\bigl[\Phi\bigl(\rho(\hat\theta(X), \theta_i)\bigr)\bigr],
--   $$
--
--   where the infimum ranges over all measurable estimators $\hat\theta: \mathcal X \to
--   \Omega$.
--
--   **Formalization Note** Realized with the extended-nonnegative-real (`ENNReal`) lower
--   Lebesgue integral `∫⁻` rather than the Bochner integral, so a non-integrable loss
--   contributes its true (possibly infinite) value rather than Mathlib's Bochner-integral junk
--   value `0` — legitimate here since the loss `Φ(ρ(·,·))` is always nonnegative. The
--   distribution class $\mathcal P$ is realized as an indexed family `measure : Idx → Measure
--   𝒳` (one measure per index) rather than a bare `Set (Measure 𝒳)`, which is definitionally
--   equivalent and composes directly with the functional `θ : Idx → Ω`.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 487 (PDF p. 507), Eq. (15.2)

import Mathlib

open MeasureTheory

namespace HighDimStat.Minimax

/-- The **minimax risk** `M(θ(P); Φ∘ρ)` of Wainwright, *High-Dimensional Statistics* (2019),
Eq. (15.2), p. 487: the infimum, over every measurable estimator `θ̂ : 𝒳 → Ω`, of the worst-case
(over the distribution class, indexed by `Idx`) expected loss `E_P[Φ(ρ(θ̂,θ(P)))]`.

Realized with the extended-nonnegative-real (`ENNReal`) lower Lebesgue integral `∫⁻` rather than
the Bochner integral `∫`, so that a non-integrable loss contributes its true (possibly
infinite) value instead of Mathlib's Bochner-integral junk value `0` — the loss
`Φ(ρ(θ̂ x, θ p))` is always a nonnegative quantity here (`ρ ≥ 0`, and `Φ` is only ever evaluated
on `[0,∞)` in this development), so `ENNReal.ofReal` composed with `∫⁻` is exactly the
extended-real expectation the book's `E_P[·]` denotes, with no integrability hypothesis needed
to state it. -/
noncomputable def minimaxRisk {𝒳 Ω Idx : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Ω]
    (measure : Idx → Measure 𝒳) (θ : Idx → Ω) (ρ : Ω → Ω → ℝ) (Φ : ℝ → ℝ) : ENNReal :=
  ⨅ θhat : {f : 𝒳 → Ω // Measurable f}, ⨆ p : Idx,
    ∫⁻ x, ENNReal.ofReal (Φ (ρ (θhat.1 x) (θ p))) ∂(measure p)

end HighDimStat.Minimax


