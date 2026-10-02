-- Prove2me | Definitions.Def_MDPFinance_FinancialMarkets_ContinuousPortfolio
-- name    : MDPFinance_FinancialMarkets_ContinuousPortfolio
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:47:26.660312+00:00
-- url     : https://prove2.me/theorems/5afef76d-156a-4ca8-a586-38f7fc9fb90d
-- title:
--   Definition 3.2.1 / 3.2.2 — continuous-time portfolios and self-financing
-- statement:
--   A **continuous-time portfolio** is an $(\mathcal{F}_t)$-predictable process $\varphi =
--   (\varphi^0_t,\varphi_t)$. Its wealth is $X_t^\varphi := \varphi^0_t + \varphi_t \cdot e$, and
--   $\varphi$ is **self-financing** if $X_t^\varphi = x_0 + \int_0^t \varphi^0_s\,dS^0_s/S^0_s +
--   \sum_k \int_0^t \varphi^k_s\,dS^k_s/S^k_s$ for $t \in [0,T]$.
--
--   **Formalization Note.** Mathlib has no general theory of stochastic integration against an
--   arbitrary càdlàg semimartingale (only specific constructions, e.g. Itô integration against
--   Brownian motion), which the book's jump-market price process (Chapter 9's setting this
--   definition is stated for) requires; `StochasticIntegral` abstracts the integral operator
--   itself as given data, so this definition states the self-financing *equation* exactly as the
--   book writes it, deferring the integral's own construction. This is infrastructure for later
--   chunks (`09b`); no result of this mission uses it.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 67, PDF 81, Definition 3.2.1 / Definition 3.2.2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.FinancialMarkets

/-- An abstract stochastic integral operator on `Ω`: `integral φ S t ω` stands for
`∫_0^t φ_s \, dS_s (ω)`. Bäuerle–Rieder's continuous-time self-financing condition (Definition
3.2.2) is stated in terms of stochastic integrals against a general càdlàg semimartingale price
process; Mathlib has no general theory of integration against such a process (only specific
constructions, e.g. against Brownian motion), so this abstracts the operator itself as given
data, satisfying no further axioms beyond being the object the book's formula names — see
`MODERATION_NOTES.md`. -/
structure StochasticIntegral (Ω : Type*) [MeasurableSpace Ω] where
  integral : (ℝ → Ω → ℝ) → (ℝ → Ω → ℝ) → ℝ → Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Definition 3.2.1 (Bäuerle–Rieder, p. 67, PDF 81). A portfolio or trading strategy is an
`(F_t)`-predictable stochastic process `φ = (φ⁰_t, φ_t)` where `φ⁰_t ∈ ℝ` and `φ_t ∈ ℝ^d`. -/
structure ContinuousPortfolio (Fam : ℝ → MeasurableSpace Ω) where
  φ0 : ℝ → Ω → ℝ
  φ : ℝ → Ω → (Fin d → ℝ)
  hφ0_predictable : ∀ t, @Measurable Ω ℝ (Fam t) _ (φ0 t)
  hφ_predictable : ∀ t, @Measurable Ω (Fin d → ℝ) (Fam t) _ (φ t)

/-- The wealth process `X_t^φ := Σ_k φ^k_t = φ⁰_t + φ_t · e` (Bäuerle–Rieder, p. 67, PDF 81,
unnumbered display). -/
noncomputable def ContinuousPortfolio.Xwealth {Fam : ℝ → MeasurableSpace Ω}
    (φ : ContinuousPortfolio (Ω := Ω) (d := d) Fam) (t : ℝ) (ω : Ω) : ℝ :=
  φ.φ0 t ω + ∑ k, φ.φ t ω k

/-- Definition 3.2.2 (Bäuerle–Rieder, p. 67, PDF 81). A portfolio strategy `φ` is called
self-financing if `X_t^φ = x_0 + ∫_0^t φ⁰_s \, dS^0_s/S^0_s + Σ_k ∫_0^t φ^k_s \, dS^k_s/S^k_s` for
`t ∈ [0,T]`, where `S⁰` is the bond price and `S^1,…,S^d` the risky asset prices. -/
def ContinuousPortfolio.IsSelfFinancing {Fam : ℝ → MeasurableSpace Ω}
    (φ : ContinuousPortfolio (Ω := Ω) (d := d) Fam) (S0 : ℝ → Ω → ℝ) (S : Fin d → ℝ → Ω → ℝ)
    (SI : StochasticIntegral Ω) (T x0 : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T,
    φ.Xwealth t = fun ω => x0 + SI.integral (fun s ω => φ.φ0 s ω / S0 s ω) S0 t ω +
      ∑ k, SI.integral (fun s ω => φ.φ s ω k / S k s ω) (S k) t ω

end MDPFinance.FinancialMarkets


