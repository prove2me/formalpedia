-- Prove2me | Definitions.Def_MDPFinance_MeanVariance_PLambdaBValueFunction
-- name    : MDPFinance_MeanVariance_PLambdaBValueFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:34.726988+00:00
-- url     : https://prove2.me/theorems/1518a521-667a-4c36-862b-94028cb9b6d5
-- title:
--   The value function of the auxiliary problem P(lambda,b) from time n
-- statement:
--   $$V_n(x) := \inf_\pi \Big[\Big(\frac{1}{1-\gamma}+\lambda\Big)
--   \mathbb{E}[(X_N+b)^- \mid X_n=x] - \lambda\,\mathbb{E}[(X_N+b)^+ \mid X_n=x]\Big]$$
--   over strategies admissible on $[n,N)$ (`VPlambdabFrom`), as an extended real, the value function
--   of $P(\lambda,b)$ whose explicit form Theorem 4.7.1 gives.
--
--   **Formalization Note.** `EReal`-valued, matching the book's own use of $\pm\infty$ as the value
--   of $P(\lambda,b)$ when $c_0<d_0$ (Theorem 4.7.1(a)).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 126-127, PDF 140-141, unnumbered display

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A policy sequence restricted to `[n,N)` is admissible if `π k` is measurable for every
`n ≤ k < N`. -/
def MeanRiskMarket.IsAdmissibleFrom (M : MeanRiskMarket Ω) (n : ℕ) (π : ℕ → ℝ → ℝ) : Prop :=
  ∀ k, n ≤ k → k < M.N → Measurable (π k)

/-- The value function of `P(λ,b)` from time `n`, state `x`:
`V_n(x) := inf_π [(1/(1-γ)+λ)𝔼[(X_N+b)^- | X_n=x] - λ𝔼[(X_N+b)^+ | X_n=x]]`, as an extended
real (Bäuerle–Rieder, p. 126-127, PDF 140-141). -/
noncomputable def MeanRiskMarket.VPlambdabFrom (M : MeanRiskMarket Ω) (lam b : ℝ) (n : ℕ)
    (x : ℝ) : EReal :=
  ⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissibleFrom n π},
    (((1 - M.γ)⁻¹ + lam) *
        ∫ ω, max (-(M.terminalWealth π (M.N - n) n x ω + b)) 0 ∂M.measIP -
      lam * ∫ ω, max (M.terminalWealth π (M.N - n) n x ω + b) 0 ∂M.measIP : EReal)

end MDPFinance.MeanVariance


