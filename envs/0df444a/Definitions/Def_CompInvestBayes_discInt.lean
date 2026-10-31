-- Prove2me | Definitions.Def_CompInvestBayes_discInt
-- name    : CompInvestBayes_discInt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:58.311968+00:00
-- url     : https://prove2.me/theorems/73d308d3-00c5-4d03-81ba-5e6ffe7c0046
-- title:
--   Discounted earnings $\int_{[\alpha,\beta)} e^{-\lambda t}\,dX_t$ of a drifted Brownian motion
-- statement:
--   For a cumulative earning process $X_t=a\,t+\sigma B_t$ with constant drift $a$ and volatility $\sigma$, and times $0\le\alpha\le\beta\le\infty$, the discounted earnings over $[\alpha,\beta)$ are
--
--   $$
--   \int_{[\alpha,\beta)} e^{-\lambda t}\,dX_t
--   = \frac{a\,(e^{-\lambda\alpha}-e^{-\lambda\beta})}{\lambda}
--   + \sigma\Big(e^{-\lambda\beta}B_\beta-e^{-\lambda\alpha}B_\alpha+\lambda\int_\alpha^\beta e^{-\lambda t}B_t\,dt\Big),
--   $$
--
--   with the conventions $e^{-\lambda\cdot\infty}:=0$ and $e^{-\lambda\cdot\infty}B_\infty:=0$. The file also defines the discount factor $e^{-\lambda\alpha}$ on $[0,\infty]$.
--
--   These integrals are the payoffs of both firms: (7) and (8) of the paper are expectations of them.
--
--   **Formalization Note** Mathlib has no Itô integral. For the deterministic $C^1$ integrand $e^{-\lambda t}$ the Itô integral equals the pathwise integration-by-parts expression above almost surely, so this is the paper's integral. When the entry time is $\infty$, the post-entry integral is $0$.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), eqs. (1), (3), (4), pp.7–8 and the integrals of (7), (8), p.10 (PDF 7–10)

import Mathlib

open MeasureTheory
open scoped NNReal

namespace CompInvestBayes

/-- The discount factor `e^{-λα}` at a time `α ∈ [0, ∞]`, with `e^{-λ·∞} := 0`. -/
noncomputable def discFactor (lam : ℝ) : WithTop ℝ≥0 → ℝ
  | ⊤ => 0
  | (t : ℝ≥0) => Real.exp (-lam * t)

/-- The discounted path value `e^{-λα} B_α` at a time `α ∈ [0, ∞]`, with `e^{-λ·∞} B_∞ := 0`. -/
noncomputable def discPath (lam : ℝ) (B : ℝ≥0 → ℝ) : WithTop ℝ≥0 → ℝ
  | ⊤ => 0
  | (t : ℝ≥0) => Real.exp (-lam * t) * B t

/-- The time window `[α, β)` (with `α, β ∈ [0, ∞]`), as a set of real times `t ≥ 0`. -/
def window (α β : WithTop ℝ≥0) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ α ≤ ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) ∧ ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) < β}

/-- **Discounted earnings over a time window.** For a cumulative earning process
`X_t = a t + σ B_t` (a drifted Brownian motion with constant drift `a` and volatility `σ`, as in
(1), (3), (4) of SSRN 3408260, pp.7–8, PDF 7–8) and times `α ≤ β` in `[0, ∞]`,
`discInt λ σ a B α β` is the discounted earning `∫_{[α, β)} e^{-λt} dX_t`, evaluated along one path
`B` by integration by parts:

`a (e^{-λα} − e^{-λβ})/λ + σ (e^{-λβ} B_β − e^{-λα} B_α + λ ∫_α^β e^{-λt} B_t dt)`,

with `e^{-λ·∞} := 0` and `e^{-λ·∞} B_∞ := 0`.

**Formalization Note.** Mathlib has no Itô integral. For the deterministic `C¹` integrand
`e^{-λt}` the Itô integral `∫ e^{-λt} dB_t` equals the pathwise integration-by-parts expression
above (almost surely), so this is the paper's integral. The paper's integrals `∫_0^τ`, `∫_τ^∞`
of (7), (8) are `discInt … 0 τ` and `discInt … τ ⊤`; when `τ = ∞` the second is `0`. -/
noncomputable def discInt (lam σ a : ℝ) (B : ℝ≥0 → ℝ) (α β : WithTop ℝ≥0) : ℝ :=
  a * (discFactor lam α - discFactor lam β) / lam
    + σ * (discPath lam B β - discPath lam B α
      + lam * ∫ t in window α β, Real.exp (-lam * t) * B t.toNNReal)

end CompInvestBayes


