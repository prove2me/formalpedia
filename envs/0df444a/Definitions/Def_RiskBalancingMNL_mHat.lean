-- Prove2me | Definitions.Def_RiskBalancingMNL_mHat
-- name    : RiskBalancingMNL_mHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:42.764584+00:00
-- url     : https://prove2.me/theorems/58e4ca6c-940e-40e2-a217-f8c51076ee19
-- title:
--   Zero-markup share $\bar\lambda$, the inverse markup $\hat m(q_0)$ of (12), the left side of (13), and $\tilde L(q_0)$ of (14)
-- statement:
--   Let $A=\sum_ie^{a_i-bc_i}$ be the total attraction at zero markups. The threshold
--   $$
--   \bar\lambda=\frac{A}{1+A}
--   $$
--   is the total market share the firm obtains by setting all markups to zero (p.11). The equal markup that produces the no-purchase probability $q_0$ is (12)
--   $$
--   \hat m(q_0)=\frac1b\Big[\log A+\log\frac{q_0}{1-q_0}\Big],
--   $$
--   the left side of the first-order condition (13) is
--   $$
--   \hat m(q_0)-\frac{1}{bq_0}+\frac{\lambda\,\hat m(q_0)}{2(1-q_0-\lambda)},
--   $$
--   and the objective as a function of $q_0$ is (14)
--   $$
--   \tilde L(q_0)=\hat m(q_0)^2(1-q_0)(1-q_0-\lambda).
--   $$
--
--   **Formalization Note** The paper prints the last term of (13) as $\hat m(q_0)/(2[(1-q_0)/\lambda-1])$. For $\lambda>0$ and $q_0\ne1-\lambda$ the two forms are equal; at $\lambda=0$ the printed one is undefined and this form gives its limit $0$. $\hat m$ is meaningful on $(0,1)$; at $q_0\in\{0,1\}$ Lean's conventions $\log0=0$ and $x/0=0$ give junk values, and every statement keeps $q_0$ inside an open subinterval of $(0,1)$.
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §4, p.11: (12), (13), (14), and the definition of $\bar\lambda$

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params

namespace RiskBalancingMNL

variable {n : ℕ}

/-- `A = Σᵢ e^{aᵢ − bcᵢ}`, the total attraction at zero markups (Li & Webster, SSRN 3959428,
(12), p.11). -/
noncomputable def zeroMarkupMass (P : Params n) : ℝ :=
  ∑ i, Real.exp (P.a i - P.b * P.c i)

/-- The threshold `λ̄ = Σᵢ e^{aᵢ−bcᵢ} / (1 + Σᵢ e^{aᵢ−bcᵢ})`, SSRN 3959428, p.11: "the total market
share the firm can accomplish by setting all product markups to zero". -/
noncomputable def lamBar (P : Params n) : ℝ :=
  zeroMarkupMass P / (1 + zeroMarkupMass P)

/-- The equal markup as a function of the no-purchase probability, (12), SSRN 3959428, p.11:
`m̂(q₀) = (1/b)[log(Σᵢ e^{aᵢ−bcᵢ}) + log(q₀/(1 − q₀))]`.

**Formalization Note** The formula is meaningful for `q₀ ∈ (0, 1)`; at `q₀ ∈ {0, 1}` Lean's
`log 0 = 0` and `x / 0 = 0` give junk values, and every statement using `mHat` keeps `q₀` in an
open subinterval of `(0, 1)`. -/
noncomputable def mHat (P : Params n) (x : ℝ) : ℝ :=
  (Real.log (zeroMarkupMass P) + Real.log (x / (1 - x))) / P.b

/-- The left side of the first-order condition (13), SSRN 3959428, p.11, in the form
`m̂(q₀) − 1/(bq₀) + λ m̂(q₀) / (2(1 − q₀ − λ))`.

**Formalization Note** The paper prints the last term as `m̂(q₀) / (2[(1 − q₀)/λ − 1])`. For
`λ > 0` and `q₀ ≠ 1 − λ` the two agree, since `(1 − q₀)/λ − 1 = (1 − q₀ − λ)/λ`. At `λ = 0` the
printed term is undefined (Lean would read `(1 − q₀)/0 = 0` and produce `−m̂/2`); this form gives
its limit `0`, the risk-neutral condition `m̂(q₀) = 1/(bq₀)`. -/
noncomputable def foc (P : Params n) (lam x : ℝ) : ℝ :=
  mHat P x - 1 / (P.b * x) + lam * mHat P x / (2 * (1 - x - lam))

/-- The objective as a function of the no-purchase probability, (14), SSRN 3959428, p.11:
`L̃(q₀) = m̂(q₀)² (1 − q₀)(1 − q₀ − λ)`. -/
noncomputable def LTilde (P : Params n) (lam x : ℝ) : ℝ :=
  mHat P x ^ 2 * (1 - x) * (1 - x - lam)

end RiskBalancingMNL


