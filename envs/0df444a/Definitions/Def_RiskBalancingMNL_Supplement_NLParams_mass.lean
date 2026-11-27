-- Prove2me | Definitions.Def_RiskBalancingMNL_Supplement_NLParams_mass
-- name    : RiskBalancingMNL_Supplement_NLParams_mass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:56:34.895729+00:00
-- url     : https://prove2.me/theorems/da74c0d6-8ccb-5e93-a96b-82de83b671b4
-- title:
--   Nested logit one-variable objects: $S$, $\bar\lambda$, $\hat m(Q_0)$ (31), the first-order expression and $\tilde L(Q_0)$ (30)
-- statement:
--   For the nested logit model with common $b$ and $\tau$, put
--   $$
--   S=\sum_k\Big(\sum_{i=1}^{M_k}e^{a_{ik}-b_kc_{ik}}\Big)^{\tau_k},\qquad \bar\lambda=\frac{S}{1+S},\qquad \hat m(Q_0)=\frac1{b\tau}\Big[\log S+\log\frac{Q_0}{1-Q_0}\Big].
--   $$
--   The first-order expression and the one-variable objective are
--   $$
--   \mathrm{foc}_\lambda(Q_0)=\hat m(Q_0)-\frac1{b\tau Q_0}+\frac{\lambda\,\hat m(Q_0)}{2(1-Q_0-\lambda)},\qquad \tilde L_\lambda(Q_0)=\hat m(Q_0)^2(1-Q_0)(1-Q_0-\lambda).
--   $$
--   $\hat m$ is the equal markup whose no-purchase probability is $Q_0$, and (31) is $m^*(\lambda)=\hat m(Q_0^*(\lambda))$.
--
--   **Formalization Note** $b$ and $\tau$ are explicit arguments, because Theorem 5 assumes $b_k=b$, $\tau_k=\tau$; under that assumption $S$ is the printed $\sum_k(\sum_je^{a_{jk}-bc_{jk}})^\tau$. The power is written $\exp(\tau_k\log\cdot)$ of a positive base. The paper prints the last term of the first-order expression as $\hat m/(2[(1-Q_0)/\lambda-1])$, which agrees for $\lambda>0$; the form used here has the limit $0$ at $\lambda=0$. $\hat m$ is meaningful for $Q_0\in(0,1)$.
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), Theorem 5 (ii), $\bar\lambda$, the first-order equation and (31), p.24; (30), p.24

import Mathlib
import Definitions.Def_RiskBalancingMNL_Supplement_NLParams

namespace RiskBalancingMNL.Supplement

namespace NLParams

variable {K : ℕ} {M : Fin K → ℕ}

/-- `S = Σₖ (Σᵢ e^{aᵢₖ − bₖcᵢₖ})^{τₖ}`, the total nest attraction at zero markups, Li & Webster,
SSRN 3959428 (PDF of 2021-11-14), Theorem 5(ii) and (31), p.24.

**Formalization Note** `(Σᵢ e^{aᵢₖ − bₖcᵢₖ})^{τₖ}` is written `exp(τₖ log Σᵢ e^{aᵢₖ − bₖcᵢₖ})`, the
paper's `e^{τₖIₖ}` at zero markups; the base is positive because every nest is nonempty. -/
noncomputable def mass (P : NLParams K M) : ℝ :=
  ∑ k, Real.exp (P.τ k * Real.log (∑ i, Real.exp (P.a k i - P.b k * P.c k i)))

/-- `λ̄ = S / (1 + S)`, SSRN 3959428, Theorem 5(ii), p.24. -/
noncomputable def lamBar (P : NLParams K M) : ℝ :=
  P.mass / (1 + P.mass)

/-- The equal markup as a function of the no-purchase probability, (31), SSRN 3959428, p.24:
`m̂(Q₀) = (1/(bτ)) [log S + log(Q₀/(1 − Q₀))]`, for common `b` and `τ`.

**Formalization Note** `b` and `τ` are explicit arguments: Theorem 5 assumes `bₖ = b`, `τₖ = τ`
for all `k`. Meaningful for `Q₀ ∈ (0, 1)`; Lean's `log 0 = 0` and `x / 0 = 0` give junk values
at `Q₀ ∈ {0, 1}`, and every statement keeps `Q₀` in an open subinterval of `(0, 1)`. -/
noncomputable def mHat (P : NLParams K M) (b τ x : ℝ) : ℝ :=
  (Real.log P.mass + Real.log (x / (1 - x))) / (b * τ)

/-- The left side of the first-order equation of Theorem 5(ii), SSRN 3959428, p.24, in the form
`m̂(Q₀) − 1/(bτQ₀) + λ m̂(Q₀) / (2(1 − Q₀ − λ))`.

**Formalization Note** The paper prints the last term as `m̂(Q₀) / (2[(1 − Q₀)/λ − 1])`; for
`λ > 0` and `Q₀ ≠ 1 − λ` the two agree. At `λ = 0` the printed term is undefined, and this form
gives its limit `0` (as the published `RiskBalancingMNL.foc`). -/
noncomputable def foc (P : NLParams K M) (b τ lam x : ℝ) : ℝ :=
  P.mHat b τ x - 1 / (b * τ * x) + lam * P.mHat b τ x / (2 * (1 - x - lam))

/-- The objective as a function of the no-purchase probability, (30), SSRN 3959428, p.24:
`L̃(Q₀) = m̂(Q₀)² (1 − Q₀)(1 − Q₀ − λ)`. -/
noncomputable def LTilde (P : NLParams K M) (b τ lam x : ℝ) : ℝ :=
  P.mHat b τ x ^ 2 * (1 - x) * (1 - x - lam)

end NLParams

end RiskBalancingMNL.Supplement


