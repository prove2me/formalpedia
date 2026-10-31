-- Prove2me | Definitions.Def_EllsbergLearning_Ellsberg
-- name    : EllsbergLearning_Ellsberg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:01.589502+00:00
-- url     : https://prove2.me/theorems/32e77c6c-596d-49b7-9811-865ebe133c1a
-- title:
--   Ellsberg's urns: the specification (17)–(19) (corrected: $u(a_0,\alpha)=\tfrac12-\alpha$), $\overline z$ of (23) and $\bar{\bar z}$
-- statement:
--   **Ellsberg's urns.** For $0<\alpha<\tfrac12$, $0<\epsilon<1$, volatility $\sigma$ and cost $c$: the parameter is the bias $\theta\in\{-\alpha,\alpha\}$ towards red, $\theta_0=-\alpha$, $\theta_1=\alpha$ (17); the priors give $\theta_1$ probability in $[\frac{1-\epsilon}{2},\frac{1+\epsilon}{2}]$ (18); $a_1$ ($a_0$) bets on red (blue) from the ambiguous urn and $a_2$ on the risky urn, with
--   $$u(a_0,-\alpha)=u(a_1,\alpha)=\tfrac12+\alpha,\qquad u(a_0,\alpha)=u(a_1,-\alpha)=\tfrac12-\alpha,\qquad u_2=\tfrac12 \quad(19).$$
--   For a root $\bar r$ of (24), the threshold (23) is
--   $$\overline z=\frac{\sigma^2}{2\alpha}\Big[\log\frac{1+\epsilon}{1-\epsilon}+\log\frac{\bar r}{1-\bar r}\Big],$$
--   and $\bar{\bar z}=\frac{\sigma^2}{2\alpha}\log\frac{1+\epsilon}{1-\epsilon}$ (§5.3).
--
--   **Formalization Note** (19) prints $u(a_0,\alpha)=u(a_1,-\alpha)=\alpha-\tfrac12$, which is negative for every admissible $\alpha$, against the nonnegativity of payoffs (p.11); the paper's (20), $u_2=\tfrac12(u_{00}+u_{10})$ (p.19) and $u_{11}-u_{10}=2\alpha$ (p.31) all use $\tfrac12-\alpha$, the probability of winning prize 1.
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §3.2, (17)–(19), pp.12–13; (23), p.14; §5.3, p.32

import Definitions.Def_EllsbergLearning_Params

noncomputable section

namespace EllsbergLearning

/-- The Ellsberg specification of §3.2 (arXiv:1708.01890v2, pp.12–13), for `0 < α < 1/2`,
`0 < ϵ < 1`, signal volatility `σ` and learning cost `c`:

* (17): `θ₀ = −α`, `θ₁ = α`;
* (18): `m̲₀ = (1 − ϵ)/2`, `m̄₀ = (1 + ϵ)/2`;
* (19), **corrected**: `u(a₀, −α) = u(a₁, α) = 1/2 + α`, `u(a₀, α) = u(a₁, −α) = 1/2 − α`,
  `u₂ = 1/2`; `a₁` (`a₀`) is the bet on red (blue) from the ambiguous urn, `a₂` the bet on the
  risky urn.

**Formalization Note (correction).** (19) prints `u(a₀, α) = u(a₁, −α) = α − 1/2`. That value is
negative for every `0 < α < 1/2`, against the standing assumption that payoffs are nonnegative
(p.11); the paper's own (20) (p.13) uses `1/2 − α`; the proof (p.31) uses
`u₁₁ − u₁₀ = 2α` and `u₂ = (u₀₀ + u₁₀)/2` (p.19), which hold only for `1/2 − α`. A winning
prize 1 and losing prize 0 give probability `1/2 − α` of winning. -/
def ellsberg (α ϵ σ c : ℝ) : Params where
  θ₀ := -α
  θ₁ := α
  σ := σ
  c := c
  mLo0 := (1 - ϵ) / 2
  mUp0 := (1 + ϵ) / 2
  u := ![![1 / 2 + α, 1 / 2 - α], ![1 / 2 - α, 1 / 2 + α]]
  u₂ := 1 / 2

/-- The stopping threshold (23), arXiv:1708.01890v2, p.14:
`z̄ = σ²/(2α) [log((1 + ϵ)/(1 − ϵ)) + log(r̄/(1 − r̄))]`, as a function of the root `r̄` of (24). -/
def zbar (α ϵ σ r : ℝ) : ℝ :=
  σ ^ 2 / (2 * α) * (Real.log ((1 + ϵ) / (1 - ϵ)) + Real.log (r / (1 - r)))

/-- The threshold `z̿ = σ²/(2α) log((1 + ϵ)/(1 − ϵ))` of §5.3, arXiv:1708.01890v2, p.32. -/
def zbarbar (α ϵ σ : ℝ) : ℝ := σ ^ 2 / (2 * α) * Real.log ((1 + ϵ) / (1 - ϵ))

end EllsbergLearning


