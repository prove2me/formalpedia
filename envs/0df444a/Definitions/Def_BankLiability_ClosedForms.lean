-- Prove2me | Definitions.Def_BankLiability_ClosedForms
-- name    : BankLiability_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:06.916998+00:00
-- url     : https://prove2.me/theorems/501bdd4b-7271-450a-96c4-ab675ef179e0
-- title:
--   Closed forms of Proposition 2 — $\pi$ (5), $D^*/V,B^*/V$ (6), $s^*,g^*$ (7) — and the regularity assumption (4)
-- statement:
--   The closed forms named by Proposition 2 are functions of the parameters only. The **state price of the regulatory total capital boundary** at the strategic structure is, by (5),
--
--   $$\pi=\frac{1}{1+\lambda}\cdot\frac{\eta(1-\tau)\lambda(1-\beta)+r\tau(1+\lambda)}{\eta(1-\tau)\lambda(1-\beta)+r\tau(1+\lambda)+r(1-\tau)\lambda[(1-\omega)\alpha+\omega\beta]} .$$
--
--   The deposit and nondeposit debt ratios of (6) are
--
--   $$\frac{D^*}{V}=(1-\beta)\pi^{1/\lambda},\qquad \frac{B^*}{V}=\Big(\frac{\tau}{1-\tau}+\beta+(1-\beta)\frac{\eta}{r}\frac{\lambda}{1+\lambda}+\frac{1-\pi}{\lambda}\Big)\pi^{1/\lambda},$$
--
--   and the credit spread and assessment rate of (7) are
--
--   $$s^*=\frac{r\pi}{1-\pi},\qquad g^*=(1-\omega)\frac{\alpha-\beta}{1-\beta}\cdot\frac{r\pi}{1-\pi}.$$
--
--   The **regularity assumption** (4) is $g^*<\eta/(1+\lambda)$: the risk-based assessment rate is small relative to the deposit service income, so deposits stay cheaper than nondeposit debt.
--
--   **Formalization Note** The paper writes (4) as $g<\eta/(1+\lambda)$ for the (structure-dependent) assessment rate $g$, and presents it as an assumption on the parameters. Required at every feasible deposit level it could not hold ($g^\circ\to\infty$ as $D/V\to1-\beta$ unless $\omega=1$), so it is read as the parameter condition $g^*<\eta/(1+\lambda)$ with $g^*$ from (7).
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, eqs. (4), (5), (6), (7), p.7

import Mathlib
import Definitions.Def_BankLiability_Params
import Definitions.Def_BankLiability_lam

namespace BankLiability

/-! The closed forms named by Proposition 2 of Sundaresan–Wang, *Strategic Bank Liability
Structure Under Capital Requirements*, Management Science (2023), doi:10.1287/mnsc.2022.4570,
Articles in Advance, p.7, equations (5), (6), (7), and the regularity assumption (4), p.7. They
are functions of the parameters only. -/

/-- **The state price π of the regulatory total capital boundary at the strategic structure**,
equation (5), p.7:
`π = 1/(1 + λ) · [η(1−τ)λ(1−β) + rτ(1+λ)] / [η(1−τ)λ(1−β) + rτ(1+λ) + r(1−τ)λ((1−ω)α + ωβ)]`. -/
noncomputable def statePrice (P : Params) : ℝ :=
  1 / (1 + lam P) *
    ((P.eta * (1 - P.tau) * lam P * (1 - P.beta) + P.r * P.tau * (1 + lam P)) /
      (P.eta * (1 - P.tau) * lam P * (1 - P.beta) + P.r * P.tau * (1 + lam P) +
        P.r * (1 - P.tau) * lam P * ((1 - P.omega) * P.alpha + P.omega * P.beta)))

/-- **Deposit ratio of (6)**, p.7: `D*/V = (1 − β)π^{1/λ}`. -/
noncomputable def depositRatioStar (P : Params) : ℝ :=
  (1 - P.beta) * statePrice P ^ (1 / lam P)

/-- **Nondeposit debt ratio of (6)**, p.7:
`B*/V = (τ/(1−τ) + β + (1−β)(η/r)(λ/(1+λ)) + (1−π)/λ) π^{1/λ}`. -/
noncomputable def debtRatioStar (P : Params) : ℝ :=
  (P.tau / (1 - P.tau) + P.beta + (1 - P.beta) * (P.eta / P.r) * (lam P / (1 + lam P)) +
      (1 - statePrice P) / lam P) * statePrice P ^ (1 / lam P)

/-- **Credit spread of (7)**, p.7: `s* = rπ/(1 − π)`. -/
noncomputable def spreadStar (P : Params) : ℝ :=
  P.r * statePrice P / (1 - statePrice P)

/-- **Assessment rate of (7)**, p.7: `g* = (1 − ω)(α − β)/(1 − β) · rπ/(1 − π)`. -/
noncomputable def assessRateStar (P : Params) : ℝ :=
  (1 - P.omega) * ((P.alpha - P.beta) / (1 - P.beta)) * (P.r * statePrice P / (1 - statePrice P))

/-- **Regularity assumption (4)**, p.7: `g < η/(1 + λ)`, read at the strategic structure: the
assessment rate `g*` of (7) is below `η/(1 + λ)`.

**Formalization Note (reading of (4)).** The paper writes (4) for the assessment rate `g`, which
depends on the liability structure, and calls it an assumption on the parameters ("we assume that
the insurance subsidy ω and the capital requirement β are high enough so that g < η/(1+λ)").
Required for every feasible deposit level it could never hold (`g° → ∞` as `D/V → 1 − β`, unless
ω = 1), so the assumption is read as the parameter condition `g* < η/(1 + λ)` with `g*` the
closed form (7). -/
def Regularity (P : Params) : Prop :=
  assessRateStar P < P.eta / (1 + lam P)

end BankLiability


