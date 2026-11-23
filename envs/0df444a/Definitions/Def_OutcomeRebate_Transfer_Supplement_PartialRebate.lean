-- Prove2me | Definitions.Def_OutcomeRebate_Transfer_Supplement_PartialRebate
-- name    : OutcomeRebate_Transfer_Supplement_PartialRebate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:01:20.339787+00:00
-- url     : https://prove2.me/theorems/65183995-2ae7-4a6d-92bd-b3b2c36e2a47
-- title:
--   Appendix C — partial-rebate game from patient welfare and payoffs
-- statement:
--   Use the published parameters: $n$ patients, values uniform on $[0,\bar v]$, production cost $c$, success probability $q$, co-insurance $\beta$, curvature $\alpha$, loss aversion $\lambda$, and payer benefit $v'$. The **unrefunded fraction** $\theta\in[0,1]$ multiplies the payment on treatment failure. For patient share $\bar\beta$, define
--
--   $$m=\theta+q(1-\theta),\qquad \bar z=1+\theta(z-1),\qquad w(v)=q u(v-\bar\beta p)+(1-q)u(-\theta\bar\beta p).$$
--
--   Buyers are exactly $v\in[0,\bar v]$ with $w(v)\ge0$. Demand is $n/\bar v$ times their Lebesgue volume. Integrate $q(v-\bar\beta p)-(1-q)\theta\bar\beta p$ over these buyers to obtain patient payoff, and multiply demand by $qv'-q(1-\bar\beta)p-(1-q)\theta(1-\bar\beta)p$ for payer payoff. Their sum is the payer objective. Coverage means the objective at $\bar\beta=\beta$ is at least that at $\bar\beta=1$. Firm profit is $(mp-c)$ times demand; realized profit uses the share actually chosen by the payer. An equilibrium price is a nonnegative price maximizing realized profit over every nonnegative price.
--
--   The candidate covered and uncovered interior prices are $p^{P*}=c/(2m)+\bar v/(2\beta\bar z)$ and $\bar p^{P*}=c/(2m)+\bar v/(2\bar z)$. The applicable profitability assumption is $\beta c/\bar v<m/\bar z$, replacing Assumption 1. The game includes $\theta=0$ and $\theta=1$. Demand is derived from prospect-theory welfare rather than defined by a positive-part closed form.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), pp. 42–44 (PDF 43–45), Appendix C, payoff table and model

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer.Supplement

open MeasureTheory

/-- Fraction of the listed price received on average. θ is the unrefunded fraction. -/
def partialMargin (P : Params) (θ : ℝ) : ℝ := θ + P.q * (1 - θ)
noncomputable def zBar (P : Params) (θ : ℝ) : ℝ := 1 + θ * (P.z - 1)
/-- Appendix C replaces Assumption 1 by this inequality. -/
def PartialAssumption (P : Params) (θ : ℝ) : Prop :=
  P.β * P.c / P.vbar < partialMargin P θ / zBar P θ
noncomputable def welfareP (P : Params) (θ bb p v : ℝ) : ℝ :=
  P.q * u P.α P.lam (v - bb * p) + (1 - P.q) * u P.α P.lam (-(θ * bb * p))
def buyersP (P : Params) (θ bb p : ℝ) : Set ℝ :=
  {v ∈ Set.Icc 0 P.vbar | 0 ≤ welfareP P θ bb p v}
noncomputable def demandP (P : Params) (θ bb p : ℝ) : ℝ :=
  P.n / P.vbar * (volume (buyersP P θ bb p)).toReal
noncomputable def patientPayoffP (P : Params) (θ bb p : ℝ) : ℝ :=
  P.n / P.vbar * ∫ v in buyersP P θ bb p,
    (P.q * (v - bb * p) - (1 - P.q) * θ * bb * p)
noncomputable def payerPayoffP (P : Params) (θ bb p : ℝ) : ℝ :=
  demandP P θ bb p * (P.q * P.vp - P.q * (1 - bb) * p - (1 - P.q) * θ * (1 - bb) * p)
noncomputable def payerObjP (P : Params) (θ bb p : ℝ) : ℝ :=
  payerPayoffP P θ bb p + patientPayoffP P θ bb p
def coversP (P : Params) (θ p : ℝ) : Prop := payerObjP P θ 1 p ≤ payerObjP P θ P.β p
open Classical in
noncomputable def shareP (P : Params) (θ p : ℝ) : ℝ := if coversP P θ p then P.β else 1
noncomputable def firmProfitP (P : Params) (θ bb p : ℝ) : ℝ :=
  (partialMargin P θ * p - P.c) * demandP P θ bb p
noncomputable def realizedProfitP (P : Params) (θ p : ℝ) : ℝ := firmProfitP P θ (shareP P θ p) p
def IsEqPriceP (P : Params) (θ p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p' : ℝ, 0 ≤ p' → realizedProfitP P θ p' ≤ realizedProfitP P θ p
noncomputable def pPartialStar (P : Params) (θ : ℝ) : ℝ :=
  P.c / (2 * partialMargin P θ) + P.vbar / (2 * P.β * zBar P θ)
noncomputable def pPartialBarStar (P : Params) (θ : ℝ) : ℝ :=
  P.c / (2 * partialMargin P θ) + P.vbar / (2 * zBar P θ)

end OutcomeRebate.Transfer.Supplement


