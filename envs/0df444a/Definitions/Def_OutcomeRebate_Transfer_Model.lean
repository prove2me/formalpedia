-- Prove2me | Definitions.Def_OutcomeRebate_Transfer_Model
-- name    : OutcomeRebate_Transfer_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:42.017006+00:00
-- url     : https://prove2.me/theorems/20d060de-51cd-47ce-8a32-d85ecbd6f74d
-- title:
--   §2–§3, pp. 8–20 — drug-pricing game: prospect-theory patients, payer coverage, firm price, uniform vs outcome-based pricing
-- statement:
--   The model of Adida's *Outcome-based pricing for new pharmaceuticals via rebates*: a three-stage game between a pharmaceutical firm, a payer (insurer) and $n$ patients, under two pricing systems.
--
--   **Data.** The parameters are $n > 0$ patients, values $V \sim \mathrm{U}[0,\bar v]$ with $\bar v > 0$, unit cost $c > 0$, co-insurance rate $\beta \in (0, 1/2]$, success probability $q \in (0,1)$, curvature $\alpha \in (0,1)$, loss aversion $\lambda \ge 1$ and the payer's surplus $v' \ge 0$ on treatment success. The patient cost share is $\bar\beta = \beta$ when the payer covers the drug and $\bar\beta = 1$ otherwise.
--
--   **Patients.** A patient evaluates payoffs with the prospect-theory value function
--   $$u(x) = \begin{cases} x^\alpha & x \ge 0,\\ -\lambda(-x)^\alpha & x < 0.\end{cases}$$
--   A patient with value $v$ who buys at price $p$ has expected welfare $q\,u(v-\bar\beta p) + (1-q)\,u(-\bar\beta p)$ under uniform pricing, where she pays on success and on failure, and $q\,u(v - \bar\beta p)$ under outcome-based pricing, where she pays only on success. She buys iff this is $\ge 0$. Demand is $n/\bar v$ times the Lebesgue measure of the buyers in $[0,\bar v]$. The total expected (risk-neutral) patient payoff $\Pi_{\text{patient}}$ is $n/\bar v$ times the integral over the buyers of $q(v-\bar\beta p) - (1-q)\bar\beta p$ (uniform) or of $q(v - \bar\beta p)$ (outcome-based).
--
--   **Payer.** Its payoff is demand times $qv' - (1-\bar\beta)p$ (uniform) or $q\,(v' - (1-\bar\beta)p)$ (outcome-based). Its objective is $W_{\text{payer}} = \Pi_{\text{payer}} + \Pi_{\text{patient}}$. It covers the drug at price $p$ iff $W_{\text{payer}}|_{\bar\beta=\beta} \ge W_{\text{payer}}|_{\bar\beta=1}$.
--
--   **Firm.** Its profit is $\Pi^U_{\text{firm}}(p;\bar\beta) = (p - c)\cdot$demand or $\Pi^O_{\text{firm}}(p;\bar\beta) = (qp - c)\cdot$demand, evaluated at the payer's chosen $\bar\beta$. An **equilibrium price** is a $p \ge 0$ maximizing this realized profit over all prices $p' \ge 0$.
--
--   **Constants.** The paper's constants are
--   $$z = 1 + \Big(\lambda\tfrac{1-q}{q}\Big)^{1/\alpha},\quad q_0 = \frac{1}{1+\lambda^{-1/(1-\alpha)}},\quad p^* = \frac c2 + \frac{\bar v}{2\beta z},\quad \tilde p^* = \frac{c}{2q} + \frac{\bar v}{2\beta},$$
--   $$M' = \frac{\bar v}{2}\Big(\frac{\bar v}{z\beta^2 c} - 1\Big) + \frac{\beta c\,(2/\beta - 1 - zq)}{4q}.$$
--   A drug is high-risk when $q < q_0$. **Assumption 1** is $\beta c/\bar v < \min\{q, 1/z\}$. **Assumption 2** is $v' \ge \tilde p^*(1-\beta/2) - \bar v/2$ together with either $q \le q_1$ or $v' \ge p^*(1/q - z\beta/2) - \bar v/2$, where $q_1$ solves $zq = 2/\beta$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real numbers. Two hypotheses are added to the page's standing assumptions: $c > 0$ (the constant $M'$ divides by $c$) and $v' \ge 0$ (used in the proof of Theorem 1, p. 54). Ties follow the page: an indifferent patient buys, and an indifferent payer covers. The root $q_1$ is an argument of `Assumption2`, and every theorem passes it together with the hypothesis that it solves $zq = 2/\beta$ on $(0,1)$; the milestone `zq_monotone` shows that such a root is unique. Demand and patient payoff are a Lebesgue measure and a set integral over an interval of $[0,\bar v]$, so no non-integrable junk value arises; the closed forms are the milestones `closed_forms_uniform` and `closed_forms_outcome`. `Real.rpow` is only applied to non-negative bases.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), pp. 8–20 (PDF 9–21), §2 (model, value function u p. 12, Assumption 1, q0 and Definition 1 p. 14), §3 (demand, payer objective, firm profit, p∗ p. 16, p̃∗ p. 19), Assumption 2 p. 20, M′ in Proposition 3 part 6 p. 21; coverage rule ∆ ≥ 0 from the proof of Proposition 1, p. 50 (PDF 51)

import Mathlib

namespace OutcomeRebate.Transfer

open MeasureTheory

/-- The primitive data of Adida's drug-pricing game (§2, pp. 8–14): number of patients `n`,
upper end `vbar` (v̄) of the patients' value distribution `U[0, v̄]`, unit cost `c`, co-insurance
rate `β`, probability of treatment success `q`, prospect-theory curvature `α`, loss-aversion
coefficient `lam` (λ), and the payer's surplus `vp` (v′) in case of treatment success. -/
structure Params where
  n : ℝ
  vbar : ℝ
  c : ℝ
  β : ℝ
  q : ℝ
  α : ℝ
  lam : ℝ
  vp : ℝ

/-- The standing assumptions of §2: `n > 0`, `v̄ > 0`, `c > 0` (added: `M′` divides by `c`),
`0 < β ≤ 1/2` (p. 8, "β ≤ 50%"), `q ∈ (0,1)` (p. 8), `0 < α < 1` and `λ ≥ 1` (p. 12), and
`v′ ≥ 0` (added: used in the proof of Theorem 1, p. 54). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.n ∧ 0 < P.vbar ∧ 0 < P.c ∧ 0 < P.β ∧ P.β ≤ 1 / 2 ∧ 0 < P.q ∧ P.q < 1 ∧
    0 < P.α ∧ P.α < 1 ∧ 1 ≤ P.lam ∧ 0 ≤ P.vp

/-- The prospect-theory value function of p. 12: `u(x) = x^α` for `x ≥ 0` and
`u(x) = −λ(−x)^α` for `x < 0` (real powers of non-negative bases only). -/
noncomputable def u (α lam x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ α else -(lam * (-x) ^ α)

/-- `z = 1 + (λ(1−q)/q)^{1/α}` of Assumption 1 (p. 14), as a function of the success
probability `q`. -/
noncomputable def zOf (α lam q : ℝ) : ℝ :=
  1 + (lam * (1 - q) / q) ^ (1 / α)

/-- `z` at the model's own success probability. -/
noncomputable def Params.z (P : Params) : ℝ :=
  zOf P.α P.lam P.q

/-- The risk threshold `q₀ = 1 / (1 + λ^{−1/(1−α)})` (p. 14). A drug is high-risk when
`q < q₀` and low-risk when `q > q₀` (Definition 1, p. 14). -/
noncomputable def q0 (α lam : ℝ) : ℝ :=
  1 / (1 + lam ^ (-(1 / (1 - α))))

/-- Assumption 1 (p. 14): `βc/v̄ < min {q, 1/z}`. -/
def Assumption1 (P : Params) : Prop :=
  P.β * P.c / P.vbar < min P.q (1 / P.z)

/-- Expected prospect-theory welfare under uniform pricing of a patient with value `v` who buys
at price `p` and cost share `bb` (β̄): `q·u(v − β̄p) + (1 − q)·u(−β̄p)` (§3.1.1, p. 14). -/
noncomputable def welfareU (P : Params) (bb p v : ℝ) : ℝ :=
  P.q * u P.α P.lam (v - bb * p) + (1 - P.q) * u P.α P.lam (-(bb * p))

/-- Expected prospect-theory welfare under outcome-based pricing: `q·u(v − β̄p)` (§3.2.1, p. 18;
on failure the patient pays nothing, and `u(0) = 0`). -/
noncomputable def welfareO (P : Params) (bb p v : ℝ) : ℝ :=
  P.q * u P.α P.lam (v - bb * p)

/-- The patients who buy under uniform pricing: values `v ∈ [0, v̄]` with non-negative
expected welfare (an indifferent patient buys). -/
def buyersU (P : Params) (bb p : ℝ) : Set ℝ :=
  {v ∈ Set.Icc 0 P.vbar | 0 ≤ welfareU P bb p v}

/-- The patients who buy under outcome-based pricing. -/
def buyersO (P : Params) (bb p : ℝ) : Set ℝ :=
  {v ∈ Set.Icc 0 P.vbar | 0 ≤ welfareO P bb p v}

/-- Expected demand under uniform pricing: `n` times the `U[0, v̄]`-probability of buying. -/
noncomputable def demandU (P : Params) (bb p : ℝ) : ℝ :=
  P.n / P.vbar * (volume (buyersU P bb p)).toReal

/-- Expected demand under outcome-based pricing. -/
noncomputable def demandO (P : Params) (bb p : ℝ) : ℝ :=
  P.n / P.vbar * (volume (buyersO P bb p)).toReal

/-- Total expected (risk-neutral) patient payoff under uniform pricing, `Π^U_patient`:
a buyer with value `v` gets `v − β̄p` on success and `−β̄p` on failure. -/
noncomputable def patientPayoffU (P : Params) (bb p : ℝ) : ℝ :=
  P.n / P.vbar * ∫ v in buyersU P bb p, (P.q * (v - bb * p) - (1 - P.q) * (bb * p))

/-- Total expected patient payoff under outcome-based pricing, `Π^O_patient`: a buyer gets
`v − β̄p` on success and `0` on failure. -/
noncomputable def patientPayoffO (P : Params) (bb p : ℝ) : ℝ :=
  P.n / P.vbar * ∫ v in buyersO P bb p, P.q * (v - bb * p)

/-- Payer's expected payoff under uniform pricing, `Π^U_payer`: per buyer, cost `(1 − β̄)p`
and surplus `v′` with probability `q`. -/
noncomputable def payerPayoffU (P : Params) (bb p : ℝ) : ℝ :=
  demandU P bb p * (P.q * P.vp - (1 - bb) * p)

/-- Payer's expected payoff under outcome-based pricing, `Π^O_payer`: per buyer,
`v′ − (1 − β̄)p` on success and `0` on failure. -/
noncomputable def payerPayoffO (P : Params) (bb p : ℝ) : ℝ :=
  demandO P bb p * (P.q * (P.vp - (1 - bb) * p))

/-- The payer's objective under uniform pricing, `W^U_payer = Π^U_payer + Π^U_patient`. -/
noncomputable def payerObjU (P : Params) (bb p : ℝ) : ℝ :=
  payerPayoffU P bb p + patientPayoffU P bb p

/-- The payer's objective under outcome-based pricing, `W^O_payer = Π^O_payer + Π^O_patient`. -/
noncomputable def payerObjO (P : Params) (bb p : ℝ) : ℝ :=
  payerPayoffO P bb p + patientPayoffO P bb p

/-- The firm's expected profit under uniform pricing, `Π^U_firm(p; β̄) = (p − c)·demand`. -/
noncomputable def firmProfitU (P : Params) (bb p : ℝ) : ℝ :=
  (p - P.c) * demandU P bb p

/-- The firm's expected profit under outcome-based pricing, `Π^O_firm(p; β̄) = (qp − c)·demand`. -/
noncomputable def firmProfitO (P : Params) (bb p : ℝ) : ℝ :=
  (P.q * p - P.c) * demandO P bb p

/-- Payer stage, uniform pricing: the payer covers the drug at price `p` iff its objective with
coverage (`β̄ = β`) is at least its objective without (`β̄ = 1`), i.e. `ΔU ≥ 0`
(proof of Proposition 1, p. 50). -/
def coversU (P : Params) (p : ℝ) : Prop :=
  payerObjU P 1 p ≤ payerObjU P P.β p

/-- Payer stage, outcome-based pricing: cover iff `ΔO ≥ 0`. -/
def coversO (P : Params) (p : ℝ) : Prop :=
  payerObjO P 1 p ≤ payerObjO P P.β p

open Classical in
/-- The patient cost share `β̄` chosen by the payer at price `p` under uniform pricing. -/
noncomputable def shareU (P : Params) (p : ℝ) : ℝ :=
  if coversU P p then P.β else 1

open Classical in
/-- The patient cost share `β̄` chosen by the payer at price `p` under outcome-based pricing. -/
noncomputable def shareO (P : Params) (p : ℝ) : ℝ :=
  if coversO P p then P.β else 1

/-- The firm's realized profit at price `p` under uniform pricing, given the payer's response. -/
noncomputable def realizedProfitU (P : Params) (p : ℝ) : ℝ :=
  firmProfitU P (shareU P p) p

/-- The firm's realized profit at price `p` under outcome-based pricing. -/
noncomputable def realizedProfitO (P : Params) (p : ℝ) : ℝ :=
  firmProfitO P (shareO P p) p

/-- The payer's realized objective at price `p` under uniform pricing. -/
noncomputable def realizedObjU (P : Params) (p : ℝ) : ℝ :=
  payerObjU P (shareU P p) p

/-- The payer's realized objective at price `p` under outcome-based pricing. -/
noncomputable def realizedObjO (P : Params) (p : ℝ) : ℝ :=
  payerObjO P (shareO P p) p

/-- Firm stage, uniform pricing: `p ≥ 0` is an equilibrium price iff it maximizes the realized
profit over all prices `p′ ≥ 0` (backward induction, p. 14). -/
def IsEqPriceU (P : Params) (p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p' : ℝ, 0 ≤ p' → realizedProfitU P p' ≤ realizedProfitU P p

/-- Firm stage, outcome-based pricing. -/
def IsEqPriceO (P : Params) (p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p' : ℝ, 0 ≤ p' → realizedProfitO P p' ≤ realizedProfitO P p

/-- `p∗ = c/2 + v̄/(2βz)` (p. 16). -/
noncomputable def pStar (P : Params) : ℝ :=
  P.c / 2 + P.vbar / (2 * P.β * P.z)

/-- `p̃∗ = c/(2q) + v̄/(2β)` (p. 19). -/
noncomputable def pTilde (P : Params) : ℝ :=
  P.c / (2 * P.q) + P.vbar / (2 * P.β)

/-- `M′ = v̄(v̄/(zβ²c) − 1)/2 + βc(2/β − 1 − zq)/(4q)` (Proposition 3 part 6, p. 21). -/
noncomputable def Mprime (P : Params) : ℝ :=
  P.vbar * (P.vbar / (P.z * P.β ^ 2 * P.c) - 1) / 2 +
    P.β * P.c * (2 / P.β - 1 - P.z * P.q) / (4 * P.q)

/-- Assumption 2 (p. 20): `v′ ≥ p̃∗(1 − β/2) − v̄/2` and either `q ≤ q₁` or
`v′ ≥ p∗(1/q − zβ/2) − v̄/2`, where `q₁` (passed as an argument) is the solution of `zq = 2/β`. -/
def Assumption2 (P : Params) (q1 : ℝ) : Prop :=
  pTilde P * (1 - P.β / 2) - P.vbar / 2 ≤ P.vp ∧
    (P.q ≤ q1 ∨ pStar P * (1 / P.q - P.z * P.β / 2) - P.vbar / 2 ≤ P.vp)

end OutcomeRebate.Transfer


