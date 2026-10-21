-- Prove2me | Definitions.Def_DataTrackComp_Surplus_Game
-- name    : DataTrackComp_Surplus_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:03.910717+00:00
-- url     : https://prove2.me/theorems/5658e8aa-27ea-493c-a0d1-8542c4937315
-- title:
--   §2, App. A, pp. 7–11, 31–35 — two-firm two-product data-tracking game: utilities (2.1)–(2.4), three settings, PBE, consumer surplus
-- statement:
--   This file sets up the model of Bimpikis, Morgenstern and Saban's *Data Tracking under Competition* and its equilibrium notion.
--
--   **Types and prior.** A consumer has a type $\tau=(s,\theta)\in T=[0,1]\times[0,1]$: $s$ is her location on a Hotelling line for product 1 (firm A sits at $0$, firm B at $1$), and $m\theta$ is her valuation for product 2, where $m>0$ is the value of consumer data. The type is drawn from the uniform distribution $\mu_0$ on the unit square.
--
--   **Utilities and profits.** Firms A and B set product-1 prices $p^A_1\in S_A=[0,1]$ and $p^B_1\in S_B=[-1/2,1]$. With baseline utility $\bar u>0$ and unit transportation cost $1/2$, the consumer's product-1 utility is
--   $$u_1(a_1;s,\theta,p^A_1,p^B_1)=(1-a_1)\left(\bar u-\tfrac{s}{2}-p^A_1\right)+a_1\left(\bar u-\tfrac{1-s}{2}-p^B_1\right),\qquad(2.1)$$
--   where $a_1=1$ means buying from firm B; product 1 is always bought from one of the two firms. Firm B alone sells product 2, at a price $p$; buying it yields $u_2=m\theta-p$ and firm B earns $p$ ((2.2), (2.4)), while firm A earns $p^A_1$ when chosen and firm B earns $p^B_1$ when chosen (2.3).
--
--   **Data tracking.** If the consumer bought product 1 from firm B, firm B observes her type before pricing product 2 and can price it per type, at $p^T(\tau)$. Otherwise it only recalls the product-1 prices and sets one price $p^U$, given a belief over types.
--
--   **Three settings.** In the *forward-looking* setting, the consumer chooses her product-1 seller to maximize $u_1+u_2$, anticipating firm B's product-2 prices. In the *myopic* setting, tracking is the same but she maximizes $u_1$ only. In the *restricted* setting there is no tracking: firm B's period-2 information is the product-1 prices only, so it charges one price $p^U$ to everyone and its belief is the prior $\mu_0$.
--
--   **Continuation equilibrium.** After product-1 prices $(p^A_1,p^B_1)$, a continuation consists of the consumer's mixed period-1 choice $\gamma_1(\tau)\in[0,1]$ (the probability of buying from B), firm B's tracked prices $p^T(\tau)$, its untracked price $p^U$ and its untracked belief. It is an equilibrium of the continuation game when the following four conditions hold:
--
--   1. at every type of the square, the consumer buys from B with positive probability only if that is weakly optimal for her objective, and from A with positive probability only if that is;
--   2. with tracking, $p^T(\tau)$ maximizes firm B's product-2 revenue against every type $\tau$ of the square;
--   3. the belief is a probability measure on the square, and $p^U$ maximizes expected revenue under it;
--   4. with tracking, the belief is the Bayes posterior of $\mu_0$ given that the consumer bought from A, whenever that event has positive prior probability, and is otherwise unrestricted; in the restricted setting the belief is $\mu_0$.
--
--   **Perfect Bayesian equilibrium.** An assessment consists of product-1 prices $(p^A_1,p^B_1)$ and a continuation after every pair of prices. It is an equilibrium (Appendix A.3, A.4) if the following hold:
--
--   1. the prices lie in $S_A\times S_B$;
--   2. the continuation is a continuation equilibrium after every price pair in $S_A\times S_B$;
--   3. neither firm can raise its expected total profit, computed under $\mu_0$ with the continuation that its deviation triggers, by changing its own product-1 price within its action space.
--
--   The **aggregate consumer surplus** of an assessment is the $\mu_0$-expectation of $u_1+u_2$ along its equilibrium path.
--
--   **Formalization Note.** The following conventions are fixed by this file.
--
--   - Types are pairs $(s,\theta)\in\mathbb R\times\mathbb R$, and $\mu_0$ is the product of Lebesgue measure restricted to $[0,1]$ with itself.
--   - The consumer buys product 2 if and only if $p\le m\theta$. At a tracked node this tie-break is forced: otherwise firm B would have no optimal price. At the untracked node, ties have prior probability zero.
--   - Period-1 indifference may be resolved by any mixing; this choice is not made $\mu_0$-almost everywhere but at every type.
--   - $\gamma_1$ and $p^T$ are required to be $\mu_0$-a.e. measurable, so that the expectations are genuine integrals.
--   - Firm B's product-2 prices are pure (p. 33).
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), pp. 7–11 and 31–35 (PDF 7–11, 31–35), §2 (eqs. (2.1)–(2.4)), Appendix A.1–A.4, footnote 20

import Mathlib

open MeasureTheory

namespace DataTrackComp.Surplus

/-- A consumer type `τ = (s, θ)`: `τ.1 = s` is the Hotelling location for product 1,
`τ.2 = θ` scales the valuation `m θ` for product 2 (§2, p. 8). -/
abbrev Ty := ℝ × ℝ

/-- The type space `T = [0,1] × [0,1]`. -/
def square : Set Ty := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- The prior `μ0`: the uniform distribution on the unit square (p. 8). -/
noncomputable def μ0 : Measure Ty :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- Firm A's period-1 action space `S_A = [0,1]` (footnote 20, p. 33). -/
def SA : Set ℝ := Set.Icc 0 1

/-- Firm B's period-1 action space `S_B = [-1/2,1]` (footnote 20, p. 33). -/
def SB : Set ℝ := Set.Icc (-1 / 2) 1

/-- The three settings of §2, p. 11 and Appendix A.4. -/
inductive Setting
  | forward
  | myopic
  | restricted

/-- (2.1) with `a1 = 0`: product-1 utility when buying from firm A. -/
noncomputable def u1A (ubar pA : ℝ) (τ : Ty) : ℝ := ubar - τ.1 / 2 - pA

/-- (2.1) with `a1 = 1`: product-1 utility when buying from firm B. -/
noncomputable def u1B (ubar pB : ℝ) (τ : Ty) : ℝ := ubar - (1 - τ.1) / 2 - pB

/-- (2.2) under the purchase rule "buy product 2 iff `p ≤ m θ`". -/
noncomputable def u2 (m p : ℝ) (τ : Ty) : ℝ := if p ≤ m * τ.2 then m * τ.2 - p else 0

/-- (2.4) under the same purchase rule: firm B's product-2 revenue at price `p`. -/
noncomputable def rev2 (m p : ℝ) (τ : Ty) : ℝ := if p ≤ m * τ.2 then p else 0

/-- What follows a pair of product-1 prices: the consumer's period-1 mixed choice
(`γ1 τ` = probability of buying product 1 from firm B), firm B's product-2 price `pT τ`
for a consumer whose type it tracked, and its price `pU` and belief `belief` at the
information set where it did not observe the type. -/
structure Cont where
  γ1 : Ty → ℝ
  pT : Ty → ℝ
  pU : ℝ
  belief : Measure Ty

/-- The consumer's period-1 objective when buying product 1 from firm B. -/
noncomputable def VB : Setting → ℝ → ℝ → ℝ → Cont → Ty → ℝ
  | .forward, ubar, m, pB, c, τ => u1B ubar pB τ + u2 m (c.pT τ) τ
  | .myopic, ubar, _, pB, _, τ => u1B ubar pB τ
  | .restricted, ubar, m, pB, c, τ => u1B ubar pB τ + u2 m c.pU τ

/-- The consumer's period-1 objective when buying product 1 from firm A. -/
noncomputable def VA : Setting → ℝ → ℝ → ℝ → Cont → Ty → ℝ
  | .forward, ubar, m, pA, c, τ => u1A ubar pA τ + u2 m c.pU τ
  | .myopic, ubar, _, pA, _, τ => u1A ubar pA τ
  | .restricted, ubar, m, pA, c, τ => u1A ubar pA τ + u2 m c.pU τ

/-- Consistency of firm B's belief at the untracked information set (Appendix A.3 (iv)(b),
A.4). With tracking, the belief is the Bayes posterior of `μ0` given that the consumer bought
from firm A, whenever that event has positive prior probability (otherwise unrestricted);
in the restricted setting the information set is reached by every type, so the belief is `μ0`. -/
noncomputable def BeliefConsistent : Setting → Cont → Prop
  | .restricted, c => c.belief = μ0
  | _, c =>
      (∫⁻ τ, ENNReal.ofReal (1 - c.γ1 τ) ∂μ0) ≠ 0 →
        c.belief = (∫⁻ τ, ENNReal.ofReal (1 - c.γ1 τ) ∂μ0)⁻¹ •
          μ0.withDensity (fun τ => ENNReal.ofReal (1 - c.γ1 τ))

/-- Firm B's sequential rationality at tracked nodes: for each observed type, the product-2
price maximizes revenue. Only with data tracking; vacuous in the restricted setting. -/
def TrackedRational : Setting → ℝ → Cont → Prop
  | .restricted, _, _ => True
  | _, m, c => ∀ τ ∈ square, ∀ p : ℝ, rev2 m p τ ≤ rev2 m (c.pT τ) τ

/-- `c` is an equilibrium of the continuation game after product-1 prices `(pA, pB)`
(Appendix A.3 conditions (i), (ii) for period 2, (iv); modified per A.4). -/
def IsContEq (S : Setting) (ubar m pA pB : ℝ) (c : Cont) : Prop :=
  AEMeasurable c.γ1 μ0 ∧ AEMeasurable c.pT μ0 ∧
  (∀ τ, c.γ1 τ ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ τ ∈ square, (0 < c.γ1 τ → VA S ubar m pA c τ ≤ VB S ubar m pB c τ) ∧
      (c.γ1 τ < 1 → VB S ubar m pB c τ ≤ VA S ubar m pA c τ)) ∧
  TrackedRational S m c ∧
  IsProbabilityMeasure c.belief ∧ c.belief squareᶜ = 0 ∧
  (∀ p : ℝ, ∫ τ, rev2 m p τ ∂c.belief ≤ ∫ τ, rev2 m c.pU τ ∂c.belief) ∧
  BeliefConsistent S c

/-- Firm A's expected profit (2.3) at prices `(pA, ·)` and continuation `c`. -/
noncomputable def profitA (pA : ℝ) (c : Cont) : ℝ := pA * ∫ τ, (1 - c.γ1 τ) ∂μ0

/-- Firm B's expected total profit (2.3)+(2.4) at product-1 price `pB` and continuation `c`. -/
noncomputable def profitB : Setting → ℝ → ℝ → Cont → ℝ
  | .restricted, m, pB, c => ∫ τ, (c.γ1 τ * pB + rev2 m c.pU τ) ∂μ0
  | _, m, pB, c =>
      ∫ τ, (c.γ1 τ * (pB + rev2 m (c.pT τ) τ) + (1 - c.γ1 τ) * rev2 m c.pU τ) ∂μ0

/-- Expected aggregate consumer utility `E_{μ0}[u1 + u2]` at prices `(pA, pB)` and
continuation `c`. -/
noncomputable def surplus : Setting → ℝ → ℝ → ℝ → ℝ → Cont → ℝ
  | .restricted, ubar, m, pA, pB, c =>
      ∫ τ, (c.γ1 τ * u1B ubar pB τ + (1 - c.γ1 τ) * u1A ubar pA τ + u2 m c.pU τ) ∂μ0
  | _, ubar, m, pA, pB, c =>
      ∫ τ, (c.γ1 τ * (u1B ubar pB τ + u2 m (c.pT τ) τ) +
        (1 - c.γ1 τ) * (u1A ubar pA τ + u2 m c.pU τ)) ∂μ0

/-- An assessment: the firms' product-1 prices and a continuation after every price pair. -/
structure Assessment where
  pA : ℝ
  pB : ℝ
  cont : ℝ → ℝ → Cont

/-- Perfect Bayesian equilibrium (Appendix A.3, A.4): prices in `S_A × S_B`, an equilibrium
continuation after every price pair in `S_A × S_B`, and each firm's product-1 price a best
response given the continuation. -/
def IsEquilibrium (S : Setting) (ubar m : ℝ) (E : Assessment) : Prop :=
  E.pA ∈ SA ∧ E.pB ∈ SB ∧
  (∀ a ∈ SA, ∀ b ∈ SB, IsContEq S ubar m a b (E.cont a b)) ∧
  (∀ a ∈ SA, profitA a (E.cont a E.pB) ≤ profitA E.pA (E.cont E.pA E.pB)) ∧
  (∀ b ∈ SB, profitB S m b (E.cont E.pA b) ≤ profitB S m E.pB (E.cont E.pA E.pB))

/-- Equilibrium aggregate consumer surplus of assessment `E` in setting `S`. -/
noncomputable def consumerSurplus (S : Setting) (ubar m : ℝ) (E : Assessment) : ℝ :=
  surplus S ubar m E.pA E.pB (E.cont E.pA E.pB)

end DataTrackComp.Surplus


