-- Prove2me | Definitions.Def_VaccineAMC_Framework_Model
-- name    : VaccineAMC_Framework_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:33.027877+00:00
-- url     : https://prove2.me/theorems/60c63670-fac4-4f8b-9183-49c97820df2e
-- title:
--   Framework AMC model and equilibrium
-- statement:
--   The model has a donor, a monopolist vaccine producer, and a country receiving vaccinations. The parameter tuple $\theta=(r,\alpha,\beta,c,K,B)$ contains the positive discount rate, donor altruism, firm bargaining weight, production cost per unit, sunk capacity cost per unit, and country benefit function. Standing assumptions require $0<\alpha,\beta<1$, $B(0)=0$, $B'(q)>0$, $B''(q)<0$ for $q\geq0$, and $B'(q)\to0$. Write $\kappa=rK$, $P(q)=\alpha B'(q)$, $\bar p=P(0)$, and $D(p)=\inf\{q\geq0:P(q)\leq p\}$. Assumption 1 is $c+\kappa<\bar p$.
--
--   Integrated welfare discounts the flow $\alpha B(q)-cq$ and subtracts $KQ$. Without an AMC, the Nash bargain maximizes that joint flow at output $q\leq Q$; the firm's continuation value is $\beta$ times the maximal joint surplus, less $KQ$. With a framework AMC, subsidy $s$ is paid per vaccine from escrow fund $F$. For AMC output $q^A$, the subsidy period lasts $T=(1/r)\log(sq^A/(sq^A-rF))$ when $sq^A>rF$, and forever otherwise. The tail output is $q^T$. The AMC bargain maximizes discounted joint surplus over both feasible outputs, and equilibrium capacity maximizes the firm's resulting value over $Q\geq0$.
--
--   These definitions expose the capacity and bargaining choices used by Propositions 1–3. **Formalization Note** $B$ is $C^2$ on all real numbers, extending the paper's half-line convention. Output is constant within each period, as in (A8). Real infima and suprema are only interpreted economically on their stated nonempty, bounded domains.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), §2–§3.4, pp. 5–13 (PDF 8–16), Assumption 1 and equations (1)–(8); Appendix A, equation (A8)

import Mathlib
import Definitions.Def_VaccineAMC_Framework_DiscountedFlow

open MeasureTheory Filter Topology

namespace VaccineAMC.Framework

structure Params where
  r : ℝ
  α : ℝ
  β : ℝ
  c : ℝ
  K : ℝ
  B : ℝ → ℝ

def Params.κ (θ : Params) : ℝ := θ.r * θ.K

def Params.Standing (θ : Params) : Prop :=
  0 < θ.r ∧ 0 < θ.α ∧ θ.α < 1 ∧ 0 < θ.β ∧ θ.β < 1 ∧ 0 < θ.c ∧ 0 < θ.K ∧
  ContDiff ℝ 2 θ.B ∧ θ.B 0 = 0 ∧
  (∀ q, 0 ≤ q → 0 < deriv θ.B q) ∧
  (∀ q, 0 ≤ q → deriv (deriv θ.B) q < 0) ∧
  Tendsto (deriv θ.B) atTop (𝓝 0)

noncomputable def invDemand (θ : Params) (q : ℝ) : ℝ := θ.α * deriv θ.B q
noncomputable def pbar (θ : Params) : ℝ := invDemand θ 0
noncomputable def demand (θ : Params) (p : ℝ) : ℝ :=
  sInf {q : ℝ | 0 ≤ q ∧ invDemand θ q ≤ p}

def Assumption1 (θ : Params) : Prop := θ.c + θ.κ < pbar θ

def flow (θ : Params) (q : ℝ) : ℝ := θ.α * θ.B q - θ.c * q

noncomputable def welfareIN (θ : Params) (Q q : ℝ) : ℝ :=
  discountedFlow θ.r (flow θ q) (Set.Ioi 0) - θ.K * Q

def IsIntegratedOpt (θ : Params) (Q q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ Q ∧
  ∀ Q' q', 0 ≤ q' → q' ≤ Q' → welfareIN θ Q' q' ≤ welfareIN θ Q q

noncomputable def jointNA (θ : Params) (q : ℝ) : ℝ :=
  discountedFlow θ.r (flow θ q) (Set.Ioi 0)

def IsBargainNA (θ : Params) (Q q : ℝ) : Prop :=
  q ∈ Set.Icc 0 Q ∧ ∀ q' ∈ Set.Icc 0 Q, jointNA θ q' ≤ jointNA θ q

noncomputable def firmValueNA (θ : Params) (Q : ℝ) : ℝ :=
  θ.β * sSup (jointNA θ '' Set.Icc 0 Q) - θ.K * Q

def IsEqNA (θ : Params) (Q q : ℝ) : Prop :=
  0 ≤ Q ∧ IsBargainNA θ Q q ∧
  ∀ Q', 0 ≤ Q' → firmValueNA θ Q' ≤ firmValueNA θ Q

noncomputable def wIN (θ : Params) (Q : ℝ) : ℝ :=
  (θ.α * θ.B Q - (θ.c + θ.κ) * Q) / θ.r

noncomputable def profitNA (θ : Params) (Q : ℝ) : ℝ :=
  θ.β / θ.r * (θ.α * θ.B Q - (θ.c + θ.κ / θ.β) * Q)

noncomputable def amcLength (θ : Params) (s F qA : ℝ) : ℝ :=
  1 / θ.r * Real.log (s * qA / (s * qA - θ.r * F))

noncomputable def amcPeriod (θ : Params) (s F qA : ℝ) : Set ℝ :=
  if θ.r * F < s * qA then Set.Ioo 0 (amcLength θ s F qA) else Set.Ioi 0

noncomputable def jointTS (θ : Params) (s F qA qT : ℝ) : ℝ :=
  discountedFlow θ.r (flow θ qA + s * qA) (amcPeriod θ s F qA) +
  discountedFlow θ.r (flow θ qT) (Set.Ioi 0 \ amcPeriod θ s F qA)

def IsBargainTS (θ : Params) (s F Q qA qT : ℝ) : Prop :=
  qA ∈ Set.Icc 0 Q ∧ qT ∈ Set.Icc 0 Q ∧
  ∀ a ∈ Set.Icc 0 Q, ∀ b ∈ Set.Icc 0 Q,
    jointTS θ s F a b ≤ jointTS θ s F qA qT

noncomputable def firmValueTS (θ : Params) (s F Q : ℝ) : ℝ :=
  θ.β * sSup ((fun x : ℝ × ℝ => jointTS θ s F x.1 x.2) ''
    (Set.Icc 0 Q ×ˢ Set.Icc 0 Q)) - θ.K * Q

def IsEqTS (θ : Params) (s F Q qA qT : ℝ) : Prop :=
  0 ≤ Q ∧ IsBargainTS θ s F Q qA qT ∧
  ∀ Q', 0 ≤ Q' → firmValueTS θ s F Q' ≤ firmValueTS θ s F Q

end VaccineAMC.Framework


