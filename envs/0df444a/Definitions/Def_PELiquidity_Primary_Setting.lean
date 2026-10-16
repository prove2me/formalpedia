-- Prove2me | Definitions.Def_PELiquidity_Primary_Setting
-- name    : PELiquidity_Primary_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:19.810433+00:00
-- url     : https://prove2.me/theorems/6c211ffd-16ac-479e-81c4-67269e3b1f88
-- title:
--   §3–§4, Definition 1, (2)–(5), (7), (11), (16) — parameters with Assumptions 1–3, 5–6, IC fee schedules, feasible and optimal partnership contracts, capital supply
-- statement:
--   The model of Maurin, Robinson and Strömberg: general partners (GPs) raise funds from limited partners (LPs) who may be hit by a liquidity shock.
--
--   **Parameters.** An investment pays $R$ per unit on success and $0$ on failure. It succeeds with probability $p$ if the GP exerts effort and with probability $q$ if the GP shirks, in which case the GP enjoys a private benefit $B$ per unit invested. Each GP has wealth $A$, the LPs hold a total mass $K$ of cash, a liquidity shock hits with probability $\lambda\in(0,1)$, and the two LP types discount period-2 consumption after the shock by $\delta_L$ and $\delta_H$, both in $(0,1)$. The structure `Params` records these numbers together with $0<q<p\le 1$, $B,A,K>0$ and
--
--   1. Assumption 1: $pR\ge 1\ge qR+B$;
--   2. Assumption 2: $p\big(R-\tfrac{pB}{p^2-q^2}\big)<1$;
--   3. Assumption 3: $K\ge \dfrac{A}{1-p\big(R-\frac{pB}{p^2-q^2}\big)}-A$;
--   4. Assumption 5 for $\delta_L$, strict: $1+r(\lambda,\delta_L)<pR$;
--   5. Assumption 6: $\delta_L<\hat\delta(\lambda)<\delta_H$;
--   6. limited liability is satisfiable: $B\le p(p-q)R$.
--
--   **Rates and thresholds.**
--   $$1+r(\lambda,\delta)=\frac{1}{1-\lambda(1-\delta)},\qquad \hat x(\lambda,\delta)=1-\frac{\delta}{1-\lambda(1-\delta)},\qquad \hat\delta(\lambda)=1-\frac{p}{p+(1-\lambda)q},$$
--   and $\underline x=q/(p+q)$, $\bar x=p/(p+q)$.
--
--   **Fee schedules.** An outcome $\omega=(\omega_1,\omega_2)$ records the success of the period-0 investment (share $x$ of the fund) and of the period-1 investment (share $1-x$); the unit cash flow is $R x\,\mathbb 1[\omega_1]+R(1-x)\,\mathbb 1[\omega_2]$. A fee schedule $f$ assigns a fee per unit of investment to each outcome; outcomes with the same cash flow receive the same fee. When the two investments succeed independently with probabilities $a$ and $b$, the expected fee is $\sum_\omega \Pr_{a,b}(\omega) f(\omega)$; $\bar f$ denotes the expected fee under effort on both investments, $a=b=p$. The schedule satisfies **limited liability** (2) if $0\le f(\omega)\le$ cash flow at every outcome, and it is **incentive compatible** ($f\in\mathcal F^{IC}_x$) if effort on both investments is at least as good for the GP as shirking on both (benefit $B$), on the first only (benefit $Bx$), or on the second only (benefit $B(1-x)$).
--
--   **Contracts.** Given a promised return $\bar R$ and a claim value $c$ (the left side of the no-default constraint (4)), a contract $(x,I,f)$ is **feasible** if $x\in[0,1]$, $f$ satisfies limited liability and incentive compatibility, $I>A$,
--   $$(pR-\bar f)\,I=\bar R\,(I-A)\qquad(3)$$
--   and $1-x\le c$ (4). It is **optimal** (5) if it is feasible and its GP profit $\Pi_{GP}=\bar f I$ is at least that of every feasible contract.
--
--   **Capital supply** (7). Given values $v_{PE}$ and $v_{cash}$ of a unit invested in private equity and in cash and a capacity $\mu K$, a supply $S$ is admissible if $S=0$ when $v_{PE}<v_{cash}$, $S\in[0,\mu K]$ when $v_{PE}=v_{cash}$, and $S=\mu K$ when $v_{PE}>v_{cash}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Fees are indexed by the four success outcomes, with equal fees required whenever outcomes produce the same cash flow. This also covers $x=0$, $x=1/2$, and $x=1$. Equation (3) is stated multiplied out, so that the fund size is never a quotient. Assumption 5 is taken strictly and $B\le p(p-q)R$ is added; both are needed for the paper's results and are discussed in the mission description. Assumption 4 is not imposed: the no-default constraint (4) is part of every feasible contract.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), pp. 7–21, §3, Definition 1, (2)–(5), (7), (11), (14), (16), Assumptions 1–3, 5, 6

import Mathlib

namespace PELiquidity.Primary

noncomputable def grossReturn (lam δ : ℝ) : ℝ := 1 / (1 - lam * (1 - δ))
noncomputable def xHat (lam δ : ℝ) : ℝ := 1 - δ / (1 - lam * (1 - δ))
noncomputable def deltaHat (p q lam : ℝ) : ℝ := 1 - p / (p + (1 - lam) * q)
noncomputable def xLow (p q : ℝ) : ℝ := q / (p + q)
noncomputable def xBar (p q : ℝ) : ℝ := p / (p + q)

structure Params where
  p : ℝ
  q : ℝ
  R : ℝ
  B : ℝ
  A : ℝ
  K : ℝ
  lam : ℝ
  δL : ℝ
  δH : ℝ
  hq : 0 < q
  hqp : q < p
  hp1 : p ≤ 1
  hB : 0 < B
  hA : 0 < A
  hK : 0 < K
  hlam0 : 0 < lam
  hlam1 : lam < 1
  hδL0 : 0 < δL
  hδL1 : δL < 1
  hδH0 : 0 < δH
  hδH1 : δH < 1
  hA1a : 1 ≤ p * R
  hA1b : q * R + B ≤ 1
  hA2 : p * (R - p * B / (p ^ 2 - q ^ 2)) < 1
  hA3 : A / (1 - p * (R - p * B / (p ^ 2 - q ^ 2))) - A ≤ K
  hA5 : grossReturn lam δL < p * R
  hA6a : δL < deltaHat p q lam
  hA6b : deltaHat p q lam < δH
  hLL : B ≤ p * (p - q) * R

abbrev Outcome := Bool × Bool

def cashFlow (R x : ℝ) (ω : Outcome) : ℝ :=
  (if ω.1 then R * x else 0) + (if ω.2 then R * (1 - x) else 0)

def outcomeProb (a b : ℝ) (ω : Outcome) : ℝ :=
  (if ω.1 then a else 1 - a) * (if ω.2 then b else 1 - b)

def expectedFee (a b : ℝ) (f : Outcome → ℝ) : ℝ :=
  ∑ ω : Outcome, outcomeProb a b ω * f ω

def IsLimitedLiability (R x : ℝ) (f : Outcome → ℝ) : Prop :=
  (∀ ω, 0 ≤ f ω ∧ f ω ≤ cashFlow R x ω) ∧
  ∀ ω ω', cashFlow R x ω = cashFlow R x ω' → f ω = f ω'

def IsIC (p q B x : ℝ) (f : Outcome → ℝ) : Prop :=
  expectedFee q q f + B ≤ expectedFee p p f ∧
  expectedFee q p f + B * x ≤ expectedFee p p f ∧
  expectedFee p q f + B * (1 - x) ≤ expectedFee p p f

def IsFeasibleContract (P : Params) (Rbar claimVal x I : ℝ) (f : Outcome → ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ IsLimitedLiability P.R x f ∧
  IsIC P.p P.q P.B x f ∧ P.A < I ∧
  (P.p * P.R - expectedFee P.p P.p f) * I = Rbar * (I - P.A) ∧
  1 - x ≤ claimVal

def IsOptimalContract (P : Params) (Rbar claimVal x I : ℝ) (f : Outcome → ℝ) : Prop :=
  IsFeasibleContract P Rbar claimVal x I f ∧
  ∀ x' I' (f' : Outcome → ℝ),
    IsFeasibleContract P Rbar claimVal x' I' f' →
    expectedFee P.p P.p f' * I' ≤ expectedFee P.p P.p f * I

def gpProfit (P : Params) (I : ℝ) (f : Outcome → ℝ) : ℝ :=
  expectedFee P.p P.p f * I

def IsCapitalSupply (vPE vcash cap S : ℝ) : Prop :=
  (vPE < vcash → S = 0) ∧
  (vPE = vcash → 0 ≤ S ∧ S ≤ cap) ∧
  (vcash < vPE → S = cap)

end PELiquidity.Primary


