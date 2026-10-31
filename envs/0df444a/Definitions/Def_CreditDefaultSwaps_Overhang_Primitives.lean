-- Prove2me | Definitions.Def_CreditDefaultSwaps_Overhang_Primitives
-- name    : CreditDefaultSwaps_Overhang_Primitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:02:20.568606+00:00
-- url     : https://prove2.me/theorems/0b295a68-187b-4ad3-ba75-97caf9018d53
-- title:
--   Post-initiation primitives, liquidation, and cash-settled protection
-- statement:
--   The fixed primitive data are the risk-free rate $r$, baseline growth $\mu$, volatility $\sigma$, production capacity $\Pi$, productivity improvement $i$, cost coefficient $\varphi$, corporate tax $\tau$, proportional bankruptcy loss $\alpha$, shareholder bargaining weight $\eta$, and perpetual coupon $C$. Standing assumptions are
--   $$r,\sigma,\Pi,i>0,\quad \varphi,C\ge0,\quad r>\mu+i,\quad \tau,\alpha\in[0,1],\quad 0\le\eta<1,$$
--   and positive investment NPV, $U_i>U_0$, where
--   $$U_0=\frac{(1-\tau)\Pi}{r-\mu},\qquad U_i=\frac{(1-\tau)\Pi-\varphi i}{r-\mu-i},\qquad L=(1-\alpha)U_0.$$
--   At bankruptcy from productivity $x$, the CDS pays $\theta\max(C/r-Lx,0)$; the creditor reservation payoff is this amount plus $Lx$. The source's two strategic-service formulas (7)–(8) are also recorded as a helper, selected by whether investment is zero. They are not imposed as hypotheses on arbitrary deviations or used to replace the optimization problem.
--
--   Differences from the source:
--   - encoding: economic rates, capacity, costs and coupon → the displayed sign conventions, retaining zero cost and zero coupon; reason: no unprinted strictly positive coupon or cost restriction is imposed.
--   - encoding: the source writes an intermediate $\widetilde\varphi=\varphi/(1-\tau)$ → the algebraically expanded numerator of $U_i$; reason: no artificial division by zero at $\tau=1$.
--   - encoding: the simplified reservation formula in §3.1.2 → the positive-part cash-settlement payoff from §2; reason: the actual CDS contract controls states outside the default branch as well.
-- source:
--   Wong and Yu, Credit Default Swaps and Debt Overhang, Management Science (2021), DOI 10.1287/mnsc.2020.3953, supplied source.pdf, §2, equations (1)–(2), printed pp. 6–8 (PDF pp. 7–9); §3.1.2, equations (7)–(8), printed p. 11 (PDF p. 12)

import Mathlib

noncomputable section

namespace CreditDefaultSwaps.Overhang

structure Primitives where
  r : ℝ
  mu : ℝ
  sigma : ℝ
  capacity : ℝ
  improvement : ℝ
  cost : ℝ
  tax : ℝ
  loss : ℝ
  weight : ℝ
  coupon : ℝ

def U0 (p : Primitives) : ℝ := (1 - p.tax) * p.capacity / (p.r - p.mu)

def Ui (p : Primitives) : ℝ :=
  ((1 - p.tax) * p.capacity - p.cost * p.improvement) /
    (p.r - p.mu - p.improvement)

def liquidationCoefficient (p : Primitives) : ℝ := (1 - p.loss) * U0 p

def Standing (p : Primitives) : Prop :=
  0 < p.r ∧ 0 < p.sigma ∧ 0 < p.capacity ∧ 0 < p.improvement ∧
  0 ≤ p.cost ∧ 0 ≤ p.coupon ∧ p.mu + p.improvement < p.r ∧
  p.tax ∈ Set.Icc 0 1 ∧ p.loss ∈ Set.Icc 0 1 ∧
  p.weight ∈ Set.Ico 0 1 ∧ U0 p < Ui p

def defaultProtection (p : Primitives) (theta x : ℝ) : ℝ :=
  theta * max (p.coupon / p.r - liquidationCoefficient p * x) 0

def reservation (p : Primitives) (theta x : ℝ) : ℝ :=
  liquidationCoefficient p * x + defaultProtection p theta x

/-- Equations (7) and (8), recorded without imposing them on arbitrary deviations. -/
def strategicService (p : Primitives) (theta x a : ℝ) : ℝ :=
  if a = 0 then
    p.weight * theta * p.coupon +
      (1 - p.weight + p.weight * (1 - theta) * (1 - p.loss)) *
        (p.r - p.mu) * U0 p * x
  else
    p.weight * theta * p.coupon +
      ((1 - p.weight) * Ui p + p.weight * (1 - theta) * liquidationCoefficient p) *
        (p.r - p.mu - p.improvement) * x

end CreditDefaultSwaps.Overhang


