-- Prove2me | Definitions.Def_WangMinimaxRegret_Reformulation_Revenue
-- name    : WangMinimaxRegret_Reformulation_Revenue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:43.984003+00:00
-- url     : https://prove2.me/theorems/19b505f0-2fef-43c8-871b-e5d3602d7085
-- title:
--   Original revenues, competitive ratio, and hypograph program
-- statement:
--   For valuation data $d$, a Stieltjes payment $m$, and a law $F$, define the inclusive tail $T_F(p)=F([p,\infty))$, revenue $R(m,F)=\int m\,dF$ using the nonnegative extended integral, posted-price revenue $B_F(p)=pT_F(p)$, and benchmark $B(F)=\sup_{p\in I}B_F(p)$. On feasible laws and payments all integrands are nonnegative. Define the operational competitive ratio by
--   $$C(m)=\sup\{r\ge0:\ \forall F\in\mathcal F,\ \forall p\in I,\ rB_F(p)\le R(m,F)\}.$$
--   This definition refers only to original revenues. The auxiliary ordinary quotient expression is $Q(m)=\inf_{F\in\mathcal F}R(m,F)/B(F)$, used for finite positive benchmarks. The original value is $V_P=\sup_{m\in\mathcal M}C(m)$, and an optimal original payment belongs to $\mathcal M$ and achieves $V_P$.
--
--   For any set $A$ of laws, the fractional value at $p$ is $J_A(m,p)=\inf_{F\in A,\ T_F(p)>0}R(m,F)/T_F(p)$. Zero-tail laws impose no constraint; an empty infimum is $+\infty$. Equation (1) is defined independently by $m\in\mathcal M$, $r\in\mathbb R$, and $rp\le J_{\mathcal F}(m,p)$ for every $p\in I$; its value is the supremum of feasible $r$. Nonnegative quantities use extended nonnegative reals, while signed program values and comparisons use extended reals. Negative trial $r$ in (1) is retained.
-- source:
--   Wang, Liu and Zhang (2024), Minimax Regret Robust Screening with Moment Information, https://doi.org/10.1287/msom.2023.0072, Section 2, pp. 7–8, (P), competitive ratio, and equation (1)

import Definitions.Def_WangMinimaxRegret_Reformulation_Model

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false
noncomputable section

namespace WangMinimaxRegret.Reformulation

def tail (F : Measure ℝ) (p : ℝ) : ℝ≥0∞ := F (Ici p)

def revenue (m : StieltjesFunction ℝ) (F : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (m x) ∂F

def priceRevenue (F : Measure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal p * tail F p

def benchmark (d : Data) (F : Measure ℝ) : ℝ≥0∞ :=
  ⨆ p ∈ interval d, priceRevenue F p

/-- Operational ratio, defined entirely from actual revenues, even for infinite benchmarks. -/
def competitiveRatio (d : Data) (m : StieltjesFunction ℝ) : ℝ≥0∞ :=
  ⨆ r : ℝ≥0, ⨆ (_ : ∀ F : Measure ℝ, Ambiguous d F →
    ∀ p ∈ interval d, (r : ℝ≥0∞) * priceRevenue F p ≤ revenue m F), (r : ℝ≥0∞)

/-- Used only under finite, strictly positive benchmark hypotheses. -/
def quotientRatio (d : Data) (m : StieltjesFunction ℝ) : ℝ≥0∞ :=
  ⨅ F : Measure ℝ, ⨅ (_ : Ambiguous d F), revenue m F / benchmark d F

def originalValue (d : Data) : EReal :=
  ⨆ m : StieltjesFunction ℝ, ⨆ (_ : IsPayment d m), (competitiveRatio d m : EReal)

def OriginalOptimal (d : Data) (m : StieltjesFunction ℝ) : Prop :=
  IsPayment d m ∧ (competitiveRatio d m : EReal) = originalValue d

/-- Zero-tail laws impose no constraint: the empty infimum is positive infinity. -/
def fractionalValue (laws : Set (Measure ℝ)) (m : StieltjesFunction ℝ) (p : ℝ) : ℝ≥0∞ :=
  ⨅ F ∈ laws, ⨅ (_ : 0 < tail F p), revenue m F / tail F p

def HypographFeasible (d : Data) (m : StieltjesFunction ℝ) (r : ℝ) : Prop :=
  IsPayment d m ∧ ∀ p ∈ interval d,
    ((r * p : ℝ) : EReal) ≤ (fractionalValue {F | Ambiguous d F} m p : EReal)

def hypographValue (d : Data) : EReal :=
  ⨆ m : StieltjesFunction ℝ, ⨆ r : ℝ, ⨆ (_ : HypographFeasible d m r), (r : EReal)

end WangMinimaxRegret.Reformulation


