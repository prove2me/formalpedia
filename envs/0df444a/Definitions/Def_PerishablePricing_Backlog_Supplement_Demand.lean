-- Prove2me | Definitions.Def_PerishablePricing_Backlog_Supplement_Demand
-- name    : PerishablePricing_Backlog_Supplement_Demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:58:42.623999+00:00
-- url     : https://prove2.me/theorems/0a215027-22bd-46ce-a6bf-26dfb7eed89e
-- title:
--   Conditions (C1)–(C2), p. 293 — demand law, truncated revenue and hazard-domain elasticity
-- statement:
--   The demand data consist of an interval $\mathcal D=[\underline d,\bar d]$, a strictly decreasing inverse demand $P$ on it, and a probability law $\mu$ for stationary independent additive noise. The noise has mean zero, is supported in $[A,B]$ with $A\le0\le B$, and $\underline d+A\ge0$. Write $F(x)=\mu(({-\infty},x])$, $\bar F=1-F$, and
--
--   $$R(d,y)=P(d)\int\min(d+\varepsilon,y)\,d\mu(\varepsilon),\qquad \varrho(d,y)=-\frac{P(d)}{P'(d)}\frac{F'(y-d)}{\bar F(y-d)}.$$
--
--   Condition (C1) is $P''(d)d+P'(d)\le0$ on $\mathcal D$, with both derivatives existing. Condition (C2) is $\varrho(d,y)\ge1$ for $d\in\mathcal D$, $y\ge0$ wherever $\bar F(y-d)>0$; there the derivative $F'(y-d)$ exists and $P'(d)\ne0$. Revenue is studied on $\mathcal D\times\mathbb R_+$. These data are independent of lifetime, costs and dynamics, and contain no revenue-concavity hypothesis.
--
--   **Formalization Note** Hazard rates are only defined at positive survival probability. This reading omits the undefined quotient above the upper support; it does not omit points below the lower support. Ordinary differentiability at the points used is explicit rather than letting Lean's default `deriv` replace a nonexistent derivative. Bounded noise guarantees integrability of the revenue integrand and of the identity defining the mean. The crucial consequence that (C2) forces $\underline d=\bar d$ is retained in the theorem statements and documented in DISPROOF.md. A deterministic zero-demand boundary can satisfy this hazard-domain reading, so no claim of incompatibility for every degenerate model is made.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, https://doi.org/10.1287/opre.2014.1261, (C1)–(C2) and LSR elasticity, p. 293 (PDF 11); §3 and R, p. 288 (PDF 6)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

namespace PerishablePricing.Backlog.Supplement

open MeasureTheory

/-- Price/noise data, unbundled from the inventory dynamics and unit costs.
No revenue concavity or lost-sales elasticity assumption is built into these data. -/
structure DemandData where
  dlo : ℝ
  dhi : ℝ
  dlo_le_dhi : dlo ≤ dhi
  P : ℝ → ℝ
  P_strictAnti : StrictAntiOn P (Set.Icc dlo dhi)
  μ : Measure ℝ
  isProb : IsProbabilityMeasure μ
  A : ℝ
  B : ℝ
  A_nonpos : A ≤ 0
  B_nonneg : 0 ≤ B
  support : μ (Set.Icc A B)ᶜ = 0
  mean_zero : ∫ x, x ∂μ = 0
  demand_nonneg : 0 ≤ dlo + A

namespace DemandData

variable (Q : DemandData)

def demandSet : Set ℝ := Set.Icc Q.dlo Q.dhi

/-- The actual distribution function of μ, not an independently chosen function. -/
noncomputable def cdf (x : ℝ) : ℝ := (Q.μ (Set.Iic x)).toReal

noncomputable def tail (x : ℝ) : ℝ := 1 - Q.cdf x

/-- The §3 lost-sales revenue on its full domain; bounded noise makes the integral honest. -/
noncomputable def revenue (d y : ℝ) : ℝ :=
  Q.P d * ∫ ε, min (d + ε) y ∂Q.μ

def revenueDomain : Set (Fin 2 → ℝ) :=
  {w | w 0 ∈ Q.demandSet ∧ 0 ≤ w 1}

noncomputable def revenueJoint (w : Fin 2 → ℝ) : ℝ := Q.revenue (w 0) (w 1)

/-- The displayed quotient is used only where both denominators are nonzero. -/
noncomputable def rho (d y : ℝ) : ℝ :=
  -(Q.P d / deriv Q.P d) * (deriv Q.cdf (y - d) / Q.tail (y - d))

/-- (C1), with existence of its two ordinary derivatives made explicit. -/
def C1 : Prop :=
  ∀ d ∈ Q.demandSet, DifferentiableAt ℝ Q.P d ∧
    DifferentiableAt ℝ (deriv Q.P) d ∧ deriv (deriv Q.P) d * d + deriv Q.P d ≤ 0

/-- (C2), on the domain of the hazard rate. No support-only restriction is made:
points below A still have tail 1 and are tested. Points with tail zero are omitted.
The derivative and nonzero price derivative are the presuppositions of the quotient. -/
def C2 : Prop :=
  ∀ d ∈ Q.demandSet, ∀ y : ℝ, 0 ≤ y → 0 < Q.tail (y - d) →
    DifferentiableAt ℝ Q.cdf (y - d) ∧ deriv Q.P d ≠ 0 ∧ 1 ≤ Q.rho d y

end DemandData

end PerishablePricing.Backlog.Supplement


