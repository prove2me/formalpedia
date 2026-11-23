-- Prove2me | Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerDemand
-- name    : PerishablePricing_Backlog_Supplement_IntegerDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:59:36.121547+00:00
-- url     : https://prove2.me/theorems/10562033-9197-416f-b681-f0771fd5c9ed
-- title:
--   §§2–3,5 — integer demand decisions, additive noise, and derivative conditions
-- statement:
--   The discrete carrier is $\mathbb F=\mathbb Z$. Expected demand ranges over the nonempty integer interval $\{d\in\mathbb Z:\underline d\le d\le\bar d\}$ with integer endpoints. The price remains real. The bounded, mean-zero noise law $\mu$ is represented on $\mathbb R$ and is concentrated on the integers, so the additive realized demand is integer at each admissible decision, almost surely. It is not obtained by rounding a continuous demand law.
--
--   The actual CDF $F$, survival function, revenue, and ordinary ambient price/CDF derivatives are inherited from the shared demand data. Conditions (C1) and (C2) are tested at integer demand and inventory decisions:
--
--   $$P''(d)d+P'(d)\le0,\qquad -\frac{P(d)}{P'(d)}\frac{F'(y-d)}{1-F(y-d)}\ge1.$$
--
--   The second condition is tested for all integer $y\ge0$ with positive survival, including below the support; derivative existence and $P'(d)\ne0$ are explicit. A CDF jump with positive survival fails this condition. No finite-difference or density-of-an-interpolation substitute is used. Integer revenue uses the same actual truncated-sales expectation, on the full integer demand/inventory domain.
--
--   **Formalization Note** This resolves the paper's implicit discrete conventions using its p. 285 continuous/discrete demand claim, p. 287 carrier convention, and (1). For integer expected demand, integer realized demand is equivalent to integer additive noise. Fractional-mean demand choices and mixed real/integer action models are outside this single-carrier instance; no claim about them is substituted for it. The separate real case retains all real choices and noise laws.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, §2, p. 287; eq. (1), p. 288; (C1)–(C2), p. 293

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Supplement_Demand
import Definitions.Def_PerishablePricing_Backlog_Supplement_IntegerLNat

namespace PerishablePricing.Backlog.Supplement

/-- Integer decision/demand instance of (1). The measure is kept on R to share the
actual CDF and derivative formulas; it is concentrated on Z. This is a carrier
choice, not a rounding approximation of continuous demand. -/
structure IntegerDemandData extends DemandData where
  lower : ℤ
  upper : ℤ
  lower_eq : dlo = (lower : ℝ)
  upper_eq : dhi = (upper : ℝ)
  noise_integer : μ {x : ℝ | ∃ z : ℤ, x = (z : ℝ)}ᶜ = 0

namespace IntegerDemandData

variable (Q : IntegerDemandData)

def demandSet : Set ℤ := Set.Icc Q.lower Q.upper

/-- Ordinary ambient derivatives, tested at the integer decision points. -/
def C1 : Prop :=
  ∀ d ∈ Q.demandSet, DifferentiableAt ℝ Q.P (d : ℝ) ∧
    DifferentiableAt ℝ (deriv Q.P) (d : ℝ) ∧
      deriv (deriv Q.P) (d : ℝ) * (d : ℝ) + deriv Q.P (d : ℝ) ≤ 0

/-- The integer carrier does not replace derivatives by finite differences.
A positive-survival jump of the actual CDF fails this condition. -/
def C2 : Prop :=
  ∀ d ∈ Q.demandSet, ∀ y : ℤ, 0 ≤ y → 0 < Q.toDemandData.tail ((y : ℝ) - d) →
    DifferentiableAt ℝ Q.toDemandData.cdf ((y : ℝ) - d) ∧
      deriv Q.P (d : ℝ) ≠ 0 ∧ 1 ≤ Q.toDemandData.rho d y

noncomputable def revenue (d y : ℤ) : ℝ := Q.toDemandData.revenue d y

def revenueDomain : Set (Fin 2 → ℤ) :=
  {w | w 0 ∈ Q.demandSet ∧ 0 ≤ w 1}

noncomputable def revenueJoint (w : Fin 2 → ℤ) : ℝ := Q.revenue (w 0) (w 1)

end IntegerDemandData

end PerishablePricing.Backlog.Supplement


