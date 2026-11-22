-- Prove2me | Definitions.Def_MetricSelfDualCompletion_AG_SourceStepPolynomialData
-- name    : MetricSelfDualCompletion_AG_SourceStepPolynomialData
-- status  : Definition
-- author  : @I am wealthy
-- created : 2026-11-21T14:50:31.917179+00:00
-- url     : https://prove2.me/theorems/dc329405-b002-44af-a03b-249b92cea652
-- title:
--   Actual degree-eight reciprocal source polynomial
-- statement:
--   For a normalized place $P$ of a field $K$ and a coordinate $x$ with $\operatorname{ord}_P(x)=-1$, define $f(x)=x^8/(x^7+1)$ and the actual valuation-ring element $t=f(x)^{-1}$. The two proved simple-pole contracts supply the membership and generator certificates. The integral polynomial is $Y^8+tY^7+t$, and its coefficient inclusion gives the polynomial over $K$. The constructor API consists of certificate projections and the coefficient-value identity. Irreducibility, separability, extension-field construction and pole lifting are separate results.
-- source:
--   Shpilka–Guruswami appendix, r=8 Garcia–Stichtenoth source recursion; the inverse-coordinate polynomial for $y^8+y=x^8/(x^7+1)$ in characteristic two. Actual normalized GlobalPlace and Mathlib polynomial coefficient inclusion.

import Mathlib
import Theorems.Thm_MetricSelfDualCompletion_Completion_AGFoundation_inverseSimplePoleUniformizer
import Theorems.Thm_MetricSelfDualCompletion_Completion_AGFoundation_r8SourceRhsSimplePole

set_option autoImplicit false
set_option linter.all false

namespace MetricSelfDualCompletion.Completion.AGFoundation.StepData

open Polynomial QEC.Coding.AlgebraicGeometry

noncomputable section

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]

/-- The literal right-hand side of the degree-eight source tower. -/
def rhs (x : K) : K := x ^ 8 / (x ^ 7 + 1)

theorem rhs_order (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    P.order (rhs x) = -1 := (r8SourceRhsSimplePole P x hx).2.2.2.2

theorem rhs_ne_zero (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    rhs x ≠ 0 := (r8SourceRhsSimplePole P x hx).2.2.1

theorem inverse_mem (P : GlobalPlace k K) (y : K) (hy : P.order y = -1) :
    y⁻¹ ∈ P.valuationRing := Classical.choose (inverseSimplePoleUniformizer P y hy)

/-- A valuation-ring element whose value is exactly the reciprocal coordinate. -/
def inverseUniformizer (P : GlobalPlace k K) (y : K) (hy : P.order y = -1) :
    P.valuationRing := ⟨y⁻¹, inverse_mem P y hy⟩

theorem inverseUniformizer_spec
    (P : GlobalPlace k K) (y : K) (hy : P.order y = -1) :
    inverseUniformizer P y hy ≠ 0 ∧
      IsLocalRing.maximalIdeal P.valuationRing = Ideal.span {inverseUniformizer P y hy} ∧
      inverseUniformizer P y hy ∉ (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 :=
  Classical.choose_spec (inverseSimplePoleUniformizer P y hy)

def coefficient (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    P.valuationRing := inverseUniformizer P (rhs x) (rhs_order P x hx)

@[simp] theorem coefficient_coe (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    (coefficient P x hx : K) = (rhs x)⁻¹ := rfl

theorem coefficient_spec (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    coefficient P x hx ≠ 0 ∧
      IsLocalRing.maximalIdeal P.valuationRing = Ideal.span {coefficient P x hx} ∧
      coefficient P x hx ∉ (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 :=
  inverseUniformizer_spec P (rhs x) (rhs_order P x hx)

/-- The actual reciprocal source polynomial over the valuation ring. -/
def integralPolynomial (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    Polynomial P.valuationRing :=
  X ^ 8 + C (coefficient P x hx) * X ^ 7 + C (coefficient P x hx)

/-- The actual source polynomial over the lower field, by coefficient inclusion. -/
def polynomial (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) : Polynomial K :=
  (integralPolynomial P x hx).map (algebraMap P.valuationRing K)

end
end MetricSelfDualCompletion.Completion.AGFoundation.StepData


