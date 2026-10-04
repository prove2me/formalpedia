-- Prove2me | Definitions.Def_StochApproxDyn_Interpolation_VectorFieldFlow
-- name    : StochApproxDyn_Interpolation_VectorFieldFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:52:49.877797+00:00
-- url     : https://prove2.me/theorems/3d118096-6f01-49a3-af62-a98980a0c47f
-- title:
--   Integral curves, globally integrable vector fields and the flow induced by F
-- statement:
--   Let $E$ be a real normed space (in the mission, $E=\mathbb R^d$) and $F:E\to E$ a vector field.
--
--   1. An **integral curve** of $F$ is a map $y:\mathbb R\to E$, differentiable at every $t\in\mathbb R$, with
--   $$\frac{dy}{dt}(t)=F(y(t))\qquad(t\in\mathbb R).$$
--   2. $F$ is **globally integrable** if it has unique integral curves: through every $p\in E$ there is an integral curve $y$ with $y(0)=p$, defined for all times, and two integral curves taking the same value at time $0$ are equal.
--   3. A map $\Phi:\mathbb R\times E\to E$, $(t,p)\mapsto\Phi_t(p)$, is the **flow induced by $F$** if for every $p$ the curve $t\mapsto\Phi_t(p)$ is an integral curve of $F$ with $\Phi_0(p)=p$.
--
--   When $F$ is globally integrable, the flow induced by $F$ exists and is unique; it is the flow $\Phi$ with respect to which the interpolated process is compared in Proposition 4.1. A bounded locally Lipschitz vector field is globally integrable.
--
--   **Formalization Note** Uniqueness is stated for curves defined on all of $\mathbb R$; under the existence of global integral curves through every point this is equivalent to uniqueness on every interval. The flow is carried as an unbundled function `ℝ → E → E` satisfying the defining property, not as a Mathlib `Flow`: continuity of $(t,p)\mapsto\Phi_t(p)$ is a consequence (continuous dependence on initial data under uniqueness), not an assumption.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 12, §4.1 ("The vector field F is said to be globally integrable if it has unique integral curves"); p. 13, Proposition 4.1 ("the flow φ induced by F")

import Mathlib

namespace StochApproxDyn.Interpolation

/-- `y : ℝ → E` is an *integral curve* of the vector field `F` (a global solution of
`dy/dt = F(y)`): `y` is differentiable at every `t ∈ ℝ` with `y'(t) = F(y(t))`. -/
def IsIntegralCurveOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E)
    (y : ℝ → E) : Prop :=
  ∀ t : ℝ, HasDerivAt y (F (y t)) t

/-- `F` is *globally integrable* (Benaïm 1999, §4.1, p. 12): it has unique integral curves.
Through every point `p` there is an integral curve `y` defined on all of `ℝ` with `y(0) = p`, and
two integral curves with the same value at time `0` coincide. -/
def IsGloballyIntegrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E) :
    Prop :=
  (∀ p : E, ∃ y : ℝ → E, y 0 = p ∧ IsIntegralCurveOf F y) ∧
    ∀ y z : ℝ → E, IsIntegralCurveOf F y → IsIntegralCurveOf F z → y 0 = z 0 → y = z

/-- `Φ : ℝ → E → E` is the *flow induced by* `F`: for every `p`, `t ↦ Φ_t(p)` is the integral
curve of `F` through `p` at time `0`. If `F` is globally integrable, this determines `Φ`. -/
def IsFlowOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E)
    (Φ : ℝ → E → E) : Prop :=
  ∀ p : E, Φ 0 p = p ∧ IsIntegralCurveOf F (fun t => Φ t p)

end StochApproxDyn.Interpolation


