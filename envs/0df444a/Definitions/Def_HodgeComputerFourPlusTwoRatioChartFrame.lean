-- Prove2me | Definitions.Def_HodgeComputerFourPlusTwoRatioChartFrame
-- name    : HodgeComputerFourPlusTwoRatioChartFrame
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-25T14:12:02.348974+00:00
-- url     : https://prove2.me/theorems/76dacab1-16ec-4d9a-a3eb-3f52a679744c
-- title:
--   Core ratio coordinates and $\delta$-frame compatibility for ratio-chart transport
-- statement:
--   This module packages the coordinate and frame data used to reduce the universal fraction-field leaf `exists_core_rational_vector_field` to a ratio-chart $t^4$ current on the dehomogenized core.
--
--   **`CoreRatioCoordinates`.** On a field $K$ under $R=\mathbb{C}[x_0,x_1,y_0,y_1]$, a quadruple $(a,s,t,P)$ is a core ratio-coordinate package when $a\neq 0$, $t\neq 0$, and the homogenization identities
--   $$
--   a^6\cdot P=\iota(H),\qquad a^6\cdot t^3=\iota(x_0^3 y_0^3)
--   $$
--   hold, where $H$ is the four-variable four-plus-two core and $\iota\colon R\to K$ is the structure map.
--
--   **`StandardCoreRatioCoordinates`.** The concrete choice $a=\iota(x_0)$, $t=\iota(y_0)/a$, $s=\iota(y_1)/\iota(y_0)$, together with $P=\iota(H)/a^6$, realizing the package above.
--
--   **`RatioChartDeltaFrame`.** Compatibility of chart directional operators $(D_r,D_s,D_t)$ with coordinate derivations $\delta_i$ extending $\partial_i$: after the standard change of variables one has
--   $$
--   \delta_1=\frac{D_r}{a},\qquad
--   \delta_2=\frac{D_t-(s/t)D_s}{a},\qquad
--   \delta_3=\frac{D_s}{a\cdot t}
--   $$
--   as operators on $K$. This is the precise frame identification needed to transport a chart $t^4$ current into `CoreRationalEquation` via `ratioChart_transport`.
-- source:
--   HodgeComputer four-plus-two residual; WORMHOLE Epoch-4 attack on exists_core_rational_vector_field; Discussion contact chart / ratioChart_transport

import Definitions.Def_HodgeComputerFourPlusTwoWormholeBridge
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.FourPlusTwoResidual

/-- Compatibility of ratio-chart directional operators `(D_r,D_s,D_t)` with the
coordinate derivations `δ` on a fraction field of `ℂ[x₀,x₁,y₀,y₁]`: after the
standard change of variables
`a=x₀`, `t=y₀/x₀`, `s=y₁/y₀`, `r=x₁/x₀`, one has
`δ₁ = D_r/a`, `δ₂ = (D_t - (s/t)D_s)/a`, `δ₃ = D_s/(a·t)` as operators on `K`.
(The Euler/`δ₀` direction is unused when the transported field has vanishing
`v₀`-component.) -/
def RatioChartDeltaFrame {K : Type*} [Field K]
    (δ : Fin 4 → Derivation ℤ K K)
    (Dr Ds Dt : Derivation ℤ K K) (a s t : K) : Prop :=
  a ≠ 0 ∧ t ≠ 0 ∧
    (∀ z : K, δ 1 z = Dr z / a) ∧
    (∀ z : K, δ 2 z = (Dt z - s / t * Ds z) / a) ∧
    (∀ z : K, δ 3 z = Ds z / (a * t))

/-- Homogenized core ratio-coordinate package: nonzero scales with
`a⁶·P = ι(core)` and `a⁶·t³ = ι(coreSource)`. -/
def CoreRatioCoordinates {K : Type*} [Field K]
    [Algebra (MvPolynomial (Fin 4) ℂ) K]
    (a s t P : K) : Prop :=
  a ≠ 0 ∧ t ≠ 0 ∧
    a ^ 6 * P = algebraMap (MvPolynomial (Fin 4) ℂ) K core ∧
    a ^ 6 * t ^ 3 = algebraMap (MvPolynomial (Fin 4) ℂ) K coreSource

/-- Concrete standard ratio coordinates on a fraction field of the core ring. -/
def StandardCoreRatioCoordinates {K : Type*} [Field K]
    [Algebra (MvPolynomial (Fin 4) ℂ) K]
    (a s t P : K) : Prop :=
  CoreRatioCoordinates a s t P ∧
    a = algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.X 0) ∧
    t = algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.X 2) / a ∧
    s = algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.X 3) /
        algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.X 2)

end HodgeComputer.FourPlusTwoResidual


