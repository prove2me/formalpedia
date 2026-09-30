-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
-- name    : WeierstrassEllipticZeta_ProjectiveChartCalculus
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-08T19:34:49.139061+00:00
-- url     : https://prove2.me/theorems/68fc7dc8-8848-4848-9f9e-177b75eeb28d
-- title:
--   Two projective chart coordinate maps and polynomial derivations
-- statement:
--   For complex parameters $g_2,g_3$, consider the two polynomial derivations on four-variable polynomial rings over $\mathbb C$:
--
--   $$\mathcal D_0=\partial_t+y\partial_x+(6x^2-g_2/2)\partial_y-x\partial_r$$
--
--   in variables $(t,x,y,r)$, and
--
--   $$\mathcal D_2=\partial_t+(-6b^2+g_2a^2/2)\partial_a
--   +(-1/2-g_2ab-3g_3a^2/2)\partial_b
--   +(-2g_2b^2-3g_3ab)\partial_d$$
--
--   in variables $(t,a,b,d)$. Their respective cubic polynomials are
--
--   $$G_0=y^2-4x^3+g_2x+g_3,\qquad G_2=a-4b^3+g_2a^2b+g_3a^3.$$
--
--   Given five functions $S_j:\mathbb C\to\mathbb C$, the coordinate maps are
--
--   $$f_0(z)=(z,S_1/S_0,S_2/S_0,S_3/S_0)(z),\qquad
--   f_2(z)=(z,S_0/S_2,S_1/S_2,S_4/S_2)(z),$$
--
--   used on $U_0=\{S_0\ne0\}$ and $U_2=\{S_2\ne0\}$, respectively. These are the affine coordinates for the zero and second homogeneous-coordinate charts of the elliptic-extension model.
--
--   This interface defines only the coordinate maps, derivations and cubic polynomials. Tangency, derivative identities, degree bounds and vanishing criteria are theorem obligations. Quotients are total functions; their chart interpretation is restricted to nonzero denominators. In Lean the chart indices 0 and 1 select homogeneous denominators $S_0$ and $S_2$, respectively.
-- source:
--   Coordinate calculus derived from Senthil Kumar K (2026), Appendix A.2, the homogeneous and regular/lattice-point exponential-map and one-parameter-curve displays between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. The derivation coefficients are those of the proved polynomial chart-flow lemma, obtained from DLMF 23.2.7, 23.3.10 and 23.3.12. Cubic equations are the dehomogenizations of the explicit Weierstrass cubic in the X0 and X2 charts.

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial

/-- Chart index 0 selects X₀ ≠ 0; chart index 1 selects X₂ ≠ 0. -/
def extensionChartDenominator (c : Fin 2) : Fin 5 := if c = 0 then 0 else 2

/-- The additive coordinate and three affine coordinates in either projective chart. -/
def extensionChartCoordinates (S : Fin 5 → ℂ → ℂ) (c : Fin 2) (z : ℂ) : Fin 4 → ℂ :=
  if c = 0 then ![z, S 1 z / S 0 z, S 2 z / S 0 z, S 3 z / S 0 z]
  else ![z, S 0 z / S 2 z, S 1 z / S 2 z, S 4 z / S 2 z]

/-- Polynomial differentiation in the two affine charts. The differential
identities, degree bounds, tangency and jet interpretation are theorem obligations. -/
def extensionChartDerivation (g₂ g₃ : ℂ) (c : Fin 2) :
    Derivation ℂ (MvPolynomial (Fin 4) ℂ) (MvPolynomial (Fin 4) ℂ) :=
  mkDerivation ℂ (if c = 0 then
    ![1, X 2, C 6 * X 1 ^ 2 - C (g₂ / 2), -X 1]
  else
    ![1, C (-6) * X 2 ^ 2 + C (g₂ / 2) * X 1 ^ 2,
      C (-(1 / 2 : ℂ)) - C g₂ * X 1 * X 2 - C (3 * g₃ / 2) * X 1 ^ 2,
      C (-2 * g₂) * X 2 ^ 2 - C (3 * g₃) * X 1 * X 2])

/-- The affine Weierstrass cubic relation in each chart, with the first
variable reserved for the independent additive coordinate. -/
def extensionChartCubic (g₂ g₃ : ℂ) (c : Fin 2) : MvPolynomial (Fin 4) ℂ :=
  if c = 0 then X 2 ^ 2 - C 4 * X 1 ^ 3 + C g₂ * X 1 + C g₃
  else X 1 - C 4 * X 2 ^ 3 + C g₂ * X 1 ^ 2 * X 2 + C g₃ * X 1 ^ 3

end WeierstrassEllipticZeta


