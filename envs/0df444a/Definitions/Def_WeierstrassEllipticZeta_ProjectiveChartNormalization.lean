-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
-- name    : WeierstrassEllipticZeta_ProjectiveChartNormalization
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-08T19:58:09.537547+00:00
-- url     : https://prove2.me/theorems/21a41de3-4155-4a20-a4b8-2cecf434139d
-- title:
--   Affine normalization of the elliptic-extension bihomogeneous polynomial
-- statement:
--   Write a polynomial in seven variables as $Q(Y_0,Y_1;X_0,X_1,X_2,X_3,X_4)$. Define two algebra homomorphisms into four-variable polynomial rings over $\mathbb C$ by
--
--   $$N_0Q(t,x,y,r)=Q(1,t;1,x,y,r,yr+2x^2),$$
--
--   $$N_2Q(t,a,b,d)=Q(1,t;a,b,1,ad-2b^2,d).$$
--
--   These substitutions set the additive homogenizing coordinate to one and eliminate a projective coordinate using $X_0X_4-X_2X_3-2X_1^2=0$. The subscripts denote the nonzero homogeneous coordinate, so the Lean indices `0` and `1` select $N_0$ and $N_2$, respectively.
--
--   Only the polynomial substitution maps and their induced complex algebra homomorphisms are defined. Agreement with chart functions, degree bounds, derivative identities and vanishing-order tests are separate theorem obligations. The homomorphisms act on all seven-variable polynomials; bihomogeneity is a hypothesis of the degree theorem, not of these definitions.
-- source:
--   Derived from the elliptic-extension projective coordinates of Senthil Kumar K (2026), Appendix A.2, between (A.3) and (A.4), and the use of bihomogeneous polynomials in Theorem A.2 and (A.8)-(A.9), https://doi.org/10.1017/S001309152610145X. The X0 and X2 substitutions eliminate X4 and X3, respectively, using X0 X4 - X2 X3 - 2 X1^2 = 0. These explicit substitution definitions are formalization infrastructure derived from those coordinates.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial

/-- Substitute the four affine coordinates into the seven homogeneous coordinates.
Chart index zero uses `X₀ ≠ 0`; index one uses `X₂ ≠ 0`. -/
def extensionChartSubstitution (c : Fin 2) : Fin 7 → MvPolynomial (Fin 4) ℂ :=
  if c = 0 then
    ![1, X 0, 1, X 1, X 2, X 3, X 2 * X 3 + C 2 * X 1 ^ 2]
  else
    ![1, X 0, X 1, X 2, 1, X 1 * X 3 - C 2 * X 2 ^ 2, X 3]

/-- Dehomogenization followed by elimination using the extension quadric. -/
def extensionChartNormalize (c : Fin 2) :
    MvPolynomial (Fin 7) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  aeval (extensionChartSubstitution c)

end WeierstrassEllipticZeta


