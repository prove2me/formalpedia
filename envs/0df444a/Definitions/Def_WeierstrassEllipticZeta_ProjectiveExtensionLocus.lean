-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
-- name    : WeierstrassEllipticZeta_ProjectiveExtensionLocus
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-08T16:56:53.180642+00:00
-- url     : https://prove2.me/theorems/3ed722ff-ead4-433a-bc5a-dcf0061721ca
-- title:
--   Quadratic and cubic polynomials for the elliptic-extension projective locus
-- statement:
--   For complex parameters $g_2,g_3$, define
--
--   $$q=X_0X_4-X_2X_3-2X_1^2,\qquad
--   c_{g_2,g_3}=X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3.$$
--
--   The type $Z_{g_2,g_3}$ consists of projective points in $\mathbb P^4(\mathbb C)$ whose standard chosen nonzero representative satisfies both polynomial equations. Homogeneity and invariance under changing representative are mathematical obligations, as is containment of the elliptic-extension image in this locus. The definition assumes no dimension, smoothness, irreducibility or algebraic-group structure.
-- source:
--   Polynomial relations derived from the five exponential-map coordinates in Senthil Kumar K (2026), Appendix A.2 between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X, and the Weierstrass differential equation DLMF 23.3.10, https://dlmf.nist.gov/23.3.E10. The quadratic eliminates u+zeta and the cubic homogenizes the differential equation.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace WeierstrassEllipticZeta

/-- The quadratic relation in the five elliptic-extension coordinates. -/
def extensionQuadric : MvPolynomial (Fin 5) ℂ :=
  MvPolynomial.X 0 * MvPolynomial.X 4 - MvPolynomial.X 2 * MvPolynomial.X 3 -
    MvPolynomial.C 2 * MvPolynomial.X 1 ^ 2

/-- The homogenized Weierstrass relation in the first three coordinates. -/
def extensionCubic (g₂ g₃ : ℂ) : MvPolynomial (Fin 5) ℂ :=
  MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 - MvPolynomial.C 4 * MvPolynomial.X 1 ^ 3 +
    MvPolynomial.C g₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
    MvPolynomial.C g₃ * MvPolynomial.X 0 ^ 3

/-- The projective locus cut out by the quadratic and cubic relations.
Its set of complex points is defined here using the standard chosen representative.
Homogeneity and independence from that choice are separate theorem obligations.
No dimension, smoothness, or algebraic-group structure is assumed. -/
def ProjectiveExtensionLocus (g₂ g₃ : ℂ) :=
  {p : Projectivization ℂ (Fin 5 → ℂ) //
    MvPolynomial.eval p.rep extensionQuadric = 0 ∧
      MvPolynomial.eval p.rep (extensionCubic g₂ g₃) = 0}

end WeierstrassEllipticZeta


