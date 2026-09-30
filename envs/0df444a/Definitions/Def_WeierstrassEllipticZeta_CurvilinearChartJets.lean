-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_CurvilinearChartJets
-- name    : WeierstrassEllipticZeta_CurvilinearChartJets
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T09:39:26.895142+00:00
-- url     : https://prove2.me/theorems/c6a2fc86-82b7-4290-b807-439055191914
-- title:
--   Curvilinear jets along the additive coordinate of the elliptic chart
-- statement:
--   For complex a,b and a natural number e, substitute t=T+a, x=0, y=b and u=0 in C[t,x,y,u], then reduce modulo T^e. Define the curvilinear chart ideal as the kernel of this algebra map to C[T]/(T^e).
--
--   For e>0 this is a jet supported at the point (a,0,b,0), along the additive coordinate. When b^2=-g_3, the elliptic cubic y^2-4x^3+g_2*x+g_3 belongs to the kernel. These properties, the dimension and the local length are proved separately.
-- source:
--   Explicit curvilinear length realization for the current A.1 interface. The model is C[T]/(T^e), with basis 1,T,...,T^(e-1), embedded along the additive coordinate of the cubic chart at (a,0,b,0), b^2=-g3. Length comparison and localization use the composition-series principles in Stacks Project, Section 10.52, Lemmas 10.52.5, 10.52.6 and 10.52.11, https://stacks.math.columbia.edu/tag/00IU. This is a derived auxiliary construction, not a theorem quoted from Kumar's Appendix A. Every prescribed positive length is realized exactly, and the existing frontier reduces equivalently to a uniform sum of positive chart budgets. The locus and constant are preserved; no identification of these auxiliary ideals with derivative ideals or analytic support points is asserted. The geometric selection and uniform bound remain open.

import Definitions.Def_WeierstrassEllipticZeta_FiniteJetChartIdeals
import Mathlib.RingTheory.AdjoinRoot

noncomputable section
namespace WeierstrassEllipticZeta

/-- The length-e jet along the additive coordinate at (a,0,b,0). -/
def curvilinearChartRestriction (a b : ℂ) (e : ℕ) :
    MvPolynomial (Fin 4) ℂ →ₐ[ℂ]
      (Polynomial ℂ ⧸ Ideal.span {(Polynomial.X : Polynomial ℂ) ^ e}) :=
  (Ideal.Quotient.mkₐ ℂ _).comp
    (MvPolynomial.aeval ![Polynomial.X + Polynomial.C a, 0, Polynomial.C b, 0])

/-- Its kernel fixes the three elliptic-chart coordinates and truncates the additive one. -/
def curvilinearChartIdeal (a b : ℂ) (e : ℕ) : Ideal (MvPolynomial (Fin 4) ℂ) :=
  RingHom.ker (curvilinearChartRestriction a b e).toRingHom

end WeierstrassEllipticZeta


