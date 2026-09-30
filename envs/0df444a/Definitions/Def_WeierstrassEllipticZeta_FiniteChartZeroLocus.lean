-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_FiniteChartZeroLocus
-- name    : WeierstrassEllipticZeta_FiniteChartZeroLocus
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T01:49:21.115122+00:00
-- url     : https://prove2.me/theorems/c488dc8b-ab95-460e-8e15-9c792e682090
-- title:
--   Finite zero sets and labelled points in the first Weierstrass cubic chart
-- statement:
--   Fix a period pair and write the first chart ring as
--
--   $$R=\mathbb C[t,x,y,u],\qquad F=y^2-4x^3+g_2x+g_3.$$
--
--   The data consist of an ideal containing the cubic relation, a proof that its complex zero set is finite, and a distinctly labelled family of points in that zero set:
--
--   $$F\in I,\qquad V_{\mathbb C}(I)\text{ finite},\qquad a:\iota\hookrightarrow V_{\mathbb C}(I).$$
--
--   There is no assumption of finite-dimensionality of the quotient in this definition. The associated local multiplicity is the length of the original localized quotient at the evaluation ideal of the labelled point:
--
--   $$\mu_i=\ell_{R_{\mathfrak m_{a_i}}}\bigl(R_{\mathfrak m_{a_i}}/IR_{\mathfrak m_{a_i}}\bigr),\qquad
--   \mathfrak m_a=\ker(\operatorname{ev}_a).$$
--
--   The interface uses the natural-number conversion of this extended-natural length. Finiteness follows from the separately proved finite-zero-set criterion and the earlier quotient-localization theorem. The ideal is retained with its full scheme multiplicity, and need not be radical. The labelled family need not exhaust the zero set. Selecting a suitable ideal and points from the analytic vanishing hypotheses, and bounding the multiplicities, remain application-specific tasks.
-- source:
--   Stacks Project, Theorem 10.34.1 (Hilbert Nullstellensatz), https://stacks.math.columbia.edu/tag/00FV; Lemma 10.36.5 (finite type and integral imply finite), https://stacks.math.columbia.edu/tag/02JJ; section 10.53, https://stacks.math.columbia.edu/tag/00J4 (finite-dimensional algebras are Artinian, with finitely many primes, all maximal). The complete theorem proves, for any ideal in finitely many variables over an algebraically closed field, that its full coordinate quotient is finite-dimensional iff its zero set is finite. It also identifies the support primes with unique evaluation points. The ideal need not be radical. Application to the first Weierstrass chart in Senthil Kumar's A.1 multiplicity frontier: replace finite-dimensional quotient data and support primes by a finite zero set and distinct labelled chart points, preserving the ideal, local lengths, dimension and uniform constant exactly. A checked local converse shows this replacement is equivalent. This does not construct the geometric ideal from the high-order vanishing hypotheses or prove the uniform section-dimension bound.

import Definitions.Def_WeierstrassEllipticZeta_ChartQuotientMultiplicity
import Mathlib.RingTheory.Nullstellensatz

noncomputable section

namespace WeierstrassEllipticZeta

/-- A finite zero set in the first Weierstrass chart, with distinctly labelled points.
No finite-dimensionality assumption is placed on the coordinate quotient. -/
structure FiniteChartZeroLocusData (L : PeriodPair) (ι : Type) where
  ideal : Ideal (MvPolynomial (Fin 4) ℂ)
  cubic_mem : extensionChartCubic L.g₂ L.g₃ 0 ∈ ideal
  finite_zeroLocus : (MvPolynomial.zeroLocus ℂ ideal).Finite
  point : ι → Fin 4 → ℂ
  point_injective : Function.Injective point
  point_mem : ∀ i, point i ∈ MvPolynomial.zeroLocus ℂ ideal

/-- The length of the full ideal at the evaluation prime of a labelled zero.
The ideal is not replaced by its radical, so nilpotent multiplicity is retained. -/
def FiniteChartZeroLocusData.localLength {L : PeriodPair} {ι : Type}
    (Z : FiniteChartZeroLocusData L ι) (i : ι) : ℕ :=
  (Module.length (Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (Z.point i)).asIdeal)
    ((Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (Z.point i)).asIdeal) ⧸ Z.ideal.map
      (algebraMap (MvPolynomial (Fin 4) ℂ)
        (Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (Z.point i)).asIdeal)))).toNat

end WeierstrassEllipticZeta


