-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_PunctualChartIdeals
-- name    : WeierstrassEllipticZeta_PunctualChartIdeals
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T02:52:19.217974+00:00
-- url     : https://prove2.me/theorems/cbae8edc-7373-445b-9244-66b3c94ceddd
-- title:
--   Point-supported ideals in the first Weierstrass cubic chart
-- statement:
--   Fix a period pair and a label set. In the first Weierstrass chart, write
--
--   $$R=\mathbb C[t,x,y,u],\qquad F=y^2-4x^3+g_2x+g_3.$$
--
--   The data assign a point and an ideal to each label. The points are distinct, every ideal contains the cubic equation, and each ideal has exactly its assigned point as complex zero set:
--
--   $$a:\iota\hookrightarrow\mathbb C^4,\qquad
--   F\in I_i,\qquad V_{\mathbb C}(I_i)=\{a_i\}.$$
--
--   The ideals retain their full nilpotent structure. In particular, they are not required to equal the reduced evaluation ideals. Their finite-dimensionality follows from the separately proved finite-zero-set criterion.
--
--   The local multiplicity assigned to a label is the length of its localized quotient at the evaluation ideal of the point:
--
--   $$\mu_i=\ell_{R_{\mathfrak m_{a_i}}}\bigl(R_{\mathfrak m_{a_i}}/I_iR_{\mathfrak m_{a_i}}\bigr).$$
--
--   The formal interface converts this extended-natural length to a natural number, just as the parent interface does. The new data contain no budget or dimension estimate; those are obligations of the geometric theorem. A finite collection can be assembled into one global chart ideal by intersection, with exact local multiplicity and total-dimension identities.
-- source:
--   Stacks Project, Chinese remainder theorem, Lemma 10.15.4, https://stacks.math.columbia.edu/tag/00DT; Artinian local decomposition, Lemma 10.53.6, https://stacks.math.columbia.edu/tag/00JB; nilpotence of the radical, Lemma 10.53.4, https://stacks.math.columbia.edu/tag/00J8. The proof uses the already proved finite-zero-set criterion to pass between point-supported polynomial ideals and finite-dimensional coordinate algebras. Pairwise distinct support points make the ideals comaximal. Their intersection retains every selected localization, has exactly the selected zero set, and has quotient dimension equal to the sum of component dimensions. Conversely, from a finite quotient and selected zeros, construct I + m_i^(N_i) using nilpotence in the local quotient. This preserves each selected localization and the total component dimension is at most the original dimension. Application to A.1: construction of the global chart quotient is reduced equivalently to individual point-supported chart ideals with the same local multiplicity budgets and a bound on their total dimensions. The same uniform constant is retained. Neither selection of those ideals from the analytic vanishing data nor the uniform geometric dimension estimate is claimed.

import Definitions.Def_WeierstrassEllipticZeta_FiniteChartZeroLocus

noncomputable section

namespace WeierstrassEllipticZeta

/-- An ideal supported at each of a distinctly indexed family of cubic-chart points.
These ideals retain their full nilpotent structure. -/
structure PunctualChartIdealData (L : PeriodPair) (ι : Type) where
  point : ι → Fin 4 → ℂ
  point_injective : Function.Injective point
  ideal : ι → Ideal (MvPolynomial (Fin 4) ℂ)
  cubic_mem : ∀ i, extensionChartCubic L.g₂ L.g₃ 0 ∈ ideal i
  zeroLocus_eq : ∀ i, MvPolynomial.zeroLocus ℂ (ideal i) = {point i}

/-- Local length of the single-point ideal assigned to a label. -/
def PunctualChartIdealData.localLength {L : PeriodPair} {ι : Type}
    (P : PunctualChartIdealData L ι) (i : ι) : ℕ :=
  (Module.length (Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (P.point i)).asIdeal)
    ((Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (P.point i)).asIdeal) ⧸ (P.ideal i).map
      (algebraMap (MvPolynomial (Fin 4) ℂ)
        (Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (P.point i)).asIdeal)))).toNat

end WeierstrassEllipticZeta


