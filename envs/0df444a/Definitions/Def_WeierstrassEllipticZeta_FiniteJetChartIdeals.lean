-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_FiniteJetChartIdeals
-- name    : WeierstrassEllipticZeta_FiniteJetChartIdeals
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T04:26:25.352105+00:00
-- url     : https://prove2.me/theorems/5eefe005-e2bc-4d93-832f-73f330ae1dfe
-- title:
--   Dimension-bounded finite-jet ideals in the Weierstrass cubic chart
-- statement:
--   For the first Weierstrass cubic chart, this data consists of an injectively indexed family of points and ideals containing the chart cubic. At each point x the corresponding ideal J satisfies
--
--   $$
--   \mathfrak m_x^{d}\subseteq J\subseteq\mathfrak m_x,
--   \qquad d=\dim_{\mathbf C}(\mathbf C[t,x,y,u]/J).
--   $$
--
--   These are exact finite-jet conditions, with the exponent fixed by the quotient dimension. The complete punctual finite-jet characterization proves that they are equivalent to requiring the zero locus of J to be precisely the specified point. They also force d to be positive and the jet algebra to be finite-dimensional, despite finrank's default value of zero for infinite-dimensional spaces.
--
--   The local length is defined using the same localization and ideal quotient as in PunctualChartIdealData. The support points remain auxiliary; this definition imposes no new identification with the analytic chart points used by CappedChartJetBudget.
-- source:
--   Stacks Project, Artinian radical nilpotence, Lemma 10.53.4, https://stacks.math.columbia.edu/tag/00J8; Hilbert Nullstellensatz, https://stacks.math.columbia.edu/tag/00FV. In a finite-dimensional algebra A, nonzero powers of a nilpotent ideal strictly decrease in dimension, so its dim(A)-th power vanishes. Applied to the quotient R/I, this proves radical(I)^dim(R/I) <= I. For polynomial ideals with singleton zero set {x}, this yields the exact finite-jet criterion m_x^d <= I <= m_x with d=dim(R/I), and reconstruction of I from its image in the finite jet algebra. The A.1 application gives an equivalent finite-jet formulation of the punctual-chart frontier, retaining the same ideals, lengths, dimensions and uniform constant. Witness selection and the geometric sum-of-dimensions bound remain open; no bidegree or integer-search bound is improved.

import Definitions.Def_WeierstrassEllipticZeta_PunctualChartIdeals

noncomputable section
namespace WeierstrassEllipticZeta

/-- Point-supported chart ideals specified by an exact finite-jet power sandwich.
The truncation exponent is the dimension of the corresponding quotient. -/
structure FiniteJetChartIdealData (L : PeriodPair) (ι : Type) where
  point : ι → Fin 4 → ℂ
  point_injective : Function.Injective point
  ideal : ι → Ideal (MvPolynomial (Fin 4) ℂ)
  cubic_mem : ∀ i, extensionChartCubic L.g₂ L.g₃ 0 ∈ ideal i
  power_le : ∀ i, (MvPolynomial.vanishingIdeal ℂ {point i}) ^
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ ideal i) ≤ ideal i
  le_point : ∀ i, ideal i ≤ MvPolynomial.vanishingIdeal ℂ {point i}

/-- Local length retains the original chart localization, including nilpotents. -/
def FiniteJetChartIdealData.localLength {L : PeriodPair} {ι : Type}
    (J : FiniteJetChartIdealData L ι) (i : ι) : ℕ :=
  (Module.length (Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (J.point i)).asIdeal)
    ((Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (J.point i)).asIdeal) ⧸ (J.ideal i).map
      (algebraMap (MvPolynomial (Fin 4) ℂ)
        (Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (J.point i)).asIdeal)))).toNat

end WeierstrassEllipticZeta


