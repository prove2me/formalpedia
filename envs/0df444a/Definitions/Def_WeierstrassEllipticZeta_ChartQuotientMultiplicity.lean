-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ChartQuotientMultiplicity
-- name    : WeierstrassEllipticZeta_ChartQuotientMultiplicity
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T01:06:12.27199+00:00
-- url     : https://prove2.me/theorems/edade2b2-4ff0-443b-9194-7dfdf4603f4f
-- title:
--   Finite quotients and support primes in the first Weierstrass cubic chart
-- statement:
--   For a period pair $L$, let
--
--   $$R=\mathbb C[t,x,y,u],\qquad F_L=y^2-4x^3+g_2x+g_3.$$
--
--   Given an indexing set $Y$, chart quotient multiplicity data consist of an ideal $I\subseteq R$ containing $F_L$, finite-dimensionality of $R/I$ over $\mathbb C$, and an injective assignment of prime ideals
--
--   $$p:Y\longrightarrow\operatorname{Spec}(R),\qquad I\subseteq p(c)\quad(c\in Y).$$
--
--   Its local multiplicity at an index $c$ is
--
--   $$e_c=\ell_{R_{p(c)}}\bigl(R_{p(c)}/IR_{p(c)}\bigr).$$
--
--   This records a finite quotient of the first cubic chart, with distinct support primes. It does not select the ideal or support from an analytic vanishing hypothesis, and does not impose a section-degree bound or a comparison with derivative ideals. Those are separate obligations in an application.
--
--   **Formalization Note** The local multiplicity is the natural-number conversion of the extended natural module length. Finiteness is a conclusion of the accompanying quotient-model theorem. The definition permits an empty indexing set and the unit ideal; if the indexing set is nonempty, prime containment excludes the unit ideal.
-- source:
--   Stacks Project, Proposition 10.9.14 (tag 00CT), https://stacks.math.columbia.edu/tag/00CT: localization commutes with quotient; Lemma 10.52.3 (tag 00IV), https://stacks.math.columbia.edu/tag/00IV: length additivity; the quotient ideal correspondence preserves submodule lattices and module length under surjective scalar restriction. Given a finite complex quotient R/I and distinct support primes p_i containing I, the complete theorem constructs the finite algebra model A=R/I, preserves finrank exactly, and identifies each localization length with length over R_(p_i) of R_(p_i)/IR_(p_i). The new geometric child specializes R to C[t,x,y,u], requires I to contain the first Weierstrass cubic, and retains the chart-budget and uniform section-dimension obligations. It is a sufficient first-chart finite-quotient route, not a formalized converse or a claim that slicing has been constructed. Multiplicities in the source zero-estimate framework: Philippon (1986), section 3, Lemma 3.2, p. 364, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X.

import Definitions.Def_WeierstrassEllipticZeta_FirstCubicChartBase
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

noncomputable section

namespace WeierstrassEllipticZeta

/-- Finite quotient and distinct support primes in the first cubic chart.
The ideal, support, and finite-dimensionality must be constructed in applications. -/
structure ChartQuotientMultiplicityData (L : PeriodPair) (ι : Type) where
  ideal : Ideal (MvPolynomial (Fin 4) ℂ)
  cubic_mem : extensionChartCubic L.g₂ L.g₃ 0 ∈ ideal
  [finite : Module.Finite ℂ (MvPolynomial (Fin 4) ℂ ⧸ ideal)]
  point : ι → PrimeSpectrum (MvPolynomial (Fin 4) ℂ)
  point_injective : Function.Injective point
  ideal_le : ∀ i, ideal ≤ (point i).asIdeal

attribute [instance] ChartQuotientMultiplicityData.finite

/-- Length of the chosen quotient at a support prime of the chart ring. -/
def ChartQuotientMultiplicityData.localLength {L : PeriodPair} {ι : Type}
    (J : ChartQuotientMultiplicityData L ι) (i : ι) : ℕ :=
  (Module.length (Localization.AtPrime (J.point i).asIdeal)
    ((Localization.AtPrime (J.point i).asIdeal) ⧸ J.ideal.map
      (algebraMap (MvPolynomial (Fin 4) ℂ) (Localization.AtPrime (J.point i).asIdeal)))).toNat

end WeierstrassEllipticZeta


