-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ChartPrimeMultiplicityData
-- name    : WeierstrassEllipticZeta_ChartPrimeMultiplicityData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T19:24:26.060987+00:00
-- url     : https://prove2.me/theorems/d42d4391-1101-4c03-81bb-59c6d00f47de
-- title:
--   Concrete prime multiplicity data in the Weierstrass charts
-- statement:
--   Fix the period pair $L$, the five projective coordinate functions $S$, a polynomial $Q$ in the seven homogeneous variables, and natural numbers $T,e$. `ChartPrimeMultiplicityData L S Q T e` supplies the following algebraic data in the fixed ring $A=\mathbb C[T,X_1,X_2,X_3]$:
--
--   - A chart index $c\in\{0,1\}$ and a point $z_0$ where its denominator is nonzero. The denominators are $S_0$ and $S_2$ respectively.
--   - An ideal $I\subseteq A$ and a minimal prime $\mathfrak p$ over $I$.
--   - Membership $Q_c\in\mathfrak p$ for the normalized chart polynomial, and vanishing $r(v_c(z_0))=0$ for every $r\in\mathfrak p$.
--   - Differential contact $\delta_c^j r\in\mathfrak p$ for every $r\in I$ and $0\le j\le T$.
--   - The localized length bound $\operatorname{length}_{A_{\mathfrak p}}(A_{\mathfrak p}/IA_{\mathfrak p})\le e$.
--
--   Here the coordinates $v_c$, normalized polynomial $Q_c$, and derivation $\delta_c$ are the fixed Weierstrass chart definitions. The ring is automatically Noetherian. The structure does not supply an arbitrary ring, a derivation, an orbit map, analyticity, or a finite-order hypothesis. The separate complete chart-orbit theorem constructs the analytic data from the global Weierstrass hypotheses and functional nonvanishing.
--
--   **Formalization Note.** These are sufficient data for the new concrete chart route. The structure does not assert their existence or identify the ideal with a selected irreducible component. Selecting suitable ideals, minimal primes and points, proving contact, and bounding the sum of lengths remain in the Open child. No converse with arbitrary abstract analytic-orbit data is claimed.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383. Definition of analytic order in local projective coordinates, section 2, pp. 357-358; coordinate-independence argument in Proposition 4.3, pp. 373-374. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Auxiliary realization in the two explicit Weierstrass charts: construct evaluation and germ-level differential compatibility, and deduce a nonzero analytic germ from the nonzero entire projective pullback. The proof reuses the Proved chart-flow and chart-jet theorems. Component and prime selection and the uniform total degree estimate remain open.

import Definitions.Def_TranscendenceTheory_AnalyticOrbitMultiplicityData
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.RingTheory.Polynomial.Basic

noncomputable section
namespace WeierstrassEllipticZeta

/-- Concrete prime and ideal data in one of the two Weierstrass affine charts.
The ring, derivation, orbit map, analyticity, and nonzero germ are not supplied.
They are fixed by the chart and proved from the global geometric inputs. -/
structure ChartPrimeMultiplicityData (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (T e : ℕ) where
  chart : Fin 2
  z : ℂ
  chart_ne : S (extensionChartDenominator chart) z ≠ 0
  I : Ideal (MvPolynomial (Fin 4) ℂ)
  p : Ideal (MvPolynomial (Fin 4) ℂ)
  [prime : p.IsPrime]
  minimal : p ∈ I.minimalPrimes
  normalized_mem : extensionChartNormalize chart Q ∈ p
  point_on_prime : ∀ r ∈ p, MvPolynomial.eval (extensionChartCoordinates S chart z) r = 0
  jets : ∀ r ∈ I, ∀ k ≤ T, ((extensionChartDerivation L.g₂ L.g₃ chart)^[k]) r ∈ p
  length_le : Module.length (Localization.AtPrime p)
    ((Localization.AtPrime p) ⧸ I.map
      (algebraMap (MvPolynomial (Fin 4) ℂ) (Localization.AtPrime p))) ≤ (e : ℕ∞)

attribute [instance] ChartPrimeMultiplicityData.prime

end WeierstrassEllipticZeta


