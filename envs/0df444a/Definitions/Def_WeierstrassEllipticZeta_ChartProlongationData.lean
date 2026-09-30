-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ChartProlongationData
-- name    : WeierstrassEllipticZeta_ChartProlongationData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T19:43:32.804979+00:00
-- url     : https://prove2.me/theorems/8f81217f-843f-4a10-b339-610be8d74105
-- title:
--   Derivative ideals and persistent minimal-prime chart data
-- statement:
--   This definition package supplies the derivative ideal
--
--   $$P_n(I)=\bigl(D^k f:f\in I,\ 0\le k\le n\bigr)$$
--
--   for an arbitrary derivation $D$ on a commutative algebra, and the associated data for a persistent minimal prime in a Weierstrass chart. The complete theorem separately proves $P_0(I)=I$, composition of these operations, and the contact interpretation of prime persistence.
--
--   Fix $L,S,Q,T,e$ as in the chart-prime frontier. `ChartProlongationMultiplicityData L S Q T e` supplies:
--
--   - A chart index $c\in\{0,1\}$ and a point $z_0$ at which its denominator is nonzero.
--   - A base ideal $J$ in $A=\mathbb C[T,X_1,X_2,X_3]$ and a natural stage $s$; the derivative ideals use the fixed chart derivation $\delta_c$.
--   - A prime $\mathfrak p$ which is minimal over both $P_s(J)$ and $P_{s+T}(J)$.
--   - Membership $Q_c\in\mathfrak p$ for the normalized chart polynomial, and vanishing $r(v_c(z_0))=0$ for every $r\in\mathfrak p$.
--   - A localized length bound $\operatorname{length}_{A_{\mathfrak p}}(A_{\mathfrak p}/P_s(J)A_{\mathfrak p})\le e$.
--
--   Differential contact on $P_s(J)$ is a consequence of persistence, not a field of this structure. The datum includes no claim that an appropriate base ideal or persistent prime exists.
--
--   **Formalization Note.** A checked local converse recovers these data from any previous `ChartPrimeMultiplicityData` by taking its ideal as the base and stage zero. Thus the two data conditions are equivalent at fixed $L,S,Q,T,e$, without changing the point, prime or local length. The remaining child must select suitable data and prove the uniform total degree bound.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383. Proposition 4.3, pp. 373-374: composition of derivative operators on ideals; section 5, pp. 380-382: the component-selection argument. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. One-derivation affine algebraic composition lemma, with an exact minimal-prime persistence/contact equivalence. This is not the full projective translation and component-saturation statement of Proposition 4.3. Selecting a persistent component and proving the uniform global degree bound remain open.

import Definitions.Def_WeierstrassEllipticZeta_ChartPrimeMultiplicityData

noncomputable section

namespace TranscendenceTheory

/-- Adjoin all derivatives through order `n` of all elements of an ideal. -/
def differentialProlongation {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (D : Derivation K R R) (I : Ideal R) (n : ℕ) : Ideal R :=
  Ideal.span {r | ∃ f ∈ I, ∃ k ≤ n, (D^[k]) f = r}

end TranscendenceTheory

namespace WeierstrassEllipticZeta
open TranscendenceTheory

/-- A chart component that persists between two stages of derivative ideals.
Contact through `T` on the first stage follows from the two minimal-prime fields. -/
structure ChartProlongationMultiplicityData (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (T e : ℕ) where
  chart : Fin 2
  z : ℂ
  chart_ne : S (extensionChartDenominator chart) z ≠ 0
  base : Ideal (MvPolynomial (Fin 4) ℂ)
  stage : ℕ
  p : Ideal (MvPolynomial (Fin 4) ℂ)
  [prime : p.IsPrime]
  minimal_start : p ∈ (differentialProlongation
    (extensionChartDerivation L.g₂ L.g₃ chart) base stage).minimalPrimes
  minimal_end : p ∈ (differentialProlongation
    (extensionChartDerivation L.g₂ L.g₃ chart) base (stage + T)).minimalPrimes
  normalized_mem : extensionChartNormalize chart Q ∈ p
  point_on_prime : ∀ r ∈ p, MvPolynomial.eval (extensionChartCoordinates S chart z) r = 0
  length_le : Module.length (Localization.AtPrime p)
    ((Localization.AtPrime p) ⧸ (differentialProlongation
      (extensionChartDerivation L.g₂ L.g₃ chart) base stage).map
      (algebraMap (MvPolynomial (Fin 4) ℂ) (Localization.AtPrime p))) ≤ (e : ℕ∞)

attribute [instance] ChartProlongationMultiplicityData.prime

end WeierstrassEllipticZeta


