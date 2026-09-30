-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_MultiplePolynomials
-- name    : WeierstrassEllipticZeta_MultiplePolynomials
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T18:14:01.883854+00:00
-- url     : https://prove2.me/theorems/61dd2aaa-2ba0-4c8b-b17c-d2fcfd0d2b7d
-- title:
--   Quantitative single-point elliptic multiplication presentations
-- statement:
--   Fix a complex period pair $L$ with lattice $\Omega$ and a point $u\in\mathbb C$. The five single-point generators are
--
--   $$y_u=(g_2/4,g_3/4,\wp_L(u),\wp'_L(u),\zeta_L(u)).$$
--
--   For natural numbers $n,D,J$, a multiple presentation consists of a common denominator $Q$ and three numerators $P_j$ in $\mathbb Z[Y_0,\ldots,Y_4]$. All four polynomials have total degree at most $D$ and coefficient length at most $J$, where coefficient length is the sum of the absolute values of the integer coefficients. They satisfy
--
--   $$Q(y_u)\ne0,\qquad P_j(y_u)=Q(y_u)x_j(nu),\qquad
--   (x_0,x_1,x_2)=(\zeta_L,\wp_L,\wp'_L).$$
--
--   The property $\operatorname{EllipticMultiplePolynomialData}(L,u)$ asserts that there are positive natural constants $C,H$, chosen before all indices, such that for every positive integer $n$ there is a multiple presentation with
--
--   $$D=Cn^2,\qquad J=H^{n^2}.$$
--
--   Numerators may vanish. Evaluated denominators may not. There is no requirement at index zero. The constants and polynomials may depend on the fixed lattice and point; the polynomials may also depend on the index. The predicate itself asserts these presentations at all positive indices. The theorem establishing it assumes that all positive multiples of the point are outside the lattice. No arithmetic parameters, auxiliary grid, or period generator occur in this property.
-- source:
--   Presentation interface for Senthil Kumar K (2026), Section 4 Lemma 5, equation (12), and its use in Section 5 Lemma 7(a). It records a common nonzero denominator, quadratic degree, and exponential coefficient length at positive multiples of one point. It does not assert or define the division polynomials themselves. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_GeneratorPolynomials

noncomputable section

namespace WeierstrassEllipticZeta

/-- The five generators needed for multiplication at a single point. -/
def ellipticMultipleGenerators (L : PeriodPair) (u : ℂ) : Fin 5 → ℂ :=
  ![L.g₂ / 4, L.g₃ / 4, L.weierstrassP u, L.derivWeierstrassP u, weierstrassZeta L u]

/-- A common denominator for the three elliptic values at a natural multiple. -/
structure EllipticMultiplePresentation (L : PeriodPair) (u : ℂ) (n D H : ℕ) where
  numerator : Fin 3 → MvPolynomial (Fin 5) ℤ
  denominator : MvPolynomial (Fin 5) ℤ
  numerator_degree : ∀ j, (numerator j).totalDegree ≤ D
  denominator_degree : denominator.totalDegree ≤ D
  numerator_length : ∀ j,
    (∑ m ∈ (numerator j).support, ((numerator j).coeff m).natAbs) ≤ H
  denominator_length : (∑ m ∈ denominator.support, (denominator.coeff m).natAbs) ≤ H
  denominator_ne_zero : MvPolynomial.eval₂ (Int.castRingHom ℂ)
    (ellipticMultipleGenerators L u) denominator ≠ 0
  evaluation : ∀ j,
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u) (numerator j) =
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u) denominator *
      (![weierstrassZeta L (n * u), L.weierstrassP (n * u),
        L.derivWeierstrassP (n * u)] j)

/-- The quadratic division-polynomial bounds needed at one nontorsion point. -/
def EllipticMultiplePolynomialData (L : PeriodPair) (u : ℂ) : Prop :=
  ∃ C H : ℕ, 0 < C ∧ 0 < H ∧ ∀ n : ℕ, 0 < n →
    Nonempty (EllipticMultiplePresentation L u n (C * n ^ 2) (H ^ (n ^ 2)))

end WeierstrassEllipticZeta


