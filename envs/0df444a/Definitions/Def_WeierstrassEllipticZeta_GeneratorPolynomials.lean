-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_GeneratorPolynomials
-- name    : WeierstrassEllipticZeta_GeneratorPolynomials
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T17:39:23.278515+00:00
-- url     : https://prove2.me/theorems/d6604c46-54f5-4e84-b20e-0751dbea49a6
-- title:
--   Bounded polynomials in the nine elliptic generators
-- statement:
--   Fix a complex period pair $L$, with lattice $\Omega$, and complex numbers $\omega,u_1,u_2$. The ordered generator tuple is
--
--   $$y=(\eta_L(\omega),g_2/4,g_3/4,\wp_L(u_1),\wp'_L(u_1),\zeta_L(u_1),
--   \wp_L(u_2),\wp'_L(u_2),\zeta_L(u_2)).$$
--
--   For a point $v$ and nonnegative integers $D,J$, a generator presentation consists of a common denominator $Q$ and three numerators $P_j$ in $\mathbb Z[Y_0,\ldots,Y_8]$, with total degrees at most $D$ and coefficient lengths at most $J$, satisfying
--
--   $$Q(y)\ne0,\qquad P_j(y)=Q(y)x_j(v),\qquad
--   (x_0,x_1,x_2)=(\zeta_L,\wp_L,\wp'_L).$$
--
--   Coefficient length means the sum of the absolute values of all integer coefficients. Numerators may vanish; the evaluated denominator may not.
--
--   The property $\operatorname{EllipticGeneratorPolynomialData}(L,\omega,u_1,u_2)$ asserts that there are positive integers $C,H$, chosen before all indices, with the following property. For every triple $a_1,a_2,a_3\in\mathbb N$, set
--
--   $$v=a_1u_1+a_2u_2+a_3\omega,\qquad T=a_1^2+a_2^2+1.$$
--
--   If $v\notin\Omega$, there is a generator presentation at $v$ with bounds
--
--   $$D=CT,\qquad J=(1+a_3)H^T.$$
--
--   Thus the degree is quadratic in the two nonperiodic indices and independent of the period index; the period index occurs only linearly in the coefficient-length bound. The constants may depend on the fixed lattice and generators. The polynomials may depend on the index triple. This property does not assert that one polynomial family works for every lattice. It contains no arithmetic parameters $\theta,\nu$, auxiliary integer $N$, or reduced polynomial model.
-- source:
--   Interface for the common-denominator polynomial construction in Senthil Kumar K (2026), Section 5 Lemma 7(a), equation (19). The natural-index formulation makes quadratic nonperiodic growth and linear dependence on the period index explicit. The definitions contain no proof of the division-polynomial estimates. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_MovingCoordinates

noncomputable section

namespace WeierstrassEllipticZeta

/-- The nine fixed values in Senthil Kumar's equation (19). -/
def ellipticArithmeticGenerators (L : PeriodPair) (ω u₁ u₂ : ℂ) : Fin 9 → ℂ :=
  ![zetaQuasiPeriod L ω, L.g₂ / 4, L.g₃ / 4,
    L.weierstrassP u₁, L.derivWeierstrassP u₁, weierstrassZeta L u₁,
    L.weierstrassP u₂, L.derivWeierstrassP u₂, weierstrassZeta L u₂]

/-- A common denominator and three numerators in the nine fixed generators. -/
structure EllipticGeneratorPresentation (L : PeriodPair) (ω u₁ u₂ v : ℂ)
    (D H : ℕ) where
  numerator : Fin 3 → MvPolynomial (Fin 9) ℤ
  denominator : MvPolynomial (Fin 9) ℤ
  numerator_degree : ∀ j, (numerator j).totalDegree ≤ D
  denominator_degree : denominator.totalDegree ≤ D
  numerator_length : ∀ j,
    (∑ m ∈ (numerator j).support, ((numerator j).coeff m).natAbs) ≤ H
  denominator_length : (∑ m ∈ denominator.support, (denominator.coeff m).natAbs) ≤ H
  denominator_ne_zero : MvPolynomial.eval₂ (Int.castRingHom ℂ)
    (ellipticArithmeticGenerators L ω u₁ u₂) denominator ≠ 0
  evaluation : ∀ j,
    MvPolynomial.eval₂ (Int.castRingHom ℂ)
      (ellipticArithmeticGenerators L ω u₁ u₂) (numerator j) =
    MvPolynomial.eval₂ (Int.castRingHom ℂ)
      (ellipticArithmeticGenerators L ω u₁ u₂) denominator *
        (![weierstrassZeta L v, L.weierstrassP v, L.derivWeierstrassP v] j)

/-- Quadratic degree and exponential length bounds before arithmetic specialization.
The period index appears only as a linear factor in the coefficient-length bound. -/
def EllipticGeneratorPolynomialData (L : PeriodPair) (ω u₁ u₂ : ℂ) : Prop :=
  ∃ C H : ℕ, 0 < C ∧ 0 < H ∧ ∀ a : Fin 3 → ℕ,
    integerGridPoint u₁ u₂ ω (fun j => a j) ∉ L.lattice →
    Nonempty (EllipticGeneratorPresentation L ω u₁ u₂
      (integerGridPoint u₁ u₂ ω (fun j => a j))
      (C * (a 0 ^ 2 + a 1 ^ 2 + 1))
      ((1 + a 2) * H ^ (a 0 ^ 2 + a 1 ^ 2 + 1)))

end WeierstrassEllipticZeta


