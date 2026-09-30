-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_MovingCoordinates
-- name    : WeierstrassEllipticZeta_MovingCoordinates
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T17:18:57.394204+00:00
-- url     : https://prove2.me/theorems/2c73eea4-ba85-4dc6-957c-a44cda6882c2
-- title:
--   Quantitative presentations of the three moving elliptic coordinates
-- statement:
--   Fix a complex period pair $L$ with lattice $\Omega$, and complex numbers $\omega,u_1,u_2,\theta,\nu$. Let $\mathscr L(P)$ denote the sum of the absolute values of all integer coefficients of a polynomial. For sufficiently large positive integers $N$, put
--
--   $$s=\lfloor N^{3/16}\rfloor,\qquad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--
--   $$\Gamma_3=\{a_1u_1+a_2u_2+a_3\omega:
--   0\le a_1,a_2<3s,\ 0\le a_3<3q,\ a_i\in\mathbb Z\}.$$
--
--   Moving elliptic coordinate data assert that there is a nonnegative integer $C$ such that, for every sufficiently large $N$ and every nonlattice point $v\in\Gamma_3$, there are three numerator polynomials $P_j$, denominator polynomials $Q_j$ in $\mathbb Z[X,Y]$, and nonnegative integers $h_j$, with
--
--   $$\deg P_j,\deg Q_j\le Cs^2,\qquad
--   \mathscr L(P_j),\mathscr L(Q_j)\le h_j\le e^{C(s^2+\log N)},$$
--
--   $$Q_j(\theta,\nu)\ne0,\qquad
--   P_j(\theta,\nu)=Q_j(\theta,\nu)y_j(v),\qquad
--   (y_0,y_1,y_2)=(\zeta_L,\wp_L,\wp'_L).$$
--
--   The constant and threshold precede all grid points. A presentation is the collection of these polynomials, bounds, and evaluation identities at one point. Numerators may vanish; evaluated denominators may not. This property concerns the three moving elliptic values only. The ordinary coordinate and the four fixed jet coordinates are supplied separately by the coordinate-completion theorem.
-- source:
--   Coordinate-presentation interface for Senthil Kumar K (2026), Section 5 Lemma 7(a), equation (19), with the degree and height estimates there. A log N allowance in the length profile accommodates the period coordinate in zeta(v). Construction from division polynomials is not included in this definition. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices

noncomputable section

namespace WeierstrassEllipticZeta

/-- The three moving elliptic coordinates, with quantitative rational presentations. -/
structure MovingEllipticCoordinatePresentation (L : PeriodPair) (θ ν v : ℂ)
    (C N s : ℕ) where
  numerator : Fin 3 → MvPolynomial (Fin 2) ℤ
  denominator : Fin 3 → MvPolynomial (Fin 2) ℤ
  lengthBound : Fin 3 → ℕ
  numerator_degree : ∀ a, (numerator a).totalDegree ≤ C * s ^ 2
  denominator_degree : ∀ a, (denominator a).totalDegree ≤ C * s ^ 2
  numerator_length : ∀ a,
    (∑ b ∈ (numerator a).support, ((numerator a).coeff b).natAbs) ≤ lengthBound a
  denominator_length : ∀ a,
    (∑ b ∈ (denominator a).support, ((denominator a).coeff b).natAbs) ≤ lengthBound a
  length_le : ∀ a, (lengthBound a : ℝ) ≤ Real.exp (C * ((s : ℝ) ^ 2 + Real.log N))
  denominator_ne_zero : ∀ a,
    MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (denominator a) ≠ 0
  evaluation : ∀ a,
    MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (numerator a) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (denominator a) *
        (![weierstrassZeta L v, L.weierstrassP v, L.derivWeierstrassP v] a)

/-- The arithmetic construction still needed after completing ordinary and fixed coordinates. -/
def AuxiliaryMovingCoordinateData (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) : Prop :=
  ∃ C : ℕ, ∀ᶠ N : ℕ in Filter.atTop,
    ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
      v ∉ L.lattice →
        Nonempty (MovingEllipticCoordinatePresentation L θ ν v C N (auxiliaryS N))

end WeierstrassEllipticZeta


