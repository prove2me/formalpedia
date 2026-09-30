-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
-- name    : WeierstrassEllipticZeta_GridJetMatrices
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T16:41:27.136931+00:00
-- url     : https://prove2.me/theorems/924b705e-e41e-41fa-afdc-29ee3d12ac71
-- title:
--   Quantitative grid-coordinate presentations and assembled derivative matrices
-- statement:
--   Fix a complex period pair with lattice $\Omega$, and complex numbers $\omega,u_1,u_2,\theta,\nu$. Write $z_0=u_1/2$ and let $\mathscr L(P)$ be the sum of the absolute values of the integer coefficients of a polynomial $P$. For a nonnegative integer $N$, put
--
--   $$s=\lfloor N^{3/16}\rfloor,\qquad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--
--   $$\Gamma_3=\{a_1u_1+a_2u_2+a_3\omega: 0\le a_1,a_2<3s,\ 0\le a_3<3q,\ a_i\in\mathbb Z\}.$$
--
--   For a nonnegative integer $C$, use the coordinate degree and logarithmic length profiles
--
--   $$d_C=(C,Cs^2,Cs^2,Cs^2,C,C,C,C),$$
--
--   $$b_C=(C\log N,C(s^2+\log N),C(s^2+\log N),C(s^2+\log N),C,C,C,C).$$
--
--   A coordinate presentation at $v,z$ consists of eight numerator polynomials $P_a$, denominator polynomials $Q_a$ in $\mathbb Z[X,Y]$, and nonnegative integers $h_a$, such that
--
--   $$\deg P_a,\deg Q_a\le d_{C,a},\qquad
--   \mathscr L(P_a),\mathscr L(Q_a)\le h_a\le e^{b_{C,a}},$$
--
--   $$Q_a(\theta,\nu)\ne0,\qquad P_a(\theta,\nu)=Q_a(\theta,\nu)J_v(z)_a,$$
--
--   $$J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)).$$
--
--   Auxiliary nonlattice coordinate data assert
--
--   $$\exists C\in\mathbb N\ \forall N\text{ sufficiently large}\ \forall v\in\Gamma_3\setminus\Omega,
--   \quad\text{there exists a coordinate presentation at }v,z_0.$$
--
--   The constant and threshold precede all points. Every evaluated denominator is nonzero. The four fixed-coordinate bounds are independent of $N$, the ordinary coordinate has fixed degree and polynomial length in $N$, and the three moving elliptic coordinates have degree $O(s^2)$ and logarithmic length $O(s^2+\log N)$. No derivative matrices or analytic estimates are part of this coordinate property.
--
--   With the coordinate presentations and notation just specified, let $g\in\mathbb Z[X,Y]$, $d\in\mathbb Z[X]$, $e=\deg_Yg$, and $\delta=d(\theta)$. Put
--
--   $$m=\lfloor N/\log N\rfloor,\qquad \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad
--   I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2,$$
--
--   $$\Gamma=\{a_1u_1+a_2u_2+a_3\omega:0\le a_1,a_2<s,\ 0\le a_3<q,\ a_i\in\mathbb Z\}.$$
--
--   Auxiliary grid jet-matrix data assert that there is a single nonnegative integer $C$ such that, for each nonnegative integer $K$, there is $A>0$ with the following property for every sufficiently large $N$. There are a nonnegative integer $D$, a polynomial matrix family
--
--   $$R=(R_{v,n,i})_{v\in\Gamma_3,\ 0\le n\le Km,\ i\in I},$$
--
--   and coordinate presentations with the profiles $d_C,b_C$ at every nonlattice point of $\Gamma_3$, satisfying
--
--   $$D\le Am,\qquad |I|(e+1)(D+1)\le e^{AN},\qquad 8(m+1)|\Gamma|\le |I|,$$
--
--   $$\deg_Y R_{v,n,i}<e,\qquad \deg_X([Y^j]R_{v,n,i})\le D\ (j\ge0),\qquad
--   \mathscr L(R_{v,n,i})\le e^{AN}.$$
--
--   Define the ordinary monomials and cleared translates by
--
--   $$f_i(w)=w^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3},\qquad
--   G_{v,i}(w)=(w+v)^{i_0}[2(\wp(v)-\wp(w))]^{3\ell}
--   \wp(w+v)^{i_2}\zeta(w+v)^{i_3}.$$
--
--   Write $Q_{v,a}$ for the denominators in the retained presentation at a nonlattice point, and put
--
--   $$k(n)=(m,5\ell,5\ell,5\ell,J_n,J_n,J_n,J_n),\quad J_n=m+5\ell+n,\qquad
--   \Delta_{v,n}=\prod_{a=0}^7 Q_{v,a}(\theta,\nu)^{k_a(n)}.$$
--
--   The entries retain their exact evaluations in both cases:
--
--   $$R_{v,n,i}(\theta,\nu)=
--   \begin{cases}
--   \delta^{7(m+2\ell+n)}f_i^{(n)}(z_0+v),&v\in\Omega,\\
--   \Delta_{v,n}G_{v,i}^{(n)}(z_0),&v\notin\Omega.
--   \end{cases}$$
--
--   For every point $v\in\Gamma_3$ and every complex coefficient vector $c=(c_i)_{i\in I}$, writing $F_c=\sum_i c_i f_i$, the same matrix family satisfies
--
--   $$\left[\sum_iR_{v,n,i}(\theta,\nu)c_i=0\quad(0\le n\le Km)\right]
--   \Longleftrightarrow
--   \left[F_c^{(n)}(z_0+v)=0\quad(0\le n\le Km)\right].$$
--
--   The matrices and retained presentations precede every coefficient vector. Their degree and length bounds are uniform in the grid point, derivative order, and monomial. Order zero and $K=0$ are included. The dimension gap refers to the smaller grid with $m+1$ equations per point; it does not assert a dimension gap for the whole enlarged derivative family. This interface supplies matrices and their derivative interpretation, while existence and estimates for a nonzero analytic test value remain separate.
-- source:
--   Interfaces for Senthil Kumar K (2026), Section 5 Lemma 7(a)-(b), equations (22)-(28), and the equations and dimension count in the proof of Lemma 8. Coordinatewise denominator exponents are inherited from the formalized clearing construction; these interfaces do not assert the analytic extraction of Lemmas 9-10. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_NonlatticeJetBounds
import Definitions.Def_WeierstrassEllipticZeta_PeriodJetBounds

noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

/-- A quantitative rational presentation of the eight elliptic jet coordinates.
All evaluated denominators are required to be nonzero. -/
structure NonlatticeCoordinatePresentation (L : PeriodPair) (θ ν v z : ℂ)
    (C N s : ℕ) where
  numerator : Fin 8 → MvPolynomial (Fin 2) ℤ
  denominator : Fin 8 → MvPolynomial (Fin 2) ℤ
  lengthBound : Fin 8 → ℕ
  numerator_degree : ∀ a, (numerator a).totalDegree ≤ nonlatticeCoordinateDegree C s a
  denominator_degree : ∀ a, (denominator a).totalDegree ≤ nonlatticeCoordinateDegree C s a
  numerator_length : ∀ a,
    (∑ b ∈ (numerator a).support, ((numerator a).coeff b).natAbs) ≤ lengthBound a
  denominator_length : ∀ a,
    (∑ b ∈ (denominator a).support, ((denominator a).coeff b).natAbs) ≤ lengthBound a
  length_le : ∀ a, (lengthBound a : ℝ) ≤ Real.exp (nonlatticeCoordinateLogBound C N s a)
  denominator_ne_zero : ∀ a,
    MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (denominator a) ≠ 0
  evaluation : ∀ a,
    MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (numerator a) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (denominator a) *
        ellipticJetCoordinates L v z a

/-- The arithmetic-coordinate obligation on the enlarged auxiliary grid. -/
def AuxiliaryNonlatticeCoordinateData (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) : Prop :=
  ∃ C : ℕ, ∀ᶠ N : ℕ in Filter.atTop,
    ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
      v ∉ L.lattice →
        Nonempty (NonlatticeCoordinatePresentation L θ ν v (u₁ / 2) C N (auxiliaryS N))

/-- A family of bounded polynomial jet matrices over the entire enlarged grid.
The rational presentations and exact entry evaluations are retained for analytic
estimates. Matrices and presentations precede every complex coefficient vector. -/
def AuxiliaryGridJetMatrixData (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ)
    (g : ℤ[X][X]) (d : ℤ[X]) : Prop :=
  ∃ C : ℕ, ∀ K : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in Filter.atTop,
    let m := auxiliaryL0 N
    let l := auxiliaryL N
    let s := auxiliaryS N
    let q := auxiliaryS3 N
    let Γ := auxiliaryGrid u₁ u₂ ω ![s, s, q]
    let Γ₃ := auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q]
    let I := Fin (m + 1) × Fin (l + 1) × Fin (l + 1)
    ∃ (D : ℕ) (R : Γ₃ → Fin (K * m + 1) → I → ℤ[X][X])
      (Q : (v : Γ₃) → v.val ∉ L.lattice →
        NonlatticeCoordinatePresentation L θ ν v.val (u₁ / 2) C N s),
      (D : ℝ) ≤ A * m ∧
      (m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 * (g.natDegree + 1) * (D + 1) ≤
        Real.exp (A * N) ∧
      8 * ((m + 1) * Γ.card) ≤ (m + 1) * (l + 1) ^ 2 ∧
      (∀ v n i, (R v n i).natDegree < g.natDegree ∧
        (∀ j, ((R v n i).coeff j).natDegree ≤ D) ∧
        ((∑ j ∈ (R v n i).support, ∑ a ∈ ((R v n i).coeff j).support,
          (((R v n i).coeff j).coeff a).natAbs) : ℝ) ≤ Real.exp (A * N)) ∧
      (∀ v : Γ₃, v.val ∈ L.lattice → ∀ n i,
        (R v n i).eval₂ (Polynomial.aeval θ).toRingHom ν =
          Polynomial.aeval θ d ^ (7 * (m + 2 * l + n)) *
            iteratedDeriv n (fun w => w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
              weierstrassZeta L w ^ i.2.2.val) (u₁ / 2 + v.val)) ∧
      (∀ (v : Γ₃) (hv : v.val ∉ L.lattice) n i,
        (R v n i).eval₂ (Polynomial.aeval θ).toRingHom ν =
          (∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
            ((Q v hv).denominator a) ^ nonlatticeJetWeight m l n a) *
              iteratedDeriv n (clearedAdditionMonomial L v.val l i.1 i.2.1 i.2.2) (u₁ / 2)) ∧
      ∀ (v : Γ₃) (c : I → ℂ),
        ((∀ n, ∑ i, (R v n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i = 0) ↔
          ∀ n ≤ K * m, iteratedDeriv n (fun w =>
            ∑ i, c i * w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
              weierstrassZeta L w ^ i.2.2.val) (u₁ / 2 + v.val) = 0)

end WeierstrassEllipticZeta


