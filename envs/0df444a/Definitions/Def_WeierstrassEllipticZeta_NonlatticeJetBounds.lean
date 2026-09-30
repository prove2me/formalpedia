-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_NonlatticeJetBounds
-- name    : WeierstrassEllipticZeta_NonlatticeJetBounds
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T16:18:09.847296+00:00
-- url     : https://prove2.me/theorems/539a621a-4294-4ea2-8691-85caccdc394c
-- title:
--   Conditional uniform bounds for auxiliary nonlattice derivative matrices
-- statement:
--   Fix a complex period pair $L$, complex numbers $\theta,\nu$, and $g\in\mathbb Z[X,Y]$. Write $e=\deg_Yg$ and let $\mathscr L(P)$ denote the sum of the absolute values of all integer coefficients of $P$.
--
--   For all sufficiently large positive integers $N$, put
--
--   $$m=\lfloor N/\log N\rfloor,\qquad
--   \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad s=\lfloor N^{3/16}\rfloor,\qquad
--   I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2.$$
--
--   For nonnegative integers $K,C$, define the eight coordinate degree and logarithmic length bounds
--
--   $$d=(C,Cs^2,Cs^2,Cs^2,C,C,C,C),$$
--
--   $$b=(C\log N,C(s^2+\log N),C(s^2+\log N),C(s^2+\log N),C,C,C,C).$$
--
--   The derivative weights are
--
--   $$k(n)=(m,5\ell,5\ell,5\ell,J_n,J_n,J_n,J_n),\qquad J_n=m+5\ell+n.$$
--
--   Bounded auxiliary nonlattice jet data assert that, for every $K,C$, there is $A>0$ such that, for all sufficiently large $N$, one can choose a nonnegative integer $D$ satisfying
--
--   $$D\le Am,\qquad (m+1)(\ell+1)^2(e+1)(D+1)\le e^{AN}.$$
--
--   This degree bound is chosen before the following coordinate presentations. Choose eight numerator and denominator polynomials $P_a,Q_a\in\mathbb Z[X,Y]$ and nonnegative integer length bounds $h_a$ such that
--
--   $$\deg P_a,\deg Q_a\le d_a,\qquad
--   \mathscr L(P_a),\mathscr L(Q_a)\le h_a\le e^{b_a}\qquad(0\le a<8).$$
--
--   There is a polynomial matrix
--
--   $$R=(R_{n,i})_{0\le n\le Km,\ i\in I}$$
--
--   with
--
--   $$\deg_Y R_{n,i}<e,\qquad
--   \deg_X([Y^j]R_{n,i})\le D\quad(j\ge0),\qquad
--   \mathscr L(R_{n,i})\le e^{AN}.$$
--
--   The matrix is chosen before any complex evaluation points $v,z$. Suppose $v,z,z+v$ lie outside the period lattice and
--
--   $$P_a(\theta,\nu)=Q_a(\theta,\nu)\mathcal J_v(z)_a,$$
--
--   $$\mathcal J_v(z)=(z+v,\zeta_L(v),\wp_L(v),\wp'_L(v),
--   \zeta_L(z),\wp_L(z),\wp'_L(z),\wp''_L(z)).$$
--
--   Put
--
--   $$G_i(w)=(w+v)^{i_0}[2(\wp_L(v)-\wp_L(w))]^{3\ell}
--   \wp_L(w+v)^{i_2}\zeta_L(w+v)^{i_3},\qquad
--   \Delta_n=\prod_{a=0}^7Q_a(\theta,\nu)^{k_a(n)}.$$
--
--   Then the exact entry evaluations are
--
--   $$R_{n,i}(\theta,\nu)=\Delta_nG_i^{(n)}(z).$$
--
--   If in addition $z-v$ lies outside the lattice and every $Q_a(\theta,\nu)$ is nonzero, then, for every complex vector $c=(c_i)_{i\in I}$, writing
--
--   $$F_c(w)=\sum_{i\in I}c_iw^{i_0}\wp_L(w)^{i_2}\zeta_L(w)^{i_3},$$
--
--   the same matrix satisfies
--
--   $$\left[\sum_i R_{n,i}(\theta,\nu)c_i=0\quad(0\le n\le Km)\right]
--   \quad\Longleftrightarrow\quad
--   \left[F_c^{(n)}(z+v)=0\quad(0\le n\le Km)\right].$$
--
--   The constant and threshold precede all coordinate polynomials; $D$ is common to every presentation and derivative order. The matrix precedes the points and vectors. Both $K=0$ and $C=0$ are allowed. Zero denominators are permitted for the exact evaluation identity, and nonzero evaluated denominators are explicit hypotheses of the kernel equivalence. This is a conditional bound for nonlattice derivative matrices: existence of coordinate presentations satisfying the profiles, their denominator nonvanishing, and a nonzero test derivative are separate obligations.
-- source:
--   Coordinate profiles and conditional matrix interface for Senthil Kumar K (2026), Section 5 Lemma 7(b), equations (22)-(27) and their following estimates. Separate denominator powers are inherited from the coordinatewise clearing construction. Coordinate existence and nonvanishing are not part of this interface. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters

noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

/-- Coordinatewise exponents used to clear the denominators of a derivative. -/
def nonlatticeJetWeight (m l n : ℕ) : Fin 8 → ℕ :=
  ![m, 5 * l, 5 * l, 5 * l, m + 5 * l + n, m + 5 * l + n,
    m + 5 * l + n, m + 5 * l + n]

/-- Degree bounds distinguish the moving elliptic coordinates from the base point. -/
def nonlatticeCoordinateDegree (C s : ℕ) : Fin 8 → ℕ :=
  ![C, C * s ^ 2, C * s ^ 2, C * s ^ 2, C, C, C, C]

/-- Logarithmic length bounds for the ordinary, moving, and fixed coordinates. -/
def nonlatticeCoordinateLogBound (C N s : ℕ) : Fin 8 → ℝ :=
  ![C * Real.log N, C * ((s : ℝ) ^ 2 + Real.log N),
    C * ((s : ℝ) ^ 2 + Real.log N), C * ((s : ℝ) ^ 2 + Real.log N), C, C, C, C]

/-- Uniform matrix estimates conditional on the indicated rational-coordinate
profiles. The matrices are chosen before evaluation points or coefficient vectors. -/
def BoundedAuxiliaryNonlatticeJetData (L : PeriodPair) (θ ν : ℂ)
    (g : ℤ[X][X]) : Prop :=
  ∀ K C : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in Filter.atTop,
    let m := auxiliaryL0 N
    let l := auxiliaryL N
    let s := auxiliaryS N
    let I := Fin (m + 1) × Fin (l + 1) × Fin (l + 1)
    ∃ D : ℕ, (D : ℝ) ≤ A * m ∧
      (m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 * (g.natDegree + 1) * (D + 1) ≤
        Real.exp (A * N) ∧
      ∀ (p q : Fin 8 → MvPolynomial (Fin 2) ℤ) (h : Fin 8 → ℕ),
        (∀ a, (p a).totalDegree ≤ nonlatticeCoordinateDegree C s a) →
        (∀ a, (q a).totalDegree ≤ nonlatticeCoordinateDegree C s a) →
        (∀ a, (∑ b ∈ (p a).support, ((p a).coeff b).natAbs) ≤ h a) →
        (∀ a, (∑ b ∈ (q a).support, ((q a).coeff b).natAbs) ≤ h a) →
        (∀ a, (h a : ℝ) ≤ Real.exp (nonlatticeCoordinateLogBound C N s a)) →
        ∃ R : Fin (K * m + 1) → I → ℤ[X][X],
          (∀ n i, (R n i).natDegree < g.natDegree ∧
            (∀ j, ((R n i).coeff j).natDegree ≤ D) ∧
            ((∑ j ∈ (R n i).support, ∑ a ∈ ((R n i).coeff j).support,
              (((R n i).coeff j).coeff a).natAbs) : ℝ) ≤ Real.exp (A * N)) ∧
          ∀ v z : ℂ, v ∉ L.lattice → z ∉ L.lattice → z + v ∉ L.lattice →
            (∀ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (p a) =
              MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q a) *
                ellipticJetCoordinates L v z a) →
            (∀ n i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν =
              (∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q a) ^
                nonlatticeJetWeight m l n a) *
                  iteratedDeriv n (clearedAdditionMonomial L v l i.1 i.2.1 i.2.2) z) ∧
            (z - v ∉ L.lattice →
              (∀ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q a) ≠ 0) →
              ∀ c : I → ℂ,
                ((∀ n, ∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i = 0) ↔
                  ∀ n ≤ K * m, iteratedDeriv n (fun w =>
                    ∑ i, c i * w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
                      weierstrassZeta L w ^ i.2.2.val) (z + v) = 0))

end WeierstrassEllipticZeta


