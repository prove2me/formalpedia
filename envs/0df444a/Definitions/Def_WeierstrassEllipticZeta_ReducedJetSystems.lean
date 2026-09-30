-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems
-- name    : WeierstrassEllipticZeta_ReducedJetSystems
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T12:48:10.094208+00:00
-- url     : https://prove2.me/theorems/1e6c8585-4e48-413a-b082-e1fb4113df09
-- title:
--   Reduced polynomial matrices for finite elliptic derivative equations
-- statement:
--   Fix a period pair $L$, complex numbers $\theta,\nu$, and $g\in\mathbb Z[X][Y]$. For a polynomial, $\ell$ denotes the sum of the absolute values of all integer coefficients.
--
--   Reduced arithmetic jet-system data mean that there exist positive integers $B,H$ with the following property. For any nonnegative $M,L_0,T$, let
--
--   $$
--   I=\{0,\ldots,L_0\}\times\{0,\ldots,M\}^2,\qquad
--   k(n)=(L_0,5M,5M,5M,K_n,K_n,K_n,K_n),\quad K_n=L_0+5M+n.
--   $$
--
--   Choose eight numerator and denominator polynomials $S_a,Q_a\in\mathbb Z[X,Y]$, whose total degrees are at most $d_a$ and lengths at most $h_a$, respectively. There exists a matrix
--
--   $$
--   R=(R_{n,i})_{\substack{0\le n<T\\i\in I}}
--   $$
--
--   of integer bivariate polynomials. Writing $D_n=\sum_{a=0}^7 k_a(n)d_a$, every entry satisfies
--
--   $$
--   \deg_Y R_{n,i}<\deg_Yg,\qquad
--   \deg_X[Y^j]R_{n,i}\le BD_n\quad(j\ge0),
--   $$
--
--   $$
--   \ell(R_{n,i})\le
--   n!\,2^{41(L_0+M+n)}\left(\prod_{a=0}^7h_a^{k_a(n)}\right)H^{D_n+1}.
--   $$
--
--   This matrix precedes the following points and coefficient vectors. For any $v,z,z+v$ outside the lattice, suppose the coordinate presentations satisfy
--
--   $$
--   S_a(\theta,\nu)=Q_a(\theta,\nu)J_v(z)_a,
--   $$
--
--   where
--
--   $$
--   J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)).
--   $$
--
--   For $i=(i_0,i_2,i_3)$, set
--
--   $$
--   G_i(w)=(w+v)^{i_0}[2(\wp(v)-\wp(w))]^{3M}
--          \wp(w+v)^{i_2}\zeta(w+v)^{i_3},\qquad
--   \Delta_n=\prod_{a=0}^7Q_a(\theta,\nu)^{k_a(n)}.
--   $$
--
--   The exact entry evaluations are
--
--   $$
--   R_{n,i}(\theta,\nu)=\Delta_nG_i^{(n)}(z).
--   $$
--
--   If additionally $z-v$ is regular and all eight evaluated denominators are nonzero, then for every complex vector $c=(c_i)_{i\in I}$,
--
--   $$
--   \left(\forall\,0\le n<T,\ \sum_iR_{n,i}(\theta,\nu)c_i=0\right)
--   \ \Longleftrightarrow\
--   \left(\forall\,0\le n<T,\ F_c^{(n)}(z+v)=0\right),
--   $$
--
--   where
--
--   $$
--   F_c(w)=\sum_{i\in I}c_iw^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}.
--   $$
--
--   The exact evaluation identities also hold with zero coordinate denominators; nonzero denominators are required only for kernel equivalence. Constants are uniform in all cutoffs, orders, and presentations. The property assembles bounded reduced derivative presentations into finite linear equations. It does not produce grid-coordinate presentations, prove that their denominators are nonzero, choose asymptotic parameters, or establish a small nonzero test value.
-- source:
--   Formal interface for the reduced arithmetic entries of Section 5 Lemma 7(b) and the finite linear equations in the proof of Lemma 8, equation (29), Senthil Kumar K (2026). This definition records bounds, entry identities, and the kernel equivalence; it contains no proof of these properties. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_ReducedArithmeticJets

noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

/-- Uniform reduced polynomial matrices for finite families of cleared derivatives,
together with the equivalence between their evaluated kernels and vanishing jets. -/
def ReducedArithmeticJetSystemData (L : PeriodPair) (θ ν : ℂ) (g : ℤ[X][X]) : Prop :=
  ∃ B H : ℕ, 0 < B ∧ 0 < H ∧
    ∀ (M L₀ T : ℕ),
      let I := Fin (L₀ + 1) × Fin (M + 1) × Fin (M + 1)
      let k : ℕ → Fin 8 → ℕ := fun n =>
        ![L₀, 5 * M, 5 * M, 5 * M,
          L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n]
      ∀ (s q : Fin 8 → MvPolynomial (Fin 2) ℤ) (d h : Fin 8 → ℕ),
        (∀ i, (s i).totalDegree ≤ d i) → (∀ i, (q i).totalDegree ≤ d i) →
        (∀ i, (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ h i) →
        (∀ i, (∑ m ∈ (q i).support, ((q i).coeff m).natAbs) ≤ h i) →
        ∃ R : Fin T → I → ℤ[X][X],
          (∀ n i, (R n i).natDegree < g.natDegree ∧
            (∀ j, ((R n i).coeff j).natDegree ≤ B * ∑ a, k n a * d a) ∧
            (∑ j ∈ (R n i).support, ∑ a ∈ ((R n i).coeff j).support,
              (((R n i).coeff j).coeff a).natAbs) ≤
                (n.val.factorial * 2 ^ (41 * (L₀ + M + n)) * ∏ a, h a ^ k n a) *
                  H ^ ((∑ a, k n a * d a) + 1)) ∧
          ∀ (v z : ℂ), v ∉ L.lattice → z ∉ L.lattice → z + v ∉ L.lattice →
            (∀ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (s a) =
              MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q a) *
                ellipticJetCoordinates L v z a) →
            (∀ n i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν =
              (∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q a) ^ k n a) *
                iteratedDeriv n (clearedAdditionMonomial L v M i.1 i.2.1 i.2.2) z) ∧
            (z - v ∉ L.lattice →
              (∀ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q a) ≠ 0) →
              ∀ c : I → ℂ,
                (∀ n, ∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i = 0) ↔
                  ∀ n < T, iteratedDeriv n (fun w =>
                    ∑ i, c i * w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
                      weierstrassZeta L w ^ i.2.2.val) (z + v) = 0)

end WeierstrassEllipticZeta


