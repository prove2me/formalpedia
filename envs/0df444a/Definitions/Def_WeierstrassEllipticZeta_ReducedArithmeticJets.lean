-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ReducedArithmeticJets
-- name    : WeierstrassEllipticZeta_ReducedArithmeticJets
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T12:25:59.732427+00:00
-- url     : https://prove2.me/theorems/1b60b777-b727-4f83-ae1b-9c29e28b4a59
-- title:
--   Reduced arithmetic presentations of cleared elliptic derivatives
-- statement:
--   Fix a period pair $L$, complex numbers $\theta,\nu$, and an integer bivariate relation $g$. Write
--
--   $$
--   J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)),
--   $$
--
--   $$
--   G_v(z)=(z+v)^{l_0}[2(\wp(v)-\wp(z))]^{3M}\wp(z+v)^{l_2}\zeta(z+v)^{l_3}.
--   $$
--
--   Reduced arithmetic jet data mean that there exist positive integers $B,H$, uniform in all the following choices. For nonnegative integers $l_0\le L_0$, $l_2,l_3\le M$, and $n$, put
--
--   $$
--   K=L_0+5M+n,\qquad k=(L_0,5M,5M,5M,K,K,K,K).
--   $$
--
--   Given eight pairs of integer bivariate polynomials $S_i,Q_i$ with total degrees at most $d_i$ and coefficient lengths at most $h_i$, put
--
--   $$
--   D=\sum_{i=0}^7 k_i d_i,\qquad T=n!\,2^{41(L_0+M+n)}\prod_{i=0}^7 h_i^{k_i}.
--   $$
--
--   There exists $R\in\mathbb Z[X][Y]$ with
--
--   $$
--   \deg_Y R<\deg_Y g,\qquad \deg_X[Y^j]R\le BD\quad(j\ge0),\qquad \ell(R)\le T H^{D+1}.
--   $$
--
--   For every $v,z,z+v$ outside the lattice, if
--
--   $$
--   S_i(\theta,\nu)=Q_i(\theta,\nu)J_v(z)_i\quad(0\le i<8),
--   $$
--
--   then
--
--   $$
--   R(\theta,\nu)=\left(\prod_{i=0}^7Q_i(\theta,\nu)^{k_i}\right)G_v^{(n)}(z).
--   $$
--
--   Here $\ell$ sums the absolute values of all integer coefficients. The representative precedes the regular points $v,z$. Its $Y$-degree is bounded independently of the derivative order and monomial cutoffs. The denominator product is shared by all monomials under the same cutoffs. The identity allows zero coordinate denominators and imposes no nonvanishing condition on an elliptic-value difference. This property supplies reduced presentations once coordinate presentations are given; it does not itself provide those inputs or their nonvanishing.
-- source:
--   Formal interface combining the bounded reduction in Senthil Kumar K (2026), Section 3 Lemma 1, with the arithmetic derivative presentations of Section 5 Lemma 7(b), equations (20)-(27). This definition records the resulting presentation property and proves no estimates. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Mathlib.Algebra.Polynomial.AlgebraMap

noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

/-- Bounded presentations of cleared elliptic derivatives in the fixed power
basis of an algebraic generator, with constants uniform in the derivative order,
monomial cutoffs, and coordinate presentations. -/
def ReducedArithmeticJetData (L : PeriodPair) (θ ν : ℂ) (g : ℤ[X][X]) : Prop :=
  ∃ B H : ℕ, 0 < B ∧ 0 < H ∧
    ∀ (M L₀ l₀ l₂ l₃ n : ℕ), l₀ ≤ L₀ → l₂ ≤ M → l₃ ≤ M →
      let k : Fin 8 → ℕ :=
        ![L₀, 5 * M, 5 * M, 5 * M,
          L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n]
      ∀ (s q : Fin 8 → MvPolynomial (Fin 2) ℤ) (d h : Fin 8 → ℕ),
        (∀ i, (s i).totalDegree ≤ d i) → (∀ i, (q i).totalDegree ≤ d i) →
        (∀ i, (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ h i) →
        (∀ i, (∑ m ∈ (q i).support, ((q i).coeff m).natAbs) ≤ h i) →
        ∃ r : ℤ[X][X],
          r.natDegree < g.natDegree ∧
          (∀ j, (r.coeff j).natDegree ≤ B * ∑ i, k i * d i) ∧
          (∑ j ∈ r.support, ∑ a ∈ (r.coeff j).support,
            ((r.coeff j).coeff a).natAbs) ≤
              (n.factorial * 2 ^ (41 * (L₀ + M + n)) * ∏ i, h i ^ k i) *
                H ^ ((∑ i, k i * d i) + 1) ∧
          ∀ (v z : ℂ), v ∉ L.lattice → z ∉ L.lattice → z + v ∉ L.lattice →
            (∀ i, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (s i) =
              MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q i) *
                ellipticJetCoordinates L v z i) →
            r.eval₂ (Polynomial.aeval θ).toRingHom ν =
              (∏ i, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q i) ^ k i) *
                iteratedDeriv n (clearedAdditionMonomial L v M l₀ l₂ l₃) z

end WeierstrassEllipticZeta


