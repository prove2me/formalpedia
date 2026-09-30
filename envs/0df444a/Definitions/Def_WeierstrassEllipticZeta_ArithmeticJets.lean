-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ArithmeticJets
-- name    : WeierstrassEllipticZeta_ArithmeticJets
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T11:57:15.681304+00:00
-- url     : https://prove2.me/theorems/2131388f-554e-49b2-bcb7-dcbf94e66c70
-- title:
--   Arithmetic presentations of cleared elliptic derivatives
-- statement:
--   For a period pair $L$, use the prescribed coordinate tuple
--
--   $$
--   J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z))
--   $$
--
--   and the canonical cleared monomial
--
--   $$
--   G_v(z)=(z+v)^{l_0}[2(\wp(v)-\wp(z))]^{3M}
--   \wp(z+v)^{l_2}\zeta(z+v)^{l_3}.
--   $$
--
--   For nonnegative integers $l_0\le L_0$, $l_2,l_3\le M$, and $n$, set
--
--   $$
--   K=L_0+5M+n,\qquad k=(L_0,5M,5M,5M,K,K,K,K).
--   $$
--
--   Arithmetic jet data mean the following universal presentation property. Given eight pairs of integer bivariate polynomials $S_i,Q_i$, each pair having total degree at most $d_i$ and coefficient length at most $H_i$, there exists an integer bivariate polynomial $R$ with
--
--   $$
--   \deg R\le\sum_{i=0}^7 k_i d_i,
--   \qquad \ell(R)\le n!\,2^{41(L_0+M+n)}\prod_{i=0}^7 H_i^{k_i}.
--   $$
--
--   For every evaluation tuple $w\in\mathbb C^2$ and all $v,z,z+v$ outside the lattice, if
--
--   $$
--   S_i(w)=Q_i(w)J_v(z)_i\quad(0\le i<8),
--   $$
--
--   then
--
--   $$
--   R(w)=\left(\prod_{i=0}^7 Q_i(w)^{k_i}\right)G_v^{(n)}(z).
--   $$
--
--   The polynomial $R$ precedes the choices of $w,v,z$. The denominator product depends on $M,L_0,n$ and the $Q_i$, and is shared by all allowed monomial exponents. The fixed elliptic coordinates have exponents $5M$ independent of $L_0,n$. This is a multiplied polynomial identity; zero denominators are allowed, and no hypothesis on $\wp(v)-\wp(z)$ is imposed. Here coefficient length is the sum of absolute values of all integer coefficients.
-- source:
--   Formal interface for the polynomial substitution and denominator clearing in Senthil Kumar K (2026), Section 5 Lemma 7(b), equations (20)-(27). Individual coordinate bounds are used in place of the source block bounds, with harmless fixed factors; this definition alone proves no estimates or grid representations. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials

noncomputable section

namespace WeierstrassEllipticZeta

open MvPolynomial

/-- Integer polynomial presentations of cleared elliptic derivatives, with a
common denominator for all coordinate exponents below `L₀`. The eight coordinate
denominators may differ, preserving the separate fixed and moving estimates. -/
def ArithmeticJetData (L : PeriodPair) : Prop :=
  ∀ (M L₀ l₀ l₂ l₃ n : ℕ), l₀ ≤ L₀ → l₂ ≤ M → l₃ ≤ M →
    let k : Fin 8 → ℕ :=
      ![L₀, 5 * M, 5 * M, 5 * M,
        L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n]
    ∀ (s q : Fin 8 → MvPolynomial (Fin 2) ℤ) (d H : Fin 8 → ℕ),
      (∀ i, (s i).totalDegree ≤ d i) → (∀ i, (q i).totalDegree ≤ d i) →
      (∀ i, (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ H i) →
      (∀ i, (∑ m ∈ (q i).support, ((q i).coeff m).natAbs) ≤ H i) →
      ∃ r : MvPolynomial (Fin 2) ℤ,
        r.totalDegree ≤ ∑ i, k i * d i ∧
        (∑ m ∈ r.support, (r.coeff m).natAbs) ≤
          n.factorial * 2 ^ (41 * (L₀ + M + n)) * ∏ i, H i ^ k i ∧
        ∀ (w : Fin 2 → ℂ) (v z : ℂ),
          v ∉ L.lattice → z ∉ L.lattice → z + v ∉ L.lattice →
          (∀ i, eval₂ (Int.castRingHom ℂ) w (s i) =
            eval₂ (Int.castRingHom ℂ) w (q i) * ellipticJetCoordinates L v z i) →
          eval₂ (Int.castRingHom ℂ) w r =
            (∏ i, eval₂ (Int.castRingHom ℂ) w (q i) ^ k i) *
              iteratedDeriv n (clearedAdditionMonomial L v M l₀ l₂ l₃) z

end WeierstrassEllipticZeta


