-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_PeriodJetBounds
-- name    : WeierstrassEllipticZeta_PeriodJetBounds
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T15:55:43.661137+00:00
-- url     : https://prove2.me/theorems/bc4158fe-dd6e-4de8-82a1-2ef4f72c28ac
-- title:
--   Bounded derivative matrices at auxiliary period translates
-- statement:
--   Fix a complex period pair $L$, complex numbers $\omega,z,\theta,\nu$, and polynomials $g\in\mathbb Z[X,Y]$, $d\in\mathbb Z[X]$. Write $e=\deg_Yg$, $\delta=d(\theta)$, and let $\mathscr L(P)$ be the sum of the absolute values of all integer coefficients of $P$.
--
--   For sufficiently large positive integers $N$, use the auxiliary parameters
--
--   $$m=\lfloor N/\log N\rfloor,\qquad
--   \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad
--   q=\lfloor N^{5/8}\log N/64\rfloor,\qquad
--   I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2.$$
--
--   Bounded auxiliary period-jet data mean the following property. For every fixed nonnegative integer $K$, there is a real constant $A>0$ such that, for all sufficiently large $N$, one can choose a nonnegative integer $D$ with
--
--   $$D\le Am,\qquad (m+1)(\ell+1)^2(e+1)(D+1)\le e^{AN}.$$
--
--   This same degree bound works for every integer $a$ satisfying $|a|\le3q$. For each such $a$, there is a matrix
--
--   $$R=(R_{n,i})_{0\le n\le Km,\ i\in I}\quad\text{over }\mathbb Z[X,Y]$$
--
--   such that, for every entry and every nonnegative $j$,
--
--   $$\deg_YR_{n,i}<e,\qquad \deg_X([Y^j]R_{n,i})\le D,\qquad
--   \mathscr L(R_{n,i})\le e^{AN}.$$
--
--   Writing $J_n=m+2\ell+n$, the exact evaluations are
--
--   $$R_{n,i}(\theta,\nu)=\delta^{7J_n}
--   \left.\frac{d^n}{dw^n}\big(w^{i_0}\wp_L(w)^{i_2}\zeta_L(w)^{i_3}\big)
--   \right|_{w=z+a\omega}.$$
--
--   Moreover, for every complex coefficient vector $c=(c_i)_{i\in I}$, set
--
--   $$F_c(w)=\sum_{i\in I}c_iw^{i_0}\wp_L(w)^{i_2}\zeta_L(w)^{i_3}.$$
--
--   The same matrix satisfies
--
--   $$\left[\sum_iR_{n,i}(\theta,\nu)c_i=0\quad(0\le n\le Km)\right]
--   \quad\Longleftrightarrow\quad
--   \left[F_c^{(n)}(z+a\omega)=0\quad(0\le n\le Km)\right].$$
--
--   The constant and threshold precede the period index, the matrix precedes the vector, and $D$ is common to all period indices. The length bound also bounds each individual integer coefficient. Order zero, $K=0$, and both signs of $a$ are included. The padded denominator exponent is inherited from the earlier period-jet construction; it is coarser than the source's exponent in (28). These data do not assert a nonzero derivative or any estimates at nonlattice translates.
-- source:
--   Conditional matrix interface for Senthil Kumar K (2026), Section 5 equation (28), its following degree/type estimates, and the period case of Lemma 10. The dimension envelope and padded denominator are explicit formalization choices. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_PeriodJets
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters

noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

/-- Uniform degree, coefficient-length and dimension bounds for the actual
period-translation derivative matrices at the auxiliary parameters. -/
def BoundedAuxiliaryPeriodJetData (L : PeriodPair) (ω z θ ν : ℂ)
    (g : ℤ[X][X]) (d : ℤ[X]) : Prop :=
  ∀ K : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in Filter.atTop,
    let m := auxiliaryL0 N
    let l := auxiliaryL N
    let I := Fin (m + 1) × Fin (l + 1) × Fin (l + 1)
    ∃ D : ℕ, (D : ℝ) ≤ A * m ∧
      ((m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 * (g.natDegree + 1) * (D + 1)) ≤
        Real.exp (A * N) ∧
      ∀ a : ℤ, a.natAbs ≤ 3 * auxiliaryS3 N →
        ∃ R : Fin (K * m + 1) → I → ℤ[X][X],
          (∀ n i, (R n i).natDegree < g.natDegree ∧
            (∀ j, ((R n i).coeff j).natDegree ≤ D) ∧
            ((∑ j ∈ (R n i).support, ∑ k ∈ ((R n i).coeff j).support,
              (((R n i).coeff j).coeff k).natAbs) : ℝ) ≤ Real.exp (A * N)) ∧
          (∀ n i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν =
            Polynomial.aeval θ d ^ (7 * (m + 2 * l + n)) *
              iteratedDeriv n (fun w => w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
                weierstrassZeta L w ^ i.2.2.val) (z + a * ω)) ∧
          ∀ c : I → ℂ,
            ((∀ n, ∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i = 0) ↔
              ∀ n ≤ K * m, iteratedDeriv n (fun w =>
                ∑ i, c i * w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
                  weierstrassZeta L w ^ i.2.2.val) (z + a * ω) = 0)

end WeierstrassEllipticZeta


