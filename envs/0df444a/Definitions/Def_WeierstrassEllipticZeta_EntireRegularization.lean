-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
-- name    : WeierstrassEllipticZeta_EntireRegularization
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T13:36:42.937753+00:00
-- url     : https://prove2.me/theorems/f653976c-b094-4b99-ab87-dee18ab7890b
-- title:
--   Entire elliptic auxiliary sums and their grid estimates
-- statement:
--   Fix a period pair $L$ and complex numbers $\omega,u_1,u_2$. Write
--
--   $$\Phi_0=\zeta_L,\qquad\Phi_1=\wp_L,\qquad\Phi_2=\wp'_L.$$
--
--   Elliptic regularization data mean the following property. Supply entire functions $\sigma,S_0,S_1,S_2$ satisfying
--
--   $$S_j(z)=\sigma(z)^{j+1}\Phi_j(z)\qquad(z\notin L,\ 0\le j\le2).$$
--
--   For any finite index set $I$, complex shift $v$, complex coefficients $c_i$, and nonnegative integers $\ell_i,e_{ij},D,K$ with
--
--   $$\ell_i\le D,\qquad e_{i0}+2e_{i1}+3e_{i2}\le K,$$
--
--   put
--
--   $$f(z)=\sum_i c_i(z+v)^{\ell_i}\prod_{j=0}^2\Phi_j(z)^{e_{ij}}.$$
--
--   There is an entire function $G$, chosen independently of the radius, grid, and bounds, with $G=\sigma^Kf$ outside the lattice. If $B\ge1$ bounds the absolute values of $\sigma,S_0,S_1,S_2$ throughout $|z|\le R$, define
--
--   $$C_R=\left(\sum_i|c_i|\right)\max(1,R+|v|)^D B^K.$$
--
--   Then $|G(z)|\le C_R$ on $|z|\le R$. Moreover, choose nonnegative integers $A_1,A_2,A_3,T$ and radii $0<r<R$ such that
--
--   $$A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2\le r.$$
--
--   Suppose all derivatives of $f$ below order $T$ vanish on
--
--   $$\{a_1u_1+a_2u_2+a_3\omega+u_1/2:0\le a_i<A_i\}.$$
--
--   Then, with $Q=TA_1A_2A_3$,
--
--   $$|G(z)|\le C_R(2r/R)^Q\qquad(|z|\le r),$$
--
--   $$|G^{(n)}(z)|\le \frac{n!}{\rho^n}C_R(2r/R)^Q
--   \qquad(\rho>0,\ |z|+\rho\le r,\ n\ge0).$$
--
--   The definition supplies the analytic extension and its interpolation consequences conditional on the four entire factors and their bounds. It does not assert existence of those factors or an order-two growth bound for them. At lattice points the entire extension need not equal the product formed from totalized meromorphic values.
-- source:
--   Supporting interface for Senthil Kumar K (2026), Section 4 Lemma 6(i)-(ii), equation (16), and the use of equations (14)-(15) on the shifted Section 5 grid. Pole weights are 1,2,3; sigma factors and their bounds remain explicit inputs. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_GridInterpolation

noncomputable section

open Filter Metric Set
open scoped Topology

namespace WeierstrassEllipticZeta

/-- The moving meromorphic coordinates, in increasing order of pole weight. -/
def ellipticPoleCoordinates (L : PeriodPair) (z : ℂ) : Fin 3 → ℂ :=
  ![weierstrassZeta L z, L.weierstrassP z, L.derivWeierstrassP z]

/-- Finite auxiliary sums allowing both the original and cleared-addition terms. -/
def ellipticRegularizationSum (L : PeriodPair) {ι : Type} [Fintype ι]
    (v : ℂ) (c : ι → ℂ) (l : ι → ℕ) (e : ι → Fin 3 → ℕ) (z : ℂ) : ℂ :=
  ∑ i, c i * (z + v) ^ l i * ∏ j, ellipticPoleCoordinates L z j ^ e i j

/-- Entire extension, growth, and grid interpolation after supplying the basic
entire sigma factors. Their existence and growth are separate obligations. -/
def EllipticRegularizationData (L : PeriodPair) (ω u₁ u₂ : ℂ) : Prop :=
  ∀ (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ),
    AnalyticOnNhd ℂ σ univ →
    (∀ j, AnalyticOnNhd ℂ (S j) univ) →
    (∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = σ z ^ (j.val + 1) * ellipticPoleCoordinates L z j) →
    ∀ {ι : Type} [Fintype ι] (v : ℂ) (c : ι → ℂ) (l : ι → ℕ)
      (e : ι → Fin 3 → ℕ) (D K : ℕ),
    (∀ i, l i ≤ D) →
    (∀ i, e i 0 + 2 * e i 1 + 3 * e i 2 ≤ K) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z : ℂ, z ∉ L.lattice →
        G z = σ z ^ K * ellipticRegularizationSum L v c l e z) ∧
      (∀ R B : ℝ, 1 ≤ B →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖S j z‖ ≤ B) →
        ∀ z : ℂ, ‖z‖ ≤ R →
          ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D * B ^ K) ∧
      ∀ (A : Fin 3 → ℕ) (T : ℕ) (r R B : ℝ),
        0 < r → r < R → 1 ≤ B →
        (A 0 : ℝ) * ‖u₁‖ + (A 1 : ℝ) * ‖u₂‖ +
          (A 2 : ℝ) * ‖ω‖ + ‖u₁‖ / 2 ≤ r →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖S j z‖ ≤ B) →
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A, ∀ t < T,
          iteratedDeriv t (ellipticRegularizationSum L v c l e) x = 0) →
        (∀ z : ℂ, ‖z‖ ≤ r →
          ‖G z‖ ≤ ((∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D * B ^ K) *
            (2 * r / R) ^ (T * ∏ i, A i)) ∧
        ∀ (z : ℂ) (ρ : ℝ), 0 < ρ → ‖z‖ + ρ ≤ r → ∀ n : ℕ,
          ‖iteratedDeriv n G z‖ ≤ n.factorial *
            (((∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D * B ^ K) *
              (2 * r / R) ^ (T * ∏ i, A i)) / ρ ^ n

end WeierstrassEllipticZeta


