-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ClearedEntire
-- name    : WeierstrassEllipticZeta_ClearedEntire
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T14:05:58.509711+00:00
-- url     : https://prove2.me/theorems/ee5c8f21-7ffc-4204-b792-89d42b14b8eb
-- title:
--   Entire cleared translates and their auxiliary-grid derivative bounds
-- statement:
--   Let $L$ be a complex period pair, with lattice $\Omega$ and canonical functions $\zeta,\wp,\wp'$. Supply entire functions $\sigma,S_0,S_1,S_2$ satisfying
--
--   $$S_0=\sigma\zeta,\qquad S_1=\sigma^2\wp,\qquad S_2=\sigma^3\wp'
--   \qquad\text{outside }\Omega.$$
--
--   Let $I$ be any finite index set, let $v\notin\Omega$, and choose complex coefficients $c_i$ and nonnegative integers $\ell_{0i},\ell_{2i},\ell_{3i},D,M$ with
--
--   $$\ell_{0i}\le D,\qquad\ell_{2i},\ell_{3i}\le M.$$
--
--   Define the translated, cleared auxiliary sum
--
--   $$f(z)=\sum_{i\in I}c_i(z+v)^{\ell_{0i}}
--   [2(\wp(v)-\wp(z))]^{3M}\wp(z+v)^{\ell_{2i}}\zeta(z+v)^{\ell_{3i}}.$$
--
--   There exists a single entire function $G$, chosen before any radius or bounds, with
--
--   $$G(z)=\sigma(z)^{15M}f(z)\qquad(z,z+v\notin\Omega).$$
--
--   Put
--
--   $$V_v=1+|\zeta(v)|+|\wp(v)|+|\wp'(v)|,\qquad K_v=36V_v^3.$$
--
--   For every $R\in\mathbb R$ and $B\ge1$, if all four basic entire functions are bounded in absolute value by $B$ on $|z|\le R$, then
--
--   $$|G(z)|\le C_R:=\left(\sum_i|c_i|\right)
--   \max(1,R+|v|)^D K_v^{15M}B^{90M}\qquad(|z|\le R).$$
--
--   The finite set may be empty, coefficients may vanish, and $D=M=0$ is allowed. Neither $\sigma$ nor the addition factor is assumed nonzero. The identity is restricted to regular arguments; the entire extension supplies its own values at poles. This is a conditional version of the construction in Lemma 6(ii), with a coarse explicit growth constant. It does not construct the basic sigma factors or assert the source's sharper displayed numerical bound.
--
--   For fixed $L,\omega,u_1,u_2$, cleared-addition entire data assert the preceding entire-extension and disk-bound property for every choice of the four basic factors, regular shift, finite coefficients, and exponents. The data also assert the following interpolation consequences for the same entire function $G$.
--
--   Let $A=(A_1,A_2,A_3)$ and $T$ be nonnegative integers. Suppose $0<r<R$, $B\ge1$, the four factors are bounded by $B$ on the closed radius-$R$ disk, and
--
--   $$A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2\le r.$$
--
--   Write
--
--   $$\Gamma_A=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:0\le a_i<A_i\}.$$
--
--   Assume $x+v\notin\Omega$ for every $x\in\Gamma_A$, and
--
--   $$f^{(t)}(x)=0\qquad(x\in\Gamma_A,\ 0\le t<T).$$
--
--   Then
--
--   $$|G(z)|\le C_R(2r/R)^{TA_1A_2A_3}\qquad(|z|\le r),$$
--
--   $$|G^{(n)}(z)|\le \frac{n!}{\rho^n}C_R(2r/R)^{TA_1A_2A_3}
--   \qquad(\rho>0,\ |z|+\rho\le r,\ n\ge0).$$
--
--   The entire function precedes all choices of grids, radii and bounds. The data do not provide the four basic factors, establish their nonvanishing or growth, or prove that a test value is nonzero.
-- source:
--   Supporting interface for Senthil Kumar K (2026), Section 4 Lemma 6(ii), equation (16), and equations (14)-(15) applied to the shifted Section 5 grids. The numerical bound is explicitly coarser, and the basic sigma factors remain inputs. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials

noncomputable section

open Filter Metric Set
open scoped Topology

namespace WeierstrassEllipticZeta

/-- Translated auxiliary polynomial multiplied by the common addition factor. -/
def clearedAuxiliarySum (L : PeriodPair) {ι : Type} [Fintype ι] (v : ℂ)
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (M : ℕ) (z : ℂ) : ℂ :=
  ∑ i, c i * clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) z

/-- A coarse explicit bound, retaining the quadratic exponential growth scale
when the basic entire factors have bounds exponential in the squared radius. -/
def clearedAuxiliaryBound (L : PeriodPair) {ι : Type} [Fintype ι] (v : ℂ)
    (c : ι → ℂ) (D M : ℕ) (R B : ℝ) : ℝ :=
  (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D *
    (36 * (1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ +
      ‖L.derivWeierstrassP v‖) ^ 3) ^ (15 * M) * B ^ (90 * M)

/-- Entire extensions and grid estimates for the actual cleared translates.
Basic entire factors and their bounds are supplied as inputs. -/
def ClearedAdditionEntireData (L : PeriodPair) (ω u₁ u₂ : ℂ) : Prop :=
  ∀ (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ),
    AnalyticOnNhd ℂ σ univ → (∀ j, AnalyticOnNhd ℂ (S j) univ) →
    (∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = σ z ^ (j.val + 1) * ellipticPoleCoordinates L z j) →
    ∀ {ι : Type} [Fintype ι] (v : ℂ), v ∉ L.lattice →
    ∀ (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (D M : ℕ),
      (∀ i, l₀ i ≤ D) → (∀ i, l₂ i ≤ M) → (∀ i, l₃ i ≤ M) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
        G z = σ z ^ (15 * M) * clearedAuxiliarySum L v c l₀ l₂ l₃ M z) ∧
      (∀ R B : ℝ, 1 ≤ B →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖S j z‖ ≤ B) →
        ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ clearedAuxiliaryBound L v c D M R B) ∧
      ∀ (A : Fin 3 → ℕ) (T : ℕ) (r R B : ℝ),
        0 < r → r < R → 1 ≤ B →
        (A 0 : ℝ) * ‖u₁‖ + (A 1 : ℝ) * ‖u₂‖ +
          (A 2 : ℝ) * ‖ω‖ + ‖u₁‖ / 2 ≤ r →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖S j z‖ ≤ B) →
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A, x + v ∉ L.lattice) →
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A, ∀ t < T,
          iteratedDeriv t (clearedAuxiliarySum L v c l₀ l₂ l₃ M) x = 0) →
        (∀ z : ℂ, ‖z‖ ≤ r → ‖G z‖ ≤ clearedAuxiliaryBound L v c D M R B *
          (2 * r / R) ^ (T * ∏ i, A i)) ∧
        ∀ (z : ℂ) (ρ : ℝ), 0 < ρ → ‖z‖ + ρ ≤ r → ∀ n : ℕ,
          ‖iteratedDeriv n G z‖ ≤ n.factorial *
            (clearedAuxiliaryBound L v c D M R B *
              (2 * r / R) ^ (T * ∏ i, A i)) / ρ ^ n

end WeierstrassEllipticZeta


