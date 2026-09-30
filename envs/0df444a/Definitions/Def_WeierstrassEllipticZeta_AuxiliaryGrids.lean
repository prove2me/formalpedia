-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
-- name    : WeierstrassEllipticZeta_AuxiliaryGrids
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T10:14:01.521718+00:00
-- url     : https://prove2.me/theorems/e6a74d9b-2e7f-457e-995d-821cc1f9e755
-- title:
--   Integer auxiliary grids and their regular geometric data
-- statement:
--   For $u_1,u_2,\omega\in\mathbb C$, define
--
--   $$
--   v(m)=m_1u_1+m_2u_2+m_3\omega\qquad(m\in\mathbb Z^3),
--   $$
--
--   $$
--   \Gamma(A_1,A_2,A_3)=\{v(m):0\le m_i<A_i\},
--   \qquad \Gamma^+=\Gamma+u_1/2.
--   $$
--
--   The side lengths are natural numbers; a zero side makes the corresponding finite grid empty. The accompanying proposition `RegularAuxiliaryGridData` records injectivity, lattice membership and congruences, regularity of every half-shifted integer point, exact finite-grid cardinalities, and the bound
--
--   $$
--   |z|\le A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2
--   \qquad(z\in\Gamma^+).
--   $$
--
--   It also records periodicity of $\wp,\wp'$ and the integer quasi-period law for the canonical zeta function at regular arguments. These fields are proof obligations, not axioms asserting that the data exist. They provide the geometric input used when constructing auxiliary equations on finite grids.
-- source:
--   Senthil Kumar K (2026), Section 5 definition of Gamma before Lemma 7, the half-shifted function in Lemma 8, and Appendix equation (A.10); the quasi-period law is recalled in the Appendix before (A.4). The proposition bundles explicit consequences and its radius is an elementary triangle-inequality bound. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Data.Fintype.Pi

noncomputable section

namespace WeierstrassEllipticZeta

/-- Integer points in the rank-three group used in the auxiliary construction. -/
def integerGridPoint (u₁ u₂ ω : ℂ) (m : Fin 3 → ℤ) : ℂ :=
  (m 0 : ℂ) * u₁ + (m 1 : ℂ) * u₂ + (m 2 : ℂ) * ω

/-- The source grid with side lengths `A 0`, `A 1`, and `A 2`. -/
def auxiliaryGrid (u₁ u₂ ω : ℂ) (A : Fin 3 → ℕ) : Finset ℂ :=
  Finset.univ.image (fun m : (i : Fin 3) → Fin (A i) ↦
    integerGridPoint u₁ u₂ ω (fun i ↦ (m i : ℕ)))

/-- The regular grid on which the shifted auxiliary function is evaluated. -/
def shiftedAuxiliaryGrid (u₁ u₂ ω : ℂ) (A : Fin 3 → ℕ) : Finset ℂ :=
  (auxiliaryGrid u₁ u₂ ω A).image (fun z ↦ z + u₁ / 2)

/-- Geometric and period-translation data for the grids of Section 5.
The analytic interpolation and zero estimates are separate obligations. -/
structure RegularAuxiliaryGridData (L : PeriodPair) (ω u₁ u₂ : ℂ) : Prop where
  point_injective : Function.Injective (integerGridPoint u₁ u₂ ω)
  lattice_iff : ∀ m : Fin 3 → ℤ,
    integerGridPoint u₁ u₂ ω m ∈ L.lattice ↔ m 0 = 0 ∧ m 1 = 0
  congruent_iff : ∀ m n : Fin 3 → ℤ,
    integerGridPoint u₁ u₂ ω m - integerGridPoint u₁ u₂ ω n ∈ L.lattice ↔
      m 0 = n 0 ∧ m 1 = n 1
  shifted_regular : ∀ m : Fin 3 → ℤ,
    integerGridPoint u₁ u₂ ω m + u₁ / 2 ∉ L.lattice
  card_grid : ∀ A : Fin 3 → ℕ, (auxiliaryGrid u₁ u₂ ω A).card = ∏ i, A i
  card_shifted_grid : ∀ A : Fin 3 → ℕ,
    (shiftedAuxiliaryGrid u₁ u₂ ω A).card = ∏ i, A i
  shifted_grid_regular : ∀ (A : Fin 3 → ℕ) z,
    z ∈ shiftedAuxiliaryGrid u₁ u₂ ω A → z ∉ L.lattice
  shifted_grid_radius : ∀ (A : Fin 3 → ℕ) z,
    z ∈ shiftedAuxiliaryGrid u₁ u₂ ω A →
    ‖z‖ ≤ (A 0 : ℝ) * ‖u₁‖ + (A 1 : ℝ) * ‖u₂‖ +
      (A 2 : ℝ) * ‖ω‖ + ‖u₁‖ / 2
  period_values : ∀ (z : ℂ) (n : ℤ), z ∉ L.lattice →
    L.weierstrassP (z + n * ω) = L.weierstrassP z ∧
    L.derivWeierstrassP (z + n * ω) = L.derivWeierstrassP z ∧
    weierstrassZeta L (z + n * ω) =
      weierstrassZeta L z + n * zetaQuasiPeriod L ω

end WeierstrassEllipticZeta


