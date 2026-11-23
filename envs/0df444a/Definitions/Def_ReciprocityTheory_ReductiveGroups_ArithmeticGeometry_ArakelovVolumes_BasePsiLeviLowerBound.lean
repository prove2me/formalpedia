-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_BasePsiLeviLowerBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_BasePsiLeviLowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:17.423488+00:00
-- url     : https://prove2.me/theorems/6e794e13-1bcd-42f0-b3c1-bd717afee052
-- title:
--   Base Psi Levi Lower Bound
-- statement:
--   Definitions and structural lemmas for Base Psi Levi Lower Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/BasePsiLeviLowerBound.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_FirstMinimumPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR
open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
structure ArchIn {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (C : Cusp A) where
  L : La
  de : La
  Fp : La
  T : ℕ
  i : ℕ
  g0 : ℕ
  N : ℕ
  c : ℝ
  c1 : ℝ
  a1 : ℝ
  r : ℝ
  n_ge : 2 ≤ n
  T_ge : 11 * n ^ 2 ≤ T
  i_pos : 1 ≤ i
  genus_pos : 1 ≤ g0
  c_pos : 0 < c
  frame_theta_const_pos : 0 < c1
  frame_theta_weight_pos : 0 < a1
  r_nonneg : 0 ≤ r
  Tcg0 : (T : ℝ) * c * g0 ≤ 1
  r_le : r * (1 + c1 / a1) ≤ 2 * T

  w : Fin N → ι → Y → ℂ
  w_sec : ∀ k, A.IsSec L (w k)
  w_bdd : ∀ k, Bdd A L (w k)
  w_van : ∀ k, C.van L 0 (w k)
  w_nz : ∀ y, ∃ k, w k (A.pick y) y ≠ 0

  ph : Y → ℝ
  ph_nonneg : ∀ y, 0 ≤ ph y
  p1 : ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ y, C.la1 y < ε0 → ca / C.la1 y ^ 2 ≤ ph y
  p2 : ∀ y, (T : ℝ) * c * ph y ≤ c1 / C.la1 y ^ 2
  p3 : ∃ K : ℝ, ∀ y, Real.exp (-(2 * c * ph y)) ≤ K * A.sqn L w y

  et : ι → Y → ℂ
  et_sec : A.IsSec ((i * g0) • de) et
  et_ne : ∃ y, et (A.pick y) y ≠ 0
  p4 : ∃ K : ℝ, ∀ y, A.nsq ((i * g0) • de) et y ≤ K * Real.exp (-(2 * i * ph y))

  th1 : ι → Y → ℂ
  firstTheta_isSection : A.IsSec (2 • L - 2 • de) th1
  firstTheta_bounded : Bdd A (2 • L - 2 • de) th1
  firstTheta_vanishes : C.van (2 • L - 2 • de) 0 th1
  firstTheta_ne_zero : ∃ y, th1 (A.pick y) y ≠ 0

  th2 : ι → Y → ℂ
  secondTheta_isSection : A.IsSec ((n + 4) • L - Fp) th2
  secondTheta_bounded : Bdd A ((n + 4) • L - Fp) th2
  secondTheta_vanishes : C.van ((n + 4) • L - Fp) 0 th2
  secondTheta_ne_zero : ∃ y, th2 (A.pick y) y ≠ 0

  thp : ι → Y → ℂ
  thp_sec : A.IsSec Fp thp
  thp_bdd : Bdd A Fp thp
  thp_van : C.van Fp 0 thp
  thp_ne : ∃ y, thp (A.pick y) y ≠ 0

  ps0 : Y → ℝ
  potential_smooth : A.SmoothFn ps0
  base_psi_levi_lower_bound : ∀ j y, y ∈ (A.chart j).source → ∀ ξ : Fin n → ℂ,
    -(r * A.leviAt j (A.ph de j) y ξ) ≤ A.leviAt j ps0 y ξ
  base_psi_weighted_cf : C.cfw ps0 a1

  posL : ∀ j y, y ∈ (A.chart j).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
    0 < A.leviAt j (A.ph L j) y ξ
  posLde : ∀ j y, y ∈ (A.chart j).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
    0 < A.leviAt j (A.ph (L - de) j) y ξ
  posF : ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → t * r ≤ 2 * T →
    ∀ j y, y ∈ (A.chart j).source → ∀ ξ : Fin n → ℂ,
      2 * η * A.leviAt j (A.ph L j) y ξ ≤
        A.leviAt j (A.ph (Fp - A.kap - n • L) j) y ξ - t * r * A.leviAt j (A.ph de j) y ξ
structure FlatDatum {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : WeightedAtlas n Y ι La) (C : Cusp A) (X : ArchIn A C)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ) : Prop where
  d0 : A.D0 X.L X.w w0 s
  flat : A.Flat w0 s De
  De0 : MvPolynomial.constantCoeff De ≠ 0
  w_le : ∃ K : ℝ, ∀ y, A.sqn X.L X.w y ≤ K * (A.nsq X.L w0 y + A.sqn X.L s y)
  weightForm_bounded : Bdd A X.L w0
  weightForm_vanishes : C.van X.L 0 w0
  s_bdd : ∀ k, Bdd A X.L (s k)
  s_van : ∀ k, C.van X.L 0 (s k)
  thp_nz : ∀ y ∈ A.Mset w0 s De, X.thp (A.pick y) y ≠ 0
def IsValBasis {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (s : Fin n → ι → Y → ℂ) (δ : ℕ) (t : Fin δ → ι → Y → ℂ) : Prop :=
  (∀ v : Y → ℂ, ∃ a : Fin δ → ℂ, ∀ P ∈ A.zeroSet s, ∑ k, a k * t k (A.pick P) P = v P) ∧
  ∀ a : Fin δ → ℂ, (∀ P ∈ A.zeroSet s, ∑ k, a k * t k (A.pick P) P = 0) → a = 0
end
end ReciprocityTheory.ChartRestriction.G.AR


