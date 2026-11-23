-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:20.030534+00:00
-- url     : https://prove2.me/theorems/b04d2c01-ff3d-4add-ac5a-4e1523bfc6e1
-- title:
--   Base Psi Levi Lower Bound
-- statement:
--   Definitions and structural lemmas for Base Psi Levi Lower Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/BasePsiLeviLowerBound.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetIndepStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def IsInvFn (X : Data E r) (ph : Frame X.Ψ r → ℝ) : Prop :=
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ph (lact γ (rmul x b)) = ph x
def leviM (X : Data E r) (g : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((g (cpt X x0 w) : ℝ) : ℂ)) z ξ).re
def cfwM (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  (∃ C A' : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x)) ∧
  ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ C A' : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ x τ) →
    ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ
structure ArchInM (X : Data E r) where
  L : Wt X.Ψ r
  de : Wt X.Ψ r
  Fp : Wt X.Ψ r
  T : ℕ
  i : ℕ
  g0 : ℕ
  N : ℕ
  c : ℝ
  c1 : ℝ
  a1 : ℝ
  rr : ℝ
  n_ge : 2 ≤ nd X
  T_ge : 11 * nd X ^ 2 ≤ T
  i_pos : 1 ≤ i
  genus_pos : 1 ≤ g0
  c_pos : 0 < c
  frame_theta_const_pos : 0 < c1
  frame_theta_weight_pos : 0 < a1
  rr_nonneg : 0 ≤ rr
  Tcg0 : (T : ℝ) * c * g0 ≤ 1
  rr_le : rr * (1 + c1 / a1) ≤ 2 * T
  w : Fin N → Frame X.Ψ r → ℂ
  w_van : ∀ k, w k ∈ X.SSgt L 0
  w_nz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0
  ph : Frame X.Ψ r → ℝ
  ph_inv : IsInvFn X ph
  ph_nonneg : ∀ x ∈ X.dom, 0 ≤ ph x
  p1 : ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x
  p2 : ∀ x ∈ X.dom, (T : ℝ) * c * ph x ≤ c1 / X.la1 x ^ 2
  p3 : ∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm L (w k) x ^ 2
  et : Frame X.Ψ r → ℂ
  genus_even : Even g0
  et_sec : X.IsSec ((i * (g0 / 2)) • de) et
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  p4 : ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm ((i * (g0 / 2)) • de) et x ^ 2 ≤ K * Real.exp (-(2 * i * ph x))
  th1 : Frame X.Ψ r → ℂ
  firstTheta_vanishes : th1 ∈ X.SSgt (2 • L - de) 0
  firstTheta_ne_zero : ∃ x ∈ X.dom, th1 x ≠ 0
  th2 : Frame X.Ψ r → ℂ
  secondTheta_vanishes : th2 ∈ X.SSgt ((nd X + 4) • L - Fp) 0
  secondTheta_ne_zero : ∃ x ∈ X.dom, th2 x ≠ 0
  thp : Frame X.Ψ r → ℂ
  thp_van : thp ∈ X.SSgt Fp 0
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0
  ps0 : Frame X.Ψ r → ℝ
  potential_invariant : IsInvFn X ps0
  potential_smooth : ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps0 (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}
  base_psi_levi_lower_bound : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
    -(rr / 2 * leviM X (phla X de) x0 z ξ) ≤ leviM X ps0 x0 z ξ
  base_psi_weighted_cf : cfwM X ps0 a1
  posL : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    0 < leviM X (phla X L) x0 z ξ
  posLde : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    0 < leviM X (phla X (2 • L - de)) x0 z ξ
  posF : ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * T →
    ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviM X (phla X L) x0 z ξ ≤
        leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - t * (rr / 2) * leviM X (phla X de) x0 z ξ
structure FlatM (X : Data E r) (Xa : ArchInM X) where
  w0 : Frame X.Ψ r → ℂ
  s : Fin (nd X) → Frame X.Ψ r → ℂ
  weightForm_vanishes : w0 ∈ X.SSgt Xa.L 0
  s_van : ∀ k, s k ∈ X.SSgt Xa.L 0
  δ : ℕ
  xs : Fin δ → Frame X.Ψ r
  xs_mem : ∀ j, xs j ∈ X.dom
  S_eq : ∀ x ∈ X.dom, (∀ k, s k x = 0) ↔
    ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)
  xs_inj : ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j'
  w0_ne : ∀ j, w0 (xs j) ≠ 0
  coord : ∀ j, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
    s k (cpt X (xs j) z) / w0 (cpt X (xs j) z) : V (nd X))) 0).det ≠ 0
  w_le : ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
    K * (X.pnorm Xa.L w0 x ^ 2 + ∑ k, X.pnorm Xa.L (s k) x ^ 2)

  denom_le_family : ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm Xa.L w0 x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2
  s_le_w : ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (s k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2

  family_le_coords : ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ j, xs j ∈ U) →
    (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
    ∃ K : ℝ, ∀ x ∈ X.dom, x ∉ U → ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (s k) x ^ 2
def monoM {n : ℕ} (X : Data E r) (s : Fin n → Frame X.Ψ r → ℂ) (α : Fin n → ℕ) (x : Frame X.Ψ r) : ℂ :=
  ∏ k, s k x ^ α k
def leadM {n δ : ℕ} (X : Data E r) (s : Fin n → Frame X.Ψ r → ℂ) (w0 : Frame X.Ψ r → ℂ)
    (t : Fin δ → Frame X.Ψ r → ℂ) (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt n a0, ∑ k, cc α k * monoM X s α x * w0 x ^ (T - ∑ q, α q) * t k x
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


