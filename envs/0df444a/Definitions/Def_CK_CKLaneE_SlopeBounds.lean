-- Prove2me | Definitions.Def_CK_CKLaneE_SlopeBounds
-- name    : CK_CKLaneE_SlopeBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:58:48.27219+00:00
-- url     : https://prove2.me/theorems/30baf26f-604b-4b08-83ee-c7fa8cbfd2ec
-- title:
--   Courtade–Kumar proof module `CKLaneE.SlopeBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.SlopeBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.SlopeBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.SlopeBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/SlopeBounds.lean)

import Definitions.Def_CK_GeneralCK_PhysicalSlope
import Definitions.Def_CK_GeneralCK_ScalarGap

-- ===== source module CKLaneE.SlopeBounds =====
section

/-!
# Lane E: profile slope lemmas for the same-side log-sum checker

* `P1_monotoneOn`: the extended slope `P1` is monotone on `[0,1)`.
* `P_trapezoid`: convexity of `P1` gives the trapezoid upper bound for increments of `P`.
* `P1_le_anchor`: an upper bound for `P1 y` from any rational-friendly anchor `v`
  with `y ≤ 1 - H v`; the value at the anchor is exact because `entropyInverse (H v) = v`.
* `H_eq_logs`: binary entropy in terms of natural logarithms.

No numerical fact is assumed; everything is derived from corpus theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE

open GeneralCK GeneralCK.Scalar Set

theorem P1_monotoneOn : MonotoneOn P1 (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  have hy0 : 0 < y := lt_of_le_of_lt hx.1 h
  have hP1y : 4 ≤ P1 y := by
    rw [P1_eq_deriv hy0]
    exact four_le_deriv_P hy0 hy.2
  have hl0 : 0 ≤ x / y := div_nonneg hx.1 hy0.le
  have hl1 : x / y ≤ 1 := (div_le_one hy0).mpr hxy
  have hconv := P1_convexOn.2 (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 by norm_num) hy
    (sub_nonneg.mpr hl1) hl0 (by ring : (1 - x / y) + x / y = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, P1_zero] at hconv
  rw [div_mul_cancel₀ x hy0.ne'] at hconv
  nlinarith

theorem hasDerivAt_P_P1 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : HasDerivAt P (P1 t) t := by
  rw [P1_eq_deriv ht0]
  exact (hasDerivAt_P ht0 ht1).differentiableAt.hasDerivAt

/-- Trapezoid bound: convexity of the slope `P1` on `[0,1)`. -/
theorem P_trapezoid {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    P y - P x ≤ (y - x) * (P1 x + P1 y) / 2 := by
  rcases eq_or_lt_of_le hxy with h | hlt
  · subst h; simp
  have hsub : Icc x y ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨hx.trans ht.1, lt_of_le_of_lt ht.2 hy⟩
  let φ : ℝ → ℝ := fun t => P t - P x - (t - x) * (P1 x + P1 t) / 2
  have hcont : ContinuousOn φ (Icc x y) := by
    have h1 : ContinuousOn P (Icc x y) := P_continuousOn.mono hsub
    have h2 : ContinuousOn P1 (Icc x y) := P1_continuousOn.mono hsub
    exact (h1.sub continuousOn_const).sub
      (((continuousOn_id.sub continuousOn_const).mul (continuousOn_const.add h2)).div_const 2)
  have hderiv : ∀ t ∈ interior (Icc x y),
      HasDerivWithinAt φ ((P1 t - P1 x - (t - x) * etaCurvature (1 - t)) / 2)
        (interior (Icc x y)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := lt_of_le_of_lt hx ht.1
    have ht1 : t < 1 := lt_trans ht.2 hy
    have hP := hasDerivAt_P_P1 ht0 ht1
    have hP1 := hasDerivAt_P1 ht0 ht1
    have hd := (hP.sub_const (P x)).sub
      ((((hasDerivAt_id' t).sub_const x).mul ((hasDerivAt_const t (P1 x)).add hP1)).div_const 2)
    have hd' : HasDerivAt φ ((P1 t - P1 x - (t - x) * etaCurvature (1 - t)) / 2) t := by
      exact hd.congr_deriv (by simp only [Pi.add_apply]; ring)
    exact hd'.hasDerivWithinAt
  have hnonpos : ∀ t ∈ interior (Icc x y),
      (P1 t - P1 x - (t - x) * etaCurvature (1 - t)) / 2 ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := lt_of_le_of_lt hx ht.1
    have ht1 : t < 1 := lt_trans ht.2 hy
    have hh := P1_convexOn.slope_le_of_hasDerivAt
      (show x ∈ Ico (0 : ℝ) 1 from ⟨hx, lt_trans ht.1 ht1⟩)
      (show t ∈ Ico (0 : ℝ) 1 from ⟨ht0.le, ht1⟩) ht.1 (hasDerivAt_P1 ht0 ht1)
    simp only [slope_def_field] at hh
    have h := (div_le_iff₀ (sub_pos.mpr ht.1)).mp hh
    linarith
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x y) hcont hderiv hnonpos
  have hxy' := hanti ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  have hφx : φ x = 0 := by simp [φ]
  have hφy : φ y ≤ 0 := hφx ▸ hxy'
  simp only [φ] at hφy
  linarith

theorem H_lt_one_of_lt_half {v : ℝ} (hv : 0 ≤ v) (hv' : v < 1 / 2) : H v < 1 := by
  have h := H_strictMonoOn ⟨hv, hv'.le⟩ ⟨by norm_num, le_rfl⟩ hv'
  rw [H_half] at h
  exact h

/-- Anchor bound for the slope: exact value at `1 - H v`, monotone below it. -/
theorem P1_le_anchor {v y : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) (hy : 0 ≤ y)
    (hyv : y ≤ 1 - H v) :
    P1 y ≤ 2 + (1 - 2 * v) / (v * (1 - v) * Real.log ((1 - v) / v)) := by
  have hH0 : 0 < H v := H_pos hv (by linarith)
  have hH1 : H v < 1 := H_lt_one_of_lt_half hv.le hv'
  have hy0 : 0 < 1 - H v := by linarith
  have hy01 : 1 - H v < 1 := by linarith
  have hmono := P1_monotoneOn ⟨hy, lt_of_le_of_lt hyv hy01⟩ ⟨hy0.le, hy01⟩ hyv
  rw [P1_eq_deriv hy0, deriv_P hy0 hy01] at hmono
  have hinv : entropyInverse (1 - (1 - H v)) = v := by
    rw [sub_sub_cancel]
    exact entropyInverse_H_lower hv.le hv'.le
  rw [hinv] at hmono
  have hJ : Real.log 2 * v * (1 - v) * J v = v * (1 - v) * Real.log ((1 - v) / v) := by
    unfold J
    field_simp [log_two_pos.ne']
  rw [hJ] at hmono
  exact hmono

theorem H_eq_logs (q : ℝ) :
    H q = (-(q * Real.log q) - (1 - q) * Real.log (1 - q)) / Real.log 2 := by
  unfold H
  congr 1
  simp only [Real.binEntropy, Real.log_inv]
  ring

end CKLaneE

#check @CKLaneE.P1_monotoneOn
#check @CKLaneE.P_trapezoid
#check @CKLaneE.P1_le_anchor
#check @CKLaneE.H_eq_logs
#print axioms CKLaneE.P1_monotoneOn
#print axioms CKLaneE.P_trapezoid
#print axioms CKLaneE.P1_le_anchor
#print axioms CKLaneE.H_eq_logs

end


