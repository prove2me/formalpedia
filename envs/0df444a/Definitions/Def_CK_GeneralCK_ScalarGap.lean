-- Prove2me | Definitions.Def_CK_GeneralCK_ScalarGap
-- name    : CK_GeneralCK_ScalarGap
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:47.124608+00:00
-- url     : https://prove2.me/theorems/71d7f3dd-3242-44d8-90ec-18af9ae7c2f9
-- title:
--   Courtade–Kumar proof module `GeneralCK.ScalarGap` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ScalarGap` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ScalarGap` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ScalarGap (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ScalarGap.lean)

import Definitions.Def_CK_GeneralCK_ProfileIncreasingCurvature
import Mathlib.Analysis.Convex.Jensen

namespace GeneralCK.Scalar
open Set

noncomputable def gap (j α Δ s : ℝ) : ℝ := j + α * s - P (Δ + s) + P s

theorem gap_concaveOn (j α : ℝ) {Δ S : ℝ}
    (hΔ : 0 ≤ Δ) (_hS : 0 ≤ S) (hcap : Δ + S < 1) :
    ConcaveOn ℝ (Icc 0 S) (gap j α Δ) := by
  have hleft : ContinuousOn (fun s => P (Δ + s)) (Icc 0 S) := by
    apply P_continuousOn.comp (continuous_const.add continuous_id).continuousOn
    intro s hs
    change 0 ≤ Δ + s ∧ Δ + s < 1
    constructor <;> linarith [hs.1, hs.2]
  have hright : ContinuousOn P (Icc 0 S) := P_continuousOn.mono (by
    intro s hs
    exact ⟨hs.1, by linarith [hs.2]⟩)
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 S)
    (f' := fun s => α - deriv P (Δ + s) + deriv P s)
    (f'' := fun s => -deriv (deriv P) (Δ + s) + deriv (deriv P) s)
  · exact ((continuous_const.add (continuous_const.mul continuous_id)).continuousOn.sub hleft).add hright
  · intro s hs
    rw [interior_Icc] at hs
    have hs' : s < 1 := by linarith [hs.2]
    have ht : 0 < Δ + s := by linarith [hs.1]
    have ht' : Δ + s < 1 := by linarith [hs.2]
    have hd := (((hasDerivAt_id s).const_mul α).const_add j).sub
      ((hasDerivAt_P ht ht').comp s ((hasDerivAt_id s).const_add Δ))
    have hd' := hd.add (hasDerivAt_P hs.1 hs')
    rw [← deriv_P ht ht', ← deriv_P hs.1 hs'] at hd'
    convert! hd'.hasDerivWithinAt using 1
    simp
  · intro s hs
    rw [interior_Icc] at hs
    have hs' : s < 1 := by linarith [hs.2]
    have ht : 0 < Δ + s := by linarith [hs.1]
    have ht' : Δ + s < 1 := by linarith [hs.2]
    have hd := (((hasDerivAt_deriv_P ht ht').comp s
      ((hasDerivAt_id s).const_add Δ)).const_sub α).add (hasDerivAt_deriv_P hs.1 hs')
    rw [← deriv2_P ht ht', ← deriv2_P hs.1 hs'] at hd
    convert! hd.hasDerivWithinAt using 1
    simp
  · intro s hs
    rw [interior_Icc] at hs
    have hm := deriv2_P_monotoneOn
      (show s ∈ Ioo (0 : ℝ) 1 from ⟨hs.1, by linarith [hs.2]⟩)
      (show Δ + s ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (show s ≤ Δ + s by linarith)
    linarith

/-- Concavity reduces every intermediate entropy deficit to the two endpoints. -/
theorem gap_endpoint_criterion {j α Δ S s : ℝ}
    (hΔ : 0 ≤ Δ) (hS : 0 ≤ S) (hcap : Δ + S < 1)
    (hzero : P Δ ≤ j) (hend : 0 ≤ gap j α Δ S) (hs : 0 ≤ s) (hs' : s ≤ S) :
    P (Δ + s) - P s ≤ j + α * s := by
  have hz : 0 ≤ gap j α Δ 0 := by simpa [gap] using sub_nonneg.mpr hzero
  have hm := (gap_concaveOn j α hΔ hS hcap).min_le_of_mem_Icc
    (show (0 : ℝ) ∈ Icc 0 S from ⟨le_rfl, hS⟩)
    (show S ∈ Icc (0 : ℝ) S from ⟨hS, le_rfl⟩) ⟨hs, hs'⟩
  have hg : 0 ≤ gap j α Δ s := (le_min hz hend).trans hm
  unfold gap at hg
  linarith

/-- The final-point secant bound includes the physical zero endpoint and
the equality case, while differentiating only at a positive information value. -/
theorem P_increment_upper {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : 0 < y) (hy' : y < 1) :
    P y - P x ≤ (y - x) * deriv P y := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hh := P_convexOn.slope_le_of_hasDerivAt
    (show x ∈ Ico (0 : ℝ) 1 from ⟨hx, hxy.trans hy'⟩)
    (show y ∈ Ico (0 : ℝ) 1 from ⟨hy.le, hy'⟩) hxy (hasDerivAt_P hy hy')
  rw [← deriv_P hy hy'] at hh
  simp only [slope_def_field] at hh
  have h := (div_le_iff₀ (sub_pos.mpr hxy)).mp hh
  simpa only [mul_comm] using h

end GeneralCK.Scalar


