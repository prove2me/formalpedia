-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryRatioExclusion
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryRatioExclusion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:05:49.771722+00:00
-- url     : https://prove2.me/theorems/f2f3aa3a-061b-46e9-b449-18518a601b9f
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryRatioExclusion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryRatioExclusion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryRatioExclusion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryRatioExclusion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryRatioExclusion.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryHighRangeEnvelope

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryRatioExclusion =====
section

/-! Cancellation between the two nearby slope terms gives a stationary
exclusion extending to the half-mean face. -/

namespace GeneralCK.ZeroCapLeftStationaryRatioExclusion

open ZeroCapLeftStationaryHighRangeEnvelope

noncomputable def ratioBudget (a e f c : ℝ) : ℝ :=
  lowerEnvelope ((1 - 2 * c) / (2 * f)) * ((c - a) / (e + f)) -
    (((1 - a - c) / (e + f)) - ((c - a) / (e + f))) *
      upperEnvelope ((c - a) / (e + f))

theorem ratioBudget_le_mul_derivative {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f) :
    ratioBudget a e f c ≤ ((c - a) / (e + f)) *
      deriv (fun y => canonicalPureGap a y e f) c := by
  let U := (c - a) / (e + f)
  let V := (1 - a - c) / (e + f)
  let W := (1 - 2 * c) / (2 * f)
  have hUpos : 0 < U := div_pos (sub_pos.mpr hac) (add_pos he hf)
  have hVpos : 0 < V := div_pos (by linarith) (add_pos he hf)
  have hWpos : 0 < W := div_pos (by linarith) (mul_pos two_pos hf)
  have hUV : U ≤ V := div_le_div_of_nonneg_right (by linarith) (add_pos he hf).le
  have hratio := (div_le_div_iff₀ hVpos hUpos).mp
    (antitoneOn_e8Theta_div hUpos hVpos hUV)
  have hupper := mul_le_mul_of_nonneg_left
    (theta_le_upperEnvelope hUpos) (sub_nonneg.mpr hUV)
  have hlower := mul_le_mul_of_nonneg_right (lowerEnvelope_le_theta hWpos) hUpos.le
  have hDeriv : deriv (fun y => canonicalPureGap a y e f) c =
      e8Theta U - e8Theta V + e8Theta W := by
    rw [deriv_canonicalPureGap_right hac (by linarith) hc he hf,
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) hf]
    congr 1 <;> dsimp [U, V, W] <;> field_simp
  change lowerEnvelope W * U - (V - U) * upperEnvelope U ≤ U * _
  rw [hDeriv]
  nlinarith only [hratio, hupper, hlower]

theorem derivative_positive_of_ratioBudget {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hr : 0 < ratioBudget a e f c) :
    0 < deriv (fun y => canonicalPureGap a y e f) c := by
  have hU := div_pos (sub_pos.mpr hac) (add_pos he hf)
  have hm := hr.trans_le (ratioBudget_le_mul_derivative hac hc he hf)
  exact (mul_pos_iff_of_pos_left hU).mp hm

theorem upperEnvelope_le_linear {u : ℝ} (hu : 5 / 4 ≤ u) :
    upperEnvelope u ≤ (118 / 25) * u := by
  have hr : (1 : ℝ) ≤ u / (5 / 4) :=
    (le_div_iff₀ (by norm_num)).mpr (by simpa using hu)
  calc
    upperEnvelope u ≤ (59 / 10) * max 1 (u / (5 / 4)) := min_le_right _ _
    _ = (118 / 25) * u := by rw [max_eq_right hr]; ring

theorem lowerEnvelope_ge_linear {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 3175 / 29184) :
    11 * w ≤ lowerEnvelope w := by
  have hr : w / (3175 / 29184) ≤ (1 : ℝ) := (div_le_one (by norm_num)).mpr hw'
  have hprev : (121 / 100) * (w / (3175 / 29184)) ≤
      ZeroCapLeftStationaryRayEnvelope.lowerEnvelope w := by
    unfold ZeroCapLeftStationaryRayEnvelope.lowerEnvelope
    rw [min_eq_right hr]
    exact le_max_left _ _
  have hlin : 11 * w ≤ (121 / 100) * (w / (3175 / 29184)) := by
    nlinarith only [hw]
  exact (hlin.trans hprev).trans (previous_le_lowerEnvelope w)

theorem normalized_ratioBudget_margin {u v w : ℝ}
    (hu : 5 / 4 ≤ u) (hw : 0 ≤ w) (hw' : w ≤ 3175 / 29184)
    (huv : u ≤ v) (hgap : v - u ≤ 2 * w) :
    (39 / 25) * u * w ≤ lowerEnvelope w * u - (v - u) * upperEnvelope u := by
  have hupos : 0 < u := by linarith
  have hlow := mul_le_mul_of_nonneg_right (lowerEnvelope_ge_linear hw hw') hupos.le
  have hhigh := mul_le_mul_of_nonneg_left (upperEnvelope_le_linear hu) (sub_nonneg.mpr huv)
  have hinc := mul_le_mul_of_nonneg_right hgap
    (show 0 ≤ (118 / 25 : ℝ) * u by positivity)
  nlinarith only [hlow, hhigh, hinc]

/-- This bound remains positive for arbitrarily small positive W, so it
reaches the c -> 1/2 face without a uniform positive margin assumption. -/
theorem derivative_smallW_margin {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hu : (5 / 4) * (e + f) ≤ c - a)
    (hw : 1 - 2 * c ≤ (3175 / 14592) * f) :
    (39 / 25) * ((1 - 2 * c) / (2 * f)) ≤
      deriv (fun y => canonicalPureGap a y e f) c := by
  let U := (c - a) / (e + f)
  let V := (1 - a - c) / (e + f)
  let W := (1 - 2 * c) / (2 * f)
  have hE : 0 < e + f := add_pos he hf
  have hUpos : 0 < U := div_pos (sub_pos.mpr hac) hE
  have hWpos : 0 < W := div_pos (by linarith) (mul_pos two_pos hf)
  have hU : 5 / 4 ≤ U := (le_div_iff₀ hE).mpr hu
  have hW : W ≤ 3175 / 29184 :=
    (div_le_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hw])
  have hUV : U ≤ V := div_le_div_of_nonneg_right (by linarith) hE.le
  have hcoeff : 2 * f / (e + f) ≤ 2 := (div_le_iff₀ hE).mpr (by linarith)
  have hid : V - U = (2 * f / (e + f)) * W := by
    dsimp [U, V, W]
    field_simp
    ring
  have hgap : V - U ≤ 2 * W := by rw [hid]; exact mul_le_mul_of_nonneg_right hcoeff hWpos.le
  have hbudget := normalized_ratioBudget_margin hU hWpos.le hW hUV hgap
  have hderiv := ratioBudget_le_mul_derivative hac hc he hf
  change lowerEnvelope W * U - (V - U) * upperEnvelope U ≤ U * _ at hderiv
  change (39 / 25) * W ≤ _
  nlinarith only [hbudget, hderiv, hUpos]

def closedRegion (a e f c : ℝ) : Prop :=
  ZeroCapLeftStationaryHighRangeEnvelope.closedRegion a e f c ∨ 0 < ratioBudget a e f c

theorem previousRegion_subset {a e f c : ℝ}
    (hr : ZeroCapLeftStationaryHighRangeEnvelope.closedRegion a e f c) :
    closedRegion a e f c := Or.inl hr

theorem no_stationary {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hr : closedRegion a e f c) : deriv (fun y => canonicalPureGap a y e f) c ≠ 0 := by
  rcases hr with hprev | hratio
  · exact ZeroCapLeftStationaryHighRangeEnvelope.no_stationary hac hc he hf hprev
  · exact (derivative_positive_of_ratioBudget hac hc he hf hratio).ne'

theorem smallW_subset {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hu : (5 / 4) * (e + f) ≤ c - a)
    (hw : 1 - 2 * c ≤ (3175 / 14592) * f) : closedRegion a e f c := by
  apply Or.inr
  let U := (c - a) / (e + f)
  let V := (1 - a - c) / (e + f)
  let W := (1 - 2 * c) / (2 * f)
  have hE : 0 < e + f := add_pos he hf
  have hU : 5 / 4 ≤ U := (le_div_iff₀ hE).mpr hu
  have hUpos : 0 < U := by linarith
  have hWpos : 0 < W := div_pos (by linarith) (mul_pos two_pos hf)
  have hW : W ≤ 3175 / 29184 :=
    (div_le_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hw])
  have hUV : U ≤ V := div_le_div_of_nonneg_right (by linarith) hE.le
  have hcoeff : 2 * f / (e + f) ≤ 2 := (div_le_iff₀ hE).mpr (by linarith)
  have hid : V - U = (2 * f / (e + f)) * W := by
    dsimp [U, V, W]
    field_simp
    ring
  have hgap : V - U ≤ 2 * W := by rw [hid]; exact mul_le_mul_of_nonneg_right hcoeff hWpos.le
  have hbudget := normalized_ratioBudget_margin hU hWpos.le hW hUV hgap
  have hpos : 0 < (39 / 25 : ℝ) * U * W := by positivity
  exact hpos.trans_le hbudget

theorem residual_iff {a e f c : ℝ} : ¬closedRegion a e f c ↔
    (lowerEnvelope ((c - a) / (e + f)) + lowerEnvelope ((1 - 2 * c) / (2 * f)) -
      upperEnvelope ((1 - a - c) / (e + f)) ≤ 0) ∧ ratioBudget a e f c ≤ 0 := by
  simp only [closedRegion, not_or, ZeroCapLeftStationaryHighRangeEnvelope.residual_iff, not_lt]

#print axioms ratioBudget_le_mul_derivative
#print axioms derivative_positive_of_ratioBudget
#print axioms upperEnvelope_le_linear
#print axioms lowerEnvelope_ge_linear
#print axioms normalized_ratioBudget_margin
#print axioms derivative_smallW_margin
#print axioms previousRegion_subset
#print axioms no_stationary
#print axioms smallW_subset
#print axioms residual_iff

end GeneralCK.ZeroCapLeftStationaryRatioExclusion

namespace GeneralCK

def LeftStationaryOutsideRatioExclusionOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ZeroCapLeftStationaryRatioExclusion.closedRegion (entropyInverse e) e f c →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_of_outsideRatioExclusion
    (h : LeftStationaryOutsideRatioExclusionOwner) :
    ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
      entropyInverse f < c → c < 1 / 2 →
      deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
      0 ≤ canonicalPureGap (entropyInverse e) c e f := by
  intro e f c he hef hf hfc hc hstation
  by_cases hr : ZeroCapLeftStationaryRatioExclusion.closedRegion (entropyInverse e) e f c
  · have hac := (entropyInverse_mono he.le hf.le hef.le).trans_lt hfc
    exact False.elim (ZeroCapLeftStationaryRatioExclusion.no_stationary
      hac hc he (he.trans hef) hr hstation)
  · exact h e f c he hef hf hfc hc hstation hr

theorem leftStationary_outsideHighRangeEnvelope_of_ratioExclusion
    (h : LeftStationaryOutsideRatioExclusionOwner) : LeftStationaryOutsideHighRangeEnvelopeOwner := by
  intro e f c he hef hf hfc hc hstation _houtside
  exact leftStationary_of_outsideRatioExclusion h e f c he hef hf hfc hc hstation

theorem leftStationary_outsideHighRangeEnvelope_iff_ratioExclusion :
    LeftStationaryOutsideHighRangeEnvelopeOwner ↔ LeftStationaryOutsideRatioExclusionOwner := by
  constructor
  · intro h e f c he hef hf hfc hc hstation _houtside
    exact leftStationary_of_outsideHighRangeEnvelope h e f c he hef hf hfc hc hstation
  · exact leftStationary_outsideHighRangeEnvelope_of_ratioExclusion

#print axioms leftStationary_of_outsideRatioExclusion
#print axioms leftStationary_outsideHighRangeEnvelope_of_ratioExclusion
#print axioms leftStationary_outsideHighRangeEnvelope_iff_ratioExclusion

end GeneralCK

end


