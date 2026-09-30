-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryAnchorRegion
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryAnchorRegion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T09:11:46.904984+00:00
-- url     : https://prove2.me/theorems/ba635c0f-2602-4e3b-9a1d-47d1066c6642
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryAnchorRegion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryAnchorRegion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryAnchorRegion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryAnchorRegion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryAnchorRegion.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryAfterNarrowMiddle

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryAnchorRegion =====
section

/-!
# Exact anchor regions excluding zero-cap left stationary points

The three accepted slope anchors apply on two explicit polyhedra in the
actual entropy coordinates. No narrow probability box is needed. A new
entropy bound also gives a larger concrete probability-domain consequence.
-/

namespace GeneralCK.ZeroCapLeftStationaryAnchorRegion

open ZeroCapLeftStationaryNarrowMiddleCertified

/-- The two positive derivative terms may use the two lower anchors in
either order. Every condition is affine in the actual entropy coordinates. -/
def closedRegion (a e f c : ℝ) : Prop :=
  1 - a - c ≤ (375 / 646) * (e + f) ∧
    (((3175 / 29184) * (e + f) ≤ c - a ∧ (25 / 38) * f ≤ 1 - 2 * c) ∨
      ((25 / 76) * (e + f) ≤ c - a ∧ (3175 / 14592) * f ≤ 1 - 2 * c))

theorem derivative_margin {a e f c : ℝ}
    (ha : 0 < a) (hac : a < c) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) (hr : closedRegion a e f c) :
    1 / 25 ≤ deriv (fun y => canonicalPureGap a y e f) c := by
  let E := e + f
  let U := (c - a) / E
  let V := (1 - a - c) / E
  let W := (1 - 2 * c) / (2 * f)
  have hE : 0 < E := add_pos he hf
  have hUpos : 0 < U := div_pos (sub_pos.mpr hac) hE
  have hVpos : 0 < V := div_pos (by linarith) hE
  have hWpos : 0 < W := div_pos (by linarith) (mul_pos two_pos hf)
  have hV : V ≤ 375 / 646 := (div_le_iff₀ hE).mpr hr.1
  have hThetaV : e8Theta V ≤ 417 / 100 :=
    (strictMonoOn_e8Theta_pos.monotoneOn hVpos (by norm_num) hV).trans theta3_upper
  have hDeriv : deriv (fun y => canonicalPureGap a y e f) c =
      e8Theta U - e8Theta V + e8Theta W := by
    rw [deriv_canonicalPureGap_right hac (by linarith) hc he hf,
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) hf]
    congr 1 <;> dsimp [U, V, W, E] <;> field_simp <;> ring
  rw [hDeriv]
  rcases hr.2 with hfirst | hsecond
  · have hU : 3175 / 29184 ≤ U := (le_div_iff₀ hE).mpr hfirst.1
    have hW : 25 / 76 ≤ W := by
      apply (le_div_iff₀ (mul_pos two_pos hf)).mpr
      linarith only [hfirst.2]
    have hThetaU : 121 / 100 ≤ e8Theta U := theta1_lower.trans
      (strictMonoOn_e8Theta_pos.monotoneOn (by norm_num) hUpos hU)
    have hThetaW : 3 ≤ e8Theta W := theta2_lower.trans
      (strictMonoOn_e8Theta_pos.monotoneOn (by norm_num) hWpos hW)
    linarith only [hThetaU, hThetaV, hThetaW]
  · have hU : 25 / 76 ≤ U := (le_div_iff₀ hE).mpr hsecond.1
    have hW : 3175 / 29184 ≤ W := by
      apply (le_div_iff₀ (mul_pos two_pos hf)).mpr
      linarith only [hsecond.2]
    have hThetaU : 3 ≤ e8Theta U := theta2_lower.trans
      (strictMonoOn_e8Theta_pos.monotoneOn (by norm_num) hUpos hU)
    have hThetaW : 121 / 100 ≤ e8Theta W := theta1_lower.trans
      (strictMonoOn_e8Theta_pos.monotoneOn (by norm_num) hWpos hW)
    linarith only [hThetaU, hThetaV, hThetaW]

theorem no_stationary {a e f c : ℝ}
    (ha : 0 < a) (hac : a < c) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) (hr : closedRegion a e f c) :
    deriv (fun y => canonicalPureGap a y e f) c ≠ 0 := by
  have h := derivative_margin ha hac hc he hf hr
  linarith

/-- The original accepted box is contained in the new exact region. -/
theorem narrow_box_subset {a b c : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 129 / 1024)
    (hb : 129 / 1024 ≤ b) (hb' : b ≤ 65 / 512)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 5 / 16) :
    closedRegion a (H a) (H b) c := by
  obtain ⟨hEl, hEu, hBu⟩ :=
    ZeroCapLeftStationaryEntropyBounds.narrow_box_entropy_bounds ha ha' hb hb'
  refine ⟨by linarith, Or.inl ⟨?_, ?_⟩⟩ <;> linarith

/-- A short, kernel-checked logarithm witness used by the wider domain. -/
theorem log_128_div_111_upper : Real.log (128 / 111 : ℝ) ≤ 143 / 1000 := by
  have h := Certificates.checkLog_sound (w := (17 / 239)) (n := 3)
    (lo := 0) (hi := (143 / 1000))
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.2

theorem H_seventeen_128_upper : H (17 / 128) ≤ (57 / 100 : ℝ) := by
  have he := Certificates.SmallMean.entropy_log_identity (17 / 128 : ℝ)
  have hlog := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)
  norm_num at hlog
  have hA : -Real.log (17 / 128 : ℝ) = 3 * Real.log 2 - Real.log (17 / 16) := by
    rw [show (17 / 128 : ℝ) = (17 / 16) / 2 ^ (3 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hB : -Real.log (1 - (17 / 128 : ℝ)) = Real.log (128 / 111) := by
    rw [show 1 - (17 / 128 : ℝ) = (128 / 111)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [hA, hB] at he
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hm : H (17 / 128) * Real.log 2 ≤ (57 / 100 : ℝ) * Real.log 2 := by
    nlinarith only [he, hlog, log_128_div_111_upper, hL]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hm)

theorem wide_probability_entropy_bounds {a b : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 17 / 128)
    (hb : 1 / 8 ≤ b) (hb' : b ≤ 17 / 128) :
    323 / 300 ≤ H a + H b ∧ H a + H b ≤ 57 / 50 ∧ H b ≤ 57 / 100 := by
  have hHaLower : H (1 / 8) ≤ H a := H_strictMonoOn.monotoneOn
    ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩ ha
  have hHbLower : H (1 / 8) ≤ H b := H_strictMonoOn.monotoneOn
    ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩ hb
  have hHaUpper : H a ≤ H (17 / 128) := H_strictMonoOn.monotoneOn
    ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ ha'
  have hHbUpper : H b ≤ H (17 / 128) := H_strictMonoOn.monotoneOn
    ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ hb'
  have hEl := ZeroCapLeftStationaryEntropyBounds.H_eighth_lower
  have hEu := H_seventeen_128_upper
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A concrete enlarged region; the lower bound on c-a is affine. -/
theorem wide_probability_subset {a b c : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 17 / 128)
    (hb : 1 / 8 ≤ b) (hb' : b ≤ 17 / 128)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 5 / 16) (hsep : 127 / 1024 ≤ c - a) :
    closedRegion a (H a) (H b) c := by
  obtain ⟨hEl, hEu, hBu⟩ := wide_probability_entropy_bounds ha ha' hb hb'
  refine ⟨by linarith, Or.inl ⟨?_, ?_⟩⟩ <;> linarith

theorem no_stationary_in_wide_probability_region {a b c : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 17 / 128)
    (hb : 1 / 8 ≤ b) (hb' : b ≤ 17 / 128)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 5 / 16) (hsep : 127 / 1024 ≤ c - a) :
    deriv (fun y => canonicalPureGap a y (H a) (H b)) c ≠ 0 := by
  exact no_stationary (by linarith) (by linarith) (by linarith)
    (H_pos (by linarith) (by linarith)) (H_pos (by linarith) (by linarith))
    (wide_probability_subset ha ha' hb hb' hc hc' hsep)

theorem residual_iff {a e f c : ℝ} : ¬closedRegion a e f c ↔
    (375 / 646) * (e + f) < 1 - a - c ∨
      ((c - a < (3175 / 29184) * (e + f) ∨ 1 - 2 * c < (25 / 38) * f) ∧
        (c - a < (25 / 76) * (e + f) ∨ 1 - 2 * c < (3175 / 14592) * f)) := by
  simp only [closedRegion, not_and_or, not_or, not_le]

#print axioms derivative_margin
#print axioms no_stationary
#print axioms narrow_box_subset
#print axioms log_128_div_111_upper
#print axioms H_seventeen_128_upper
#print axioms wide_probability_entropy_bounds
#print axioms wide_probability_subset
#print axioms no_stationary_in_wide_probability_region
#print axioms residual_iff

end GeneralCK.ZeroCapLeftStationaryAnchorRegion

namespace GeneralCK

def LeftStationaryOutsideAnchorRegionOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ZeroCapLeftStationaryAnchorRegion.closedRegion (entropyInverse e) e f c →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_of_outsideAnchorRegion
    (h : LeftStationaryOutsideAnchorRegionOwner) :
    ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
      entropyInverse f < c → c < 1 / 2 →
      deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
      0 ≤ canonicalPureGap (entropyInverse e) c e f := by
  intro e f c he hef hf hfc hc hstation
  by_cases hr : ZeroCapLeftStationaryAnchorRegion.closedRegion (entropyInverse e) e f c
  · have ha := entropyInverse_pos he (hef.le.trans hf.le)
    have hac := (entropyInverse_mono he.le hf.le hef.le).trans_lt hfc
    exact False.elim (ZeroCapLeftStationaryAnchorRegion.no_stationary
      ha hac hc he (he.trans hef) hr hstation)
  · exact h e f c he hef hf hfc hc hstation hr

theorem leftStationary_outsideNarrowMiddle_of_anchorRegion
    (h : LeftStationaryOutsideAnchorRegionOwner) : LeftStationaryOutsideNarrowMiddleOwner := by
  intro e f c he hef hf hfc hc hstation _houtside
  exact leftStationary_of_outsideAnchorRegion h e f c he hef hf hfc hc hstation

theorem leftStationary_outsideNarrowMiddle_iff_anchorRegion :
    LeftStationaryOutsideNarrowMiddleOwner ↔ LeftStationaryOutsideAnchorRegionOwner := by
  constructor
  · intro h e f c he hef hf hfc hc hstation _houtside
    exact leftStationary_of_outsideNarrowMiddle h e f c he hef hf hfc hc hstation
  · exact leftStationary_outsideNarrowMiddle_of_anchorRegion

#print axioms leftStationary_of_outsideAnchorRegion
#print axioms leftStationary_outsideNarrowMiddle_of_anchorRegion
#print axioms leftStationary_outsideNarrowMiddle_iff_anchorRegion

end GeneralCK

end


