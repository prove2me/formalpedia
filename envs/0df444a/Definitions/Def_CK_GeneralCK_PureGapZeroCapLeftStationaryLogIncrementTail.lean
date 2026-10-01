-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryLogIncrementTail
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryLogIncrementTail
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:33:15.646321+00:00
-- url     : https://prove2.me/theorems/09b4c6c5-0c87-48fb-bbdb-d71f2d667d90
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryLogIncrementTail` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryLogIncrementTail` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryLogIncrementTail` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryLogIncrementTail (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryLogIncrementTail.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryCompactReduction
import Definitions.Def_CK_GeneralCK_MixedDerivative

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryLogIncrementTail =====
section

/-! A logarithmic slope increment excludes an unbounded low-entropy region.
The mixed-profile bound is already proved on its entire contact domain. -/

namespace GeneralCK.ZeroCapLeftStationaryLogIncrementTail

open Set ZeroCapLeftStationaryHighAnchors ZeroCapLeftStationaryRayEnvelope

theorem mul_deriv_theta_le {x : ℝ} (hx : 0 < x) :
    x * deriv e8Theta x ≤ 13 / 6 := by
  rw [(hasDerivAt_e8Theta hx).deriv]
  have h := global_mixed_derivative_bound (z := 2 * x) (h := 1)
    (by positivity) (by norm_num)
  nlinarith only [h]

theorem log_minus_theta_mono :
    MonotoneOn (fun x : ℝ => (13 / 6) * Real.log x - e8Theta x) (Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => (13 / 6) * Real.log y - e8Theta y)
        ((13 / 6) * x⁻¹ - deriv e8Theta x) x := by
    intro x hx
    exact ((Real.hasDerivAt_log hx.ne').const_mul (13 / 6)).sub
      (hasDerivAt_e8Theta hx).differentiableAt.hasDerivAt
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := interior_subset hx
    have h := mul_deriv_theta_le hxpos
    have hdiv : deriv e8Theta x ≤ (13 / 6) * x⁻¹ := by
      have hd' : deriv e8Theta x ≤ (13 / 6) / x :=
        (le_div_iff₀ hxpos).mpr (by simpa only [mul_comm] using h)
      simpa only [div_eq_mul_inv] using hd'
    linarith only [hdiv]

theorem theta_increment_log_bound {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    e8Theta v - e8Theta u ≤ (13 / 6) * Real.log (v / u) := by
  have hv : 0 < v := hu.trans_le huv
  have hm := log_minus_theta_mono hu hv huv
  rw [Real.log_div hv.ne' hu.ne']
  linarith only [hm]

theorem theta_increment_mul_bound {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (e8Theta v - e8Theta u) * u ≤ (13 / 6) * (v - u) := by
  have hv : 0 < v := hu.trans_le huv
  have hlog := Real.log_le_sub_one_of_pos (div_pos hv hu)
  have hinc := theta_increment_log_bound hu huv
  have hscale := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 13 / 6)
  have hm := mul_le_mul_of_nonneg_right (hinc.trans hscale) hu.le
  have heq : ((13 / 6) * (v / u - 1)) * u = (13 / 6) * (v - u) := by
    field_simp
  rwa [heq] at hm

theorem theta_increment_le_91_div_30 {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hvu : v ≤ 4 * u) :
    e8Theta v - e8Theta u ≤ 91 / 30 := by
  have hv : 0 < v := hu.trans_le huv
  have hquot : v / u ≤ 4 := (div_le_iff₀ hu).mpr hvu
  have hlog := Real.log_le_log (div_pos hv hu) hquot
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  rw [hfour] at hlog
  linarith only [theta_increment_log_bound hu huv, hlog, hL]

theorem theta_lower_linear_to_seven_tenths {w : ℝ}
    (hw : 0 < w) (hw' : w ≤ 7 / 10) : (89 / 14) * w ≤ e8Theta w := by
  have h := theta_lower_ray (by norm_num : (0 : ℝ) < 7 / 10) hw theta_seven_tenths_lower
  rw [min_eq_right ((div_le_one (by norm_num)).mpr hw')] at h
  convert h using 1 <;> ring

/-- This unbounded cone has positive actual slope sum, uniformly for all W>0. -/
theorem theta_sum_positive_on_cone {u v w : ℝ}
    (hu : 5 / 4 ≤ u) (hw : 0 < w) (huv : u ≤ v)
    (hvu : v ≤ 4 * u) (hgap : v - u ≤ 2 * w) :
    0 < e8Theta u - e8Theta v + e8Theta w := by
  have hup : 0 < u := by linarith
  by_cases hw' : w ≤ 7 / 10
  · have hl := theta_lower_linear_to_seven_tenths hw hw'
    have hlmul := mul_le_mul_of_nonneg_right hl hup.le
    have hi := theta_increment_mul_bound hup huv
    have huw := mul_nonneg (sub_nonneg.mpr hu) hw.le
    have hpos : 0 < u * (e8Theta u - e8Theta v + e8Theta w) := by
      nlinarith only [hlmul, hi, huw, hgap, hw]
    exact (mul_pos_iff_of_pos_left hup).mp hpos
  · have hwl : 7 / 10 ≤ w := (lt_of_not_ge hw').le
    have hl := theta_seven_tenths_lower.trans
      (strictMonoOn_e8Theta_pos.monotoneOn (by norm_num) hw hwl)
    have hi := theta_increment_le_91_div_30 hup huv hvu
    linarith only [hl, hi]

theorem derivative_positive_on_cone {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hu : (5 / 4) * (e + f) ≤ c - a)
    (hvu : 1 - a - c ≤ 4 * (c - a)) :
    0 < deriv (fun y => canonicalPureGap a y e f) c := by
  let U := (c - a) / (e + f)
  let V := (1 - a - c) / (e + f)
  let W := (1 - 2 * c) / (2 * f)
  have hE : 0 < e + f := add_pos he hf
  have hU : 5 / 4 ≤ U := (le_div_iff₀ hE).mpr hu
  have hW : 0 < W := div_pos (by linarith) (mul_pos two_pos hf)
  have hUV : U ≤ V := div_le_div_of_nonneg_right (by linarith) hE.le
  have hVU : V ≤ 4 * U := by
    have h := div_le_div_of_nonneg_right hvu hE.le
    dsimp [V, U]
    simpa only [mul_div_assoc] using h
  have hcoeff : 2 * f / (e + f) ≤ 2 := (div_le_iff₀ hE).mpr (by linarith)
  have hid : V - U = (2 * f / (e + f)) * W := by
    dsimp [U, V, W]
    field_simp
    ring
  have hgap : V - U ≤ 2 * W := by rw [hid]; exact mul_le_mul_of_nonneg_right hcoeff hW.le
  have hDeriv : deriv (fun y => canonicalPureGap a y e f) c =
      e8Theta U - e8Theta V + e8Theta W := by
    rw [deriv_canonicalPureGap_right hac (by linarith) hc he hf,
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) hf]
    congr 1 <;> dsimp [U, V, W] <;> field_simp
  rw [hDeriv]
  exact theta_sum_positive_on_cone hU hW hUV hVU hgap

theorem entropy_sixteenth_lower : (1 / 4 : ℝ) ≤ H (1 / 16) := by
  have hm : (1 / 4 : ℝ) * Real.log 2 ≤ H (1 / 16) * Real.log 2 := by
    linarith only [entropy_sixteenth_identity, log_fifteen_upper]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hm)

theorem inverse_le_sixteenth_of_small_entropy {e : ℝ} (he : 0 ≤ e) (he' : e ≤ 1 / 16) :
    entropyInverse e ≤ 1 / 16 := by
  have hH : e ≤ H (1 / 16) := by linarith only [he', entropy_sixteenth_lower]
  have hm := entropyInverse_mono he (H_le_one (1 / 16)) hH
  rwa [entropyInverse_H_lower (by norm_num) (by norm_num)] at hm

/-- The whole low-entropy range c>=1/4 is excluded, including arbitrarily
small entropy and arbitrarily large normalized coordinates. -/
theorem lowEntropy_upperQuarter_derivative_positive {e f c : ℝ}
    (he : 0 < e) (hef : e < f) (hf : f < 1 / 16)
    (hc : c < 1 / 2) (hcq : 1 / 4 ≤ c) :
    0 < deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c := by
  have ha := inverse_le_sixteenth_of_small_entropy he.le (by linarith)
  have hac : entropyInverse e < c := by linarith
  apply derivative_positive_on_cone hac hc he (he.trans hef)
  · linarith
  · linarith

#print axioms mul_deriv_theta_le
#print axioms log_minus_theta_mono
#print axioms theta_increment_log_bound
#print axioms theta_increment_mul_bound
#print axioms theta_increment_le_91_div_30
#print axioms theta_lower_linear_to_seven_tenths
#print axioms theta_sum_positive_on_cone
#print axioms derivative_positive_on_cone
#print axioms lowEntropy_upperQuarter_derivative_positive

end GeneralCK.ZeroCapLeftStationaryLogIncrementTail

namespace GeneralCK

def LeftStationaryLowEntropyLowerQuarterOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ZeroCapLeftStationaryRatioExclusion.closedRegion (entropyInverse e) e f c →
    f < 1 / 16 → c < 1 / 4 → 0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_lowEntropyTail_of_lowerQuarter
    (h : LeftStationaryLowEntropyLowerQuarterOwner) : LeftStationaryLowEntropyTailOwner := by
  intro e f c he hef hf hfc hc hstation hr htail
  by_cases hcq : 1 / 4 ≤ c
  · have hpos := ZeroCapLeftStationaryLogIncrementTail.lowEntropy_upperQuarter_derivative_positive
      he hef htail hc hcq
    rw [hstation] at hpos
    linarith
  · exact h e f c he hef hf hfc hc hstation hr htail (lt_of_not_ge hcq)

theorem leftStationary_lowEntropyTail_iff_lowerQuarter :
    LeftStationaryLowEntropyTailOwner ↔ LeftStationaryLowEntropyLowerQuarterOwner := by
  constructor
  · intro h e f c he hef hf hfc hc hstation hr htail _hcq
    exact h e f c he hef hf hfc hc hstation hr htail
  · exact leftStationary_lowEntropyTail_of_lowerQuarter

theorem leftStationary_outsideRatioExclusion_of_compact_and_lowerQuarter
    (hcompact : LeftStationaryCompactBoxOwner) (htail : LeftStationaryLowEntropyLowerQuarterOwner) :
    LeftStationaryOutsideRatioExclusionOwner :=
  leftStationary_outsideRatioExclusion_of_compact_and_tail hcompact
    (leftStationary_lowEntropyTail_of_lowerQuarter htail)

#print axioms leftStationary_lowEntropyTail_of_lowerQuarter
#print axioms leftStationary_lowEntropyTail_iff_lowerQuarter
#print axioms leftStationary_outsideRatioExclusion_of_compact_and_lowerQuarter

end GeneralCK

end


