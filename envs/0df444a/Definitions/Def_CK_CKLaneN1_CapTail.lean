-- Prove2me | Definitions.Def_CK_CKLaneN1_CapTail
-- name    : CK_CKLaneN1_CapTail
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:15:37.578802+00:00
-- url     : https://prove2.me/theorems/7dc4c2b4-9f03-4d87-b7d1-a6a5048cbc73
-- title:
--   Courtade–Kumar proof module `CKLaneN1.CapTail` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.CapTail` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.CapTail` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.CapTail (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/CapTail.lean)

import Definitions.Def_CK_CKLaneN1_CapSlope
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryLogIncrementTail
import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaHigherDerivatives

-- ===== source module CKLaneN1.CapTail =====
section

set_option autoImplicit false

/-!
# Lane N1: capital exclusion — analytic tails and anchors

* `profile_le_small`: `profile v ≤ 81/50` for `0 < v ≤ 1/2000`
  (from `hn ≤ v(L+1)`, `kap ≥ L/2`, `2kap - (1-2v)² ≤ L - 0.997`, `L = -log v ≥ 7.5`);
* `theta_increment_tail`: `Θ(y) - Θ(x) ≤ (81/50) log (y/x)` for `128 ≤ x ≤ y`;
* anchors `Θ(21/200)`, `Θ(1/5)`, `Θ(303/50)` from contact witnesses (kernel checked).
-/

namespace CKLaneN1.Capital

open GeneralCK CKLaneE.FP GeneralCK.Certificates.Mixed

/-! ## Rational anchors (kernel checked) -/

def vA0 : ℚ := dy 1793171331294041 52
def vB0 : ℚ := dy 1437911680383111 52
def vW0 : ℚ := dy 45079052257119 52

theorem anchorA_ok : slopeLoOk vA0 = true ∧ 1 - 2 * vA0 ≤ 2 * (21 / 200) * Hlo vA0 := by
  constructor <;> decide +kernel
theorem anchorB_ok : slopeLoOk vB0 = true ∧ 1 - 2 * vB0 ≤ 2 * (1 / 5) * Hlo vB0 := by
  constructor <;> decide +kernel
theorem anchorW_ok : slopeLoOk vW0 = true ∧ 1 - 2 * vW0 ≤ 2 * (303 / 50) * Hlo vW0 := by
  constructor <;> decide +kernel

/-- `log 3 ≤ -lLo(1/3)` and `log (1281/640) ≤ -lLo(640/1281)`; numeric comparisons with anchors. -/
theorem logs_ok : ptOk (1 / 3) = true ∧ ptOk (640 / 1281) = true ∧ ptOk (1 / 2000) = true ∧
    (81 / 50) * (-lLo (640 / 1281)) ≤ slopeLo vA0 ∧
    (81 / 50) * (-lLo (1 / 3)) ≤ slopeLo vB0 ∧
    (13 / 6) * (-lLo (1 / 3)) ≤ slopeLo vW0 ∧
    (1999 / 2000 : ℚ) ≤ 256 * Hlo (1 / 2000) ∧
    lHi (1 / 2000) ≤ -15 / 2 ∧
    Hhi (1 / 100) ≤ 49 / 606 ∧ ptOk (1 / 100) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem theta_anchorA : ((slopeLo vA0 : ℚ) : ℝ) ≤ e8Theta (21 / 200) := by
  refine theta_ge (by norm_num) anchorA_ok.1 ?_
  have h := (Rat.cast_le (K := ℝ)).mpr anchorA_ok.2
  push_cast at h
  linarith

theorem theta_anchorB : ((slopeLo vB0 : ℚ) : ℝ) ≤ e8Theta (1 / 5) := by
  refine theta_ge (by norm_num) anchorB_ok.1 ?_
  have h := (Rat.cast_le (K := ℝ)).mpr anchorB_ok.2
  push_cast at h
  linarith

theorem theta_anchorW : ((slopeLo vW0 : ℚ) : ℝ) ≤ e8Theta (303 / 50) := by
  refine theta_ge (by norm_num) anchorW_ok.1 ?_
  have h := (Rat.cast_le (K := ℝ)).mpr anchorW_ok.2
  push_cast at h
  linarith

theorem log_three_le : Real.log 3 ≤ ((-lLo (1 / 3) : ℚ) : ℝ) := by
  obtain ⟨h1, -⟩ := ptOk_sound logs_ok.1
  have e : ((1 / 3 : ℚ) : ℝ) = (3 : ℝ)⁻¹ := by push_cast; ring
  rw [e, Real.log_inv] at h1
  push_cast
  linarith

theorem log_1281_le : Real.log (1281 / 640) ≤ ((-lLo (640 / 1281) : ℚ) : ℝ) := by
  obtain ⟨h1, -⟩ := ptOk_sound logs_ok.2.1
  have e : ((640 / 1281 : ℚ) : ℝ) = ((1281 : ℝ) / 640)⁻¹ := by push_cast; ring
  rw [e, Real.log_inv] at h1
  push_cast
  linarith

/-- `log 2000 ≥ 15/2`. -/
theorem log_2000_ge : (15 / 2 : ℝ) ≤ Real.log 2000 := by
  obtain ⟨-, h2, -, -⟩ := ptOk_sound logs_ok.2.2.1
  have hl := logs_ok.2.2.2.2.2.2.2.1
  have hlR : ((lHi (1 / 2000) : ℚ) : ℝ) ≤ -15 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hl
    push_cast at h
    linarith
  have e : ((1 / 2000 : ℚ) : ℝ) = (2000 : ℝ)⁻¹ := by push_cast; ring
  rw [e, Real.log_inv] at h2
  linarith

/-! ## Profile bound for small contacts -/

theorem neg_log_one_sub_le {v : ℝ} (hv1 : v < 1) :
    -Real.log (1 - v) ≤ v / (1 - v) := by
  have hpos : 0 < 1 - v := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have e : (1 - v)⁻¹ - 1 = v / (1 - v) := by field_simp; ring
  linarith

theorem profile_le_small {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 2000) : profile v ≤ 81 / 50 := by
  set L := -Real.log v with hLdef
  have hv1 : v < 1 := by linarith
  have hL : 15 / 2 ≤ L := by
    have h1 : Real.log v ≤ Real.log (1 / 2000) := Real.log_le_log hv0 hv
    have h2 : Real.log (1 / 2000 : ℝ) = -Real.log 2000 := by
      rw [one_div, Real.log_inv]
    have := log_2000_ge
    rw [hLdef]; linarith
  have hc0 : 0 ≤ -Real.log (1 - v) := by
    have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - v) (by linarith : 1 - v ≤ 1)
    linarith
  have hc1 : -Real.log (1 - v) ≤ 2 * v := by
    have h := neg_log_one_sub_le hv1
    have h2 : v / (1 - v) ≤ 2 * v := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  -- hn bounds
  have hhn : hn v = v * L + (1 - v) * (-Real.log (1 - v)) := by
    unfold hn; rw [hLdef]; ring
  have hhn0 : v * L ≤ hn v := by
    rw [hhn]; have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - v) hc0; linarith
  have hhn1 : hn v ≤ v * (L + 1) := by
    rw [hhn]
    have h : (1 - v) * (-Real.log (1 - v)) ≤ v := by
      have := neg_log_one_sub_le hv1
      have hp : 0 < 1 - v := by linarith
      calc (1 - v) * (-Real.log (1 - v)) ≤ (1 - v) * (v / (1 - v)) :=
            mul_le_mul_of_nonneg_left this hp.le
        _ = v := by field_simp
    nlinarith
  -- kap bounds
  have hk : kap v = (L + (-Real.log (1 - v))) / 2 := by
    unfold kap; rw [Real.log_mul hv0.ne' (by linarith), hLdef]; ring
  have hk0 : L / 2 ≤ kap v := by rw [hk]; linarith
  have hkpos : 0 < kap v := by linarith
  have hG1 : 2 * kap v - (1 - 2 * v) ^ 2 ≤ L - 997 / 1000 := by
    rw [hk]; nlinarith
  have hG0 : 0 ≤ 2 * kap v - (1 - 2 * v) ^ 2 := by
    rw [hk]; nlinarith
  -- numerator and denominator
  have hnum : 2 * (1 - 2 * v) * (hn v) ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) ≤
      2 * (v * (L + 1)) ^ 2 * (L - 997 / 1000) := by
    have h1 : (hn v) ^ 2 ≤ (v * (L + 1)) ^ 2 :=
      pow_le_pow_left₀ (le_trans (by positivity) hhn0) hhn1 2
    have h2 : 0 ≤ (hn v) ^ 2 := sq_nonneg _
    have h3 : (1 - 2 * v) ≤ 1 := by linarith
    have h4 : 0 ≤ 1 - 2 * v := by linarith
    have hA : (1 - 2 * v) * (hn v) ^ 2 ≤ (v * (L + 1)) ^ 2 := by
      calc (1 - 2 * v) * (hn v) ^ 2 ≤ 1 * (hn v) ^ 2 := mul_le_mul_of_nonneg_right h3 h2
        _ ≤ (v * (L + 1)) ^ 2 := by linarith
    have hB := mul_le_mul hA hG1 hG0 (sq_nonneg _)
    nlinarith [hB]
  have hL2 := log_two_pos
  have hden : 2 * Real.log 2 * (1999 / 2000) ^ 2 * v ^ 2 * L ^ 3 ≤
      Real.log 2 * (4 * v * (1 - v)) ^ 2 * (kap v) ^ 3 := by
    have h1 : (4 * v * (1999 / 2000)) ^ 2 ≤ (4 * v * (1 - v)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    have h2 : (L / 2) ^ 3 ≤ (kap v) ^ 3 := pow_le_pow_left₀ (by linarith) hk0 3
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 hL2.le
    nlinarith [h4]
  have hdenpos : 0 < Real.log 2 * (4 * v * (1 - v)) ^ 2 * (kap v) ^ 3 := by
    have : 0 < 4 * v * (1 - v) := by nlinarith
    positivity
  have hpoly : 2 * (v * (L + 1)) ^ 2 * (L - 997 / 1000) ≤
      81 / 50 * (2 * Real.log 2 * (1999 / 2000) ^ 2 * v ^ 2 * L ^ 3) := by
    have hl2 : (6931 / 10000 : ℝ) < Real.log 2 := by
      have hq : (6931 / 10000 : ℚ) < LqLo := by decide +kernel
      have hqR : (6931 / 10000 : ℝ) < ((LqLo : ℚ) : ℝ) := by
        have h := (Rat.cast_lt (K := ℝ)).mpr hq
        push_cast at h
        linarith
      linarith [LqLo_le']
    have hv2 : 0 < v ^ 2 := by positivity
    have hP : (L + 1) ^ 2 * (L - 997 / 1000) ≤ 81 / 50 * (6931 / 10000) * (1999 / 2000) ^ 2 * L ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hL),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hL)) (sub_nonneg.mpr hL)]
    have hQ : 81 / 50 * (6931 / 10000) * (1999 / 2000) ^ 2 * L ^ 3 ≤
        81 / 50 * Real.log 2 * (1999 / 2000) ^ 2 * L ^ 3 := by
      have : 0 ≤ L ^ 3 := by positivity
      nlinarith
    have hR := mul_le_mul_of_nonneg_left (hP.trans hQ) (show (0 : ℝ) ≤ 2 * v ^ 2 by positivity)
    nlinarith [hR]
  unfold profile
  rw [div_le_iff₀ hdenpos]
  nlinarith [hnum, hden, hpoly]

/-! ## Increment bound on `[128, ∞)` -/

theorem contact_small_of_ge {x : ℝ} (hx : 128 ≤ x) : radialContact (2 * x) 1 ≤ 1 / 2000 := by
  have hHlo := (H_bounds logs_ok.2.2.1).1
  have hc := logs_ok.2.2.2.2.2.2.1
  have hcR : (1999 / 2000 : ℝ) ≤ 256 * ((Hlo (1 / 2000) : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at h
    linarith
  apply (radialContact_le_iff (by positivity) (by norm_num) (by norm_num) (by norm_num)).2
  have e : ((1 / 2000 : ℚ) : ℝ) = 1 / 2000 := by push_cast; ring
  rw [e] at hHlo
  have hH0 : 0 ≤ H (1 / 2000 : ℝ) := H_nonneg (by norm_num) (by norm_num)
  nlinarith

theorem mul_deriv_theta_le_tail {x : ℝ} (hx : 128 ≤ x) : x * deriv e8Theta x ≤ 81 / 50 := by
  have hxpos : 0 < x := by linarith
  rw [deriv_e8Theta_eq_profile hxpos]
  have hv0 := radialContact_pos (show (0 : ℝ) < 2 * x by positivity) (by norm_num : (0 : ℝ) < 1)
  have hp := profile_le_small hv0 (contact_small_of_ge hx)
  have e : x * (profile (radialContact (2 * x) 1) / x) = profile (radialContact (2 * x) 1) := by
    field_simp
  rw [e]
  exact hp

theorem theta_increment_tail {x y : ℝ} (hx : 128 ≤ x) (hxy : x ≤ y) :
    e8Theta y - e8Theta x ≤ (81 / 50) * Real.log (y / x) := by
  have hmono : MonotoneOn (fun t : ℝ => (81 / 50) * Real.log t - e8Theta t) (Set.Ici 128) := by
    have hd : ∀ t : ℝ, 0 < t →
        HasDerivAt (fun s : ℝ => (81 / 50) * Real.log s - e8Theta s)
          ((81 / 50) * t⁻¹ - deriv e8Theta t) t := by
      intro t ht
      exact ((Real.hasDerivAt_log ht.ne').const_mul (81 / 50)).sub
        (hasDerivAt_e8Theta ht).differentiableAt.hasDerivAt
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 128)
    · intro t ht
      exact (hd t (by linarith [Set.mem_Ici.mp ht])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hd t (by linarith [Set.mem_Ioi.mp ht])).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : 128 < t := Set.mem_Ioi.mp ht
      have htpos : 0 < t := by linarith
      have h := mul_deriv_theta_le_tail ht'.le
      have hdiv : deriv e8Theta t ≤ (81 / 50) * t⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ htpos]
        linarith
      linarith
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hm := hmono (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxy)) hxy
  simp only at hm
  rw [Real.log_div hypos.ne' hxpos.ne']
  linarith

end CKLaneN1.Capital

end


