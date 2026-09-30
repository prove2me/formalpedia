-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameRatioTail8SmallMean
-- name    : CK_GeneralCK_PsiSameRatioTail8SmallMean
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:19:22.784598+00:00
-- url     : https://prove2.me/theorems/ad34e03d-54ce-4088-a15d-d7ccd9356e09
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameRatioTail8SmallMean` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameRatioTail8SmallMean` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameRatioTail8SmallMean` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameRatioTail8SmallMean (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameRatioTail8SmallMean.lean)

import Definitions.Def_CK_GeneralCK_PsiSameRatioTail15
import Definitions.Def_CK_GeneralCK_PsiNormalizedLowEntropy

-- ===== source module GeneralCK.PsiSameRatioTail8SmallMean =====
section

/-!
# A two-child ratio-eight strip at small midpoint

The inverse-entropy anchor `1/12` bounds the information-profile slope by
seven for midpoint at most `1/8`. A sharper entropy-chain estimate bounds
the entropy drop by `9(b-a)/16`. This fits the four-unit odds cost whenever
`a/b ≤ 1/256`. Both child Psi profiles enter through `splitBound`.
-/

namespace GeneralCK
open Set
namespace PsiSameRatioTail8SmallMean

theorem entropy_twelfth_le : H (1 / 12) ≤ (4 / 9 : ℝ) := by
  have hpow : (12 : ℝ) ^ (5 : ℕ) ≤ (2 : ℝ) ^ (18 : ℕ) := by norm_num
  have hl := Real.log_le_log
    (show (0 : ℝ) < (12 : ℝ) ^ (5 : ℕ) by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  have he := H_mul_log_two_le (p := (1 / 12 : ℝ)) (by norm_num) (by norm_num)
  norm_num only [one_div, inv_inv] at he
  have htwo := Certificates.Mixed.log_two_gt_69
  have hbound : H (1 / 12) * Real.log 2 ≤ (4 / 9) * Real.log 2 := by
    nlinarith only [he, hl, htwo]
  exact (mul_le_mul_iff_left₀ log_two_pos).mp hbound

theorem log_eleven_lower : (23 / 10 : ℝ) < Real.log 11 := by
  have hpow : (2 : ℝ) ^ (10 : ℕ) ≤ (11 : ℝ) ^ (3 : ℕ) := by norm_num
  have hl := Real.log_le_log
    (show (0 : ℝ) < (2 : ℝ) ^ (10 : ℕ) by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  nlinarith only [hl, Certificates.Mixed.log_two_gt_69]

theorem slope_at_anchor_le :
    deriv Scalar.P (1 - H (1 / 12)) ≤ (7 : ℝ) := by
  have hh : 0 < H (1 / 12) := H_pos (by norm_num) (by norm_num)
  have hi : 0 < 1 - H (1 / 12) := by linarith [entropy_twelfth_le]
  have hi' : 1 - H (1 / 12) < 1 := by linarith
  rw [Scalar.deriv_P hi hi', sub_sub_cancel,
    entropyInverse_H_lower (by norm_num) (by norm_num)]
  have he : Real.log 2 * (1 / 12) * (1 - 1 / 12) * J (1 / 12) =
      (11 / 144) * Real.log 11 := by
    unfold J
    norm_num
    field_simp [log_two_pos.ne']
    norm_num
  rw [he]
  have hd : 0 < (11 / 144 : ℝ) * Real.log 11 := by positivity
  have hfrac : (1 - 2 * (1 / 12 : ℝ)) /
      ((11 / 144) * Real.log 11) ≤ 5 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [log_eleven_lower]
  linarith

theorem slope_le {I m : ℝ} (hI : 0 < I) (hIm : I ≤ H m)
    (hm : 0 ≤ m) (hm' : m ≤ 1 / 8) : deriv Scalar.P I ≤ 7 := by
  have hH : H m ≤ H (1 / 8) := H_strictMonoOn.monotoneOn
    ⟨hm, by linarith⟩ ⟨by norm_num, by norm_num⟩ hm'
  have hcap : I ≤ 1 - H (1 / 12) := by
    linarith [H_eighth_le, entropy_twelfth_le]
  have ht0 : 0 < 1 - H (1 / 12) := by linarith [entropy_twelfth_le]
  have ht1 : 1 - H (1 / 12) < 1 := by
    linarith [H_pos (p := (1 / 12 : ℝ)) (by norm_num) (by norm_num)]
  have hconv : ConvexOn ℝ (Ioo 0 1) Scalar.P :=
    Scalar.P_convexOn.subset Ioo_subset_Ico_self (convex_Ioo _ _)
  have hmono := hconv.monotoneOn_deriv (fun x hx =>
    (Scalar.hasDerivAt_P hx.1 hx.2).differentiableAt)
  exact (hmono ⟨hI, lt_of_le_of_lt hcap ht1⟩ ⟨ht0, ht1⟩ hcap).trans
    slope_at_anchor_le

theorem entropy_drop_le_nine_sixteenths {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hsum : a + b ≤ 1 / 4) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ (9 / 16) * (b - a) := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hbalance : 6 * (b - a) ≤ 2 - a - b := by linarith
  have hratio : 0 ≤ (b - a) / (2 - a - b) ∧
      (b - a) / (2 - a - b) ≤ 1 / 3 := by
    constructor
    · positivity
    · apply (div_le_iff₀ ht).mpr
      linarith
  have hp := PsiSameRatioTail.entropy_chord (p := a / (a + b)) (by positivity)
    ((div_le_iff₀ hs).mpr (by linarith))
  have hp' := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (a + b) / 2 by linarith)
  have hep : ((a + b) / 2) * (2 * (a / (a + b))) = a := by field_simp
  rw [hep] at hp'
  have hposterior : (1 - b) / (2 - a - b) =
      (1 - (b - a) / (2 - a - b)) / 2 := by
    field_simp
    ring
  have hcap := PsiSameRatioTail15.biasDeficit_le_three_quarters_sq hratio.1 hratio.2
  rw [PsiSmallDistance.biasDeficit_eq] at hcap
  have hsecond := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ 1 - (a + b) / 2 by linarith)
  have hprod := mul_le_mul_of_nonneg_left hbalance hd
  have hsecondBound :
      (1 - (a + b) / 2) *
          (1 - H ((1 - (b - a) / (2 - a - b)) / 2)) ≤ (b - a) / 16 := by
    have hident :
        (1 - (a + b) / 2) *
          ((3 / 4) * ((b - a) / (2 - a - b)) ^ 2) =
          (3 / 4) * ((b - a) ^ 2 / (2 * (2 - a - b))) := by
      field_simp
      ring
    rw [hident] at hsecond
    have hden : 0 < 2 * (2 - a - b) := by positivity
    have hfrac : (b - a) ^ 2 / (2 * (2 - a - b)) ≤ (b - a) / 12 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hprod]
    have hscaled := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ) ≤ 3 / 4)
    nlinarith only [hsecond, hscaled]
  rw [← hposterior] at hsecondBound
  rw [deterministic_entropy_chain ha ha1 hb0 hb1]
  nlinarith only [hp', hsecondBound]

theorem ratio_tail_cost {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hr : a / b ≤ 1 / 256) :
    4 * (b - a) ≤ interiorCost a b := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := hab.trans_lt hb
  have hratio : (2 : ℝ) ^ (8 : ℕ) ≤ b / a := by
    have hr' := (div_le_iff₀ hb0).mp hr
    apply (le_div_iff₀ ha).mpr
    norm_num
    linarith
  have hl := Real.log_le_log
    (show (0 : ℝ) < 2 ^ (8 : ℕ) by positivity) hratio
  rw [Real.log_pow] at hl
  have hc : 0 ≤ Real.log (1 - a) - Real.log (1 - b) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have he : J a - J b =
      (Real.log (b / a) + (Real.log (1 - a) - Real.log (1 - b))) / Real.log 2 := by
    unfold J
    rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) hb0.ne',
      Real.log_div hb0.ne' ha.ne']
    ring
  have hj : (8 : ℝ) ≤ J a - J b := by
    rw [he]
    apply (le_div_iff₀ log_two_pos).mpr
    norm_num at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ b - a by linarith)
  unfold interiorCost
  nlinarith only [hm]

end PsiSameRatioTail8SmallMean

namespace InteriorLaw

theorem same_ratio_tail8_smallMean_splitBound {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b ≤ 1 / 4)
    (hr : μ.a / μ.b ≤ 1 / 256) : μ.splitBound ≤ μ.cost := by
  have ha0 := μ.a_interior.1
  have hb0 := μ.b_interior.1
  have hm0 : 0 ≤ μ.midpoint := by unfold midpoint; linarith
  have hm : μ.midpoint ≤ 1 / 8 := by unfold midpoint; linarith
  have hIm : μ.information ≤ H μ.midpoint := by
    unfold information meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hd : μ.entropyDrop ≤ (9 / 16) * (μ.b - μ.a) :=
    PsiSameRatioTail8SmallMean.entropy_drop_le_nine_sixteenths ha0 hab hsum
  have hcost : 4 * (μ.b - μ.a) ≤ interiorCost μ.a μ.b :=
    PsiSameRatioTail8SmallMean.ratio_tail_cost ha0 hab μ.b_interior.2 hr
  have hi := μ.information_mem
  by_cases hIz : μ.information = 0
  · have hd0 : μ.entropyDrop = 0 := by
      rw [μ.information_eq] at hIz
      linarith [μ.entropyDrop_nonneg, μ.meanDeficit_mem.1]
    have hnonneg : 0 ≤ μ.cost := by
      have hc := (μ.interiorCost_le_psiLogSumCostFloor).trans μ.psiLogSumCostFloor_le_cost
      linarith
    simpa [splitBound, hd0] using hnonneg
  · have hIp : 0 < μ.information := lt_of_le_of_ne hi.1 (Ne.symm hIz)
    have hs : deriv Scalar.P μ.information ≤ 7 :=
      PsiSameRatioTail8SmallMean.slope_le hIp hIm hm0 hm
    have hinc := Scalar.P_increment_upper μ.meanDeficit_mem.1
      (show μ.meanDeficit ≤ μ.information by
        rw [μ.information_eq]
        linarith [μ.entropyDrop_nonneg]) hIp hi.2
    rw [μ.information_eq] at hinc
    have hmul := mul_le_mul_of_nonneg_left hs μ.entropyDrop_nonneg
    rw [μ.information_eq] at hmul
    have hsbound : μ.splitBound ≤ interiorCost μ.a μ.b := by
      unfold splitBound
      nlinarith only [hinc, hmul, hd, hcost, sub_nonneg.mpr hab]
    exact hsbound.trans
      ((μ.interiorCost_le_psiLogSumCostFloor).trans μ.psiLogSumCostFloor_le_cost)

end InteriorLaw

theorem sameSidePsiRatioTail8SmallMeanOwner {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b ≤ 1 / 4)
    (hr : μ.a / μ.b ≤ 1 / 256)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_splitBound hactive (μ.same_ratio_tail8_smallMean_splitBound hab hsum hr)

end GeneralCK

#print axioms GeneralCK.PsiSameRatioTail8SmallMean.entropy_twelfth_le
#print axioms GeneralCK.PsiSameRatioTail8SmallMean.slope_at_anchor_le
#print axioms GeneralCK.PsiSameRatioTail8SmallMean.entropy_drop_le_nine_sixteenths
#print axioms GeneralCK.InteriorLaw.same_ratio_tail8_smallMean_splitBound
#print axioms GeneralCK.sameSidePsiRatioTail8SmallMeanOwner

end


