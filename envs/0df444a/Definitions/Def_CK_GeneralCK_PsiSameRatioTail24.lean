-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameRatioTail24
-- name    : CK_GeneralCK_PsiSameRatioTail24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T09:44:02.165027+00:00
-- url     : https://prove2.me/theorems/262fbb87-cc9f-4b42-a412-580ea35c41e3
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameRatioTail24` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameRatioTail24` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameRatioTail24` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameRatioTail24 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameRatioTail24.lean)

import Definitions.Def_CK_GeneralCK_PsiSameRatioTail

-- ===== source module GeneralCK.PsiSameRatioTail24 =====
section

/-! A larger same-side ratio tail, covering `a/b≤2⁻²⁴` for every entropy split. -/

namespace GeneralCK
open Set
namespace PsiSameRatioTail24

private theorem log_10000_7499_upper : Real.log (10000 / 7499 : ℝ) ≤ 36 / 125 := by
  have h := Certificates.checkLog_sound (w := (2501 / 17499)) (n := 5)
    (lo := 0) (hi := 36 / 125)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.2

private theorem log_35_32_upper : Real.log (35 / 32 : ℝ) ≤ 9 / 100 := by
  have h := Certificates.checkLog_sound (w := (3 / 67)) (n := 3)
    (lo := 0) (hi := 9 / 100)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.2

private theorem log_35_34_upper : Real.log (35 / 34 : ℝ) ≤ 29 / 1000 := by
  have h := Certificates.checkLog_sound (w := (1 / 69)) (n := 3)
    (lo := 0) (hi := 29 / 1000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.2

theorem entropy_2501_10000_le : H (2501 / 10000) ≤ (13 / 16 : ℝ) := by
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hq : -Real.log (2501 / 10000 : ℝ) ≤ 2 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 2501 / 10000)
    have he : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1 / 4 : ℝ) = (2 ^ (2 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      norm_num
    rw [he] at h
    linarith
  have hc : -Real.log (1 - (2501 / 10000 : ℝ)) ≤ 36 / 125 := by
    rw [show 1 - (2501 / 10000 : ℝ) = (10000 / 7499)⁻¹ by norm_num,
      Real.log_inv, neg_neg]
    exact log_10000_7499_upper
  have he := Certificates.SmallMean.entropy_log_identity (2501 / 10000)
  have hH := H_nonneg (p := (2501 / 10000 : ℝ)) (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hL hH
  nlinarith

theorem entropy_1_35_le : H (1 / 35) ≤ (3 / 16 : ℝ) := by
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hq : -Real.log (1 / 35 : ℝ) ≤ 5 * Real.log 2 + 9 / 100 := by
    rw [show (1 / 35 : ℝ) = ((2 : ℝ) ^ (5 : ℕ) * (35 / 32))⁻¹ by norm_num,
      Real.log_inv, neg_neg, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have h := log_35_32_upper
    norm_num
    linarith
  have hc : -Real.log (1 - (1 / 35 : ℝ)) ≤ 29 / 1000 := by
    rw [show 1 - (1 / 35 : ℝ) = (35 / 34)⁻¹ by norm_num,
      Real.log_inv, neg_neg]
    exact log_35_34_upper
  have he := Certificates.SmallMean.entropy_log_identity (1 / 35)
  have hH := H_nonneg (p := (1 / 35 : ℝ)) (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hL hH
  nlinarith

theorem slope_at_threshold_le : deriv Scalar.P (1 - H (1 / 35)) ≤ (12 : ℝ) := by
  have hh : 0 < H (1 / 35) := H_pos (by norm_num) (by norm_num)
  have hi : 0 < 1 - H (1 / 35) := by linarith [entropy_1_35_le]
  have hi' : 1 - H (1 / 35) < 1 := by linarith
  rw [Scalar.deriv_P hi hi', sub_sub_cancel,
    entropyInverse_H_lower (by norm_num) (by norm_num)]
  have hlog : (69 / 20 : ℝ) < Real.log 34 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 32) (by norm_num : (32 : ℝ) ≤ 34)
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at h
    norm_num at h
    nlinarith [Certificates.Mixed.log_two_gt_69]
  have he : Real.log 2 * (1 / 35) * (1 - 1 / 35) * J (1 / 35) =
      (34 / 1225) * Real.log 34 := by
    unfold J
    norm_num
    field_simp [log_two_pos.ne']
    norm_num
  rw [he]
  have hd : 0 < (34 / 1225 : ℝ) * Real.log 34 := by positivity
  have hfrac : (1 - 2 * (1 / 35 : ℝ)) / ((34 / 1225) * Real.log 34) ≤ 10 := by
    apply (div_le_iff₀ hd).2
    linarith
  linarith

theorem slope_le_twelve {I m : ℝ} (hI : 0 < I) (hIm : I ≤ H m)
    (hm : 0 ≤ m) (hm' : m ≤ 2501/10000) : deriv Scalar.P I ≤ 12 := by
  have hH : H m ≤ H (2501/10000) := H_strictMonoOn.monotoneOn
    ⟨hm, by linarith⟩ ⟨by norm_num, by norm_num⟩ hm'
  have hcap : I ≤ 1-H (1/35) := by
    linarith [entropy_2501_10000_le, entropy_1_35_le]
  have ht0 : 0 < 1-H (1/35) := by linarith [entropy_1_35_le]
  have ht1 : 1-H (1/35) < 1 := by
    linarith [H_pos (p := (1/35 : ℝ)) (by norm_num) (by norm_num)]
  have hconv : ConvexOn ℝ (Ioo 0 1) Scalar.P :=
    Scalar.P_convexOn.subset Ioo_subset_Ico_self (convex_Ioo _ _)
  have hmono := hconv.monotoneOn_deriv (fun x hx =>
    (Scalar.hasDerivAt_P hx.1 hx.2).differentiableAt)
  have h := hmono ⟨hI, lt_of_le_of_lt hcap ht1⟩ ⟨ht0, ht1⟩ hcap
  exact h.trans slope_at_threshold_le

theorem ratio_tail_cost {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hr : a/b ≤ 1/16777216) :
    12*(b-a) ≤ interiorCost a b := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := hab.trans_lt hb
  have hratio : (2:ℝ)^24 ≤ b/a := by
    have hr' := (div_le_iff₀ hb0).mp hr
    apply (le_div_iff₀ ha).mpr
    norm_num
    linarith
  have hl := Real.log_le_log (show (0:ℝ) < 2^24 by positivity) hratio
  rw [Real.log_pow] at hl
  have hc : 0 ≤ Real.log (1-a)-Real.log (1-b) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have he : J a-J b = (Real.log (b/a)+(Real.log (1-a)-Real.log (1-b)))/Real.log 2 := by
    unfold J
    rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) hb0.ne',
      Real.log_div hb0.ne' ha.ne']
    ring
  have hj : (24 : ℝ) ≤ J a-J b := by
    rw [he]
    apply (le_div_iff₀ log_two_pos).mpr
    norm_num at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ b-a by linarith)
  unfold interiorCost
  nlinarith only [hm]

end PsiSameRatioTail24

namespace InteriorLaw
theorem same_ratio_tail24_splitBound {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1/2)
    (hr : μ.a/μ.b ≤ 1/16777216) : μ.splitBound ≤ μ.cost := by
  have ha0 := μ.a_interior.1
  have hb0 := μ.b_interior.1
  have hm0 : 0 ≤ μ.midpoint := by
    unfold midpoint
    linarith
  have hm : μ.midpoint ≤ 2501/10000 := by
    have hr' := (div_le_iff₀ hb0).mp hr
    unfold midpoint
    linarith
  have hIm : μ.information ≤ H μ.midpoint := by
    unfold information meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hd : μ.entropyDrop ≤ μ.b-μ.a :=
    PsiSameRatioTail.entropy_drop_le_difference ha0 hab μ.b_interior.2
  have hcost : 12*(μ.b-μ.a) ≤ interiorCost μ.a μ.b :=
    PsiSameRatioTail24.ratio_tail_cost ha0 hab μ.b_interior.2 hr
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
    have hs : deriv Scalar.P μ.information ≤ 12 :=
      PsiSameRatioTail24.slope_le_twelve hIp hIm hm0 hm
    have hinc := Scalar.P_increment_upper μ.meanDeficit_mem.1
      (show μ.meanDeficit ≤ μ.information by
        rw [μ.information_eq]
        linarith [μ.entropyDrop_nonneg]) hIp hi.2
    rw [μ.information_eq] at hinc
    have hmul := mul_le_mul_of_nonneg_left hs μ.entropyDrop_nonneg
    rw [μ.information_eq] at hmul
    have hsbound : μ.splitBound ≤ interiorCost μ.a μ.b := by
      unfold splitBound
      nlinarith only [hinc, hmul, hd, hcost]
    exact hsbound.trans
      ((μ.interiorCost_le_psiLogSumCostFloor).trans μ.psiLogSumCostFloor_le_cost)

end InteriorLaw

/-- The enlarged same-side tail is closed for actual finite laws and every
feasible entropy allocation. The previous `2⁻³²` owner remains unchanged. -/
theorem sameSidePsiRatioTail24Owner {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1 / 2)
    (hr : μ.a / μ.b ≤ 1 / 16777216)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_splitBound hactive (μ.same_ratio_tail24_splitBound hab hb hr)

end GeneralCK

#print axioms GeneralCK.PsiSameRatioTail24.slope_le_twelve
#print axioms GeneralCK.InteriorLaw.same_ratio_tail24_splitBound
#print axioms GeneralCK.sameSidePsiRatioTail24Owner

end


