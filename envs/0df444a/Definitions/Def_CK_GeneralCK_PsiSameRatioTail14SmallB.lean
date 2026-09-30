-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameRatioTail14SmallB
-- name    : CK_GeneralCK_PsiSameRatioTail14SmallB
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:19:19.822269+00:00
-- url     : https://prove2.me/theorems/f95f1639-b91e-47c7-8d03-87814fac90cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameRatioTail14SmallB` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameRatioTail14SmallB` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameRatioTail14SmallB` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameRatioTail14SmallB (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameRatioTail14SmallB.lean)

import Definitions.Def_CK_GeneralCK_PsiSameRatioTail15
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanLeaves

-- ===== source module GeneralCK.PsiSameRatioTail14SmallB =====
section

/-!
# A ratio-fourteen same-side subregion

For `b≤39/100`, the same-side midpoint is at most `1/5` when
`a/b≤2⁻¹⁴`. Exact integer-power comparisons and existing checked entropy
bounds place the information-profile slope below `56/5`. Together with
the checked `5/8` entropy-drop bound, this matches the seven-unit odds cost.
-/

namespace GeneralCK
open Set
namespace PsiSameRatioTail14SmallB

theorem entropy_one_fifth_le : H (1 / 5) ≤ (3 / 4 : ℝ) := by
  have hpow : (5 : ℝ) ^ (20 : ℕ) ≤ (2 : ℝ) ^ (47 : ℕ) := by norm_num
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (5 : ℝ) ^ (20 : ℕ)) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have he := Certificates.SmallMean.entropy_log_identity (1 / 5)
  have h5 : -Real.log (1 / 5 : ℝ) = Real.log 5 := by
    rw [show (1 / 5 : ℝ) = (5 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  have h4 : -Real.log (1 - (1 / 5 : ℝ)) = Real.log 5 - 2 * Real.log 2 := by
    rw [show 1 - (1 / 5 : ℝ) = (4 : ℝ) / 5 by norm_num,
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    ring
  rw [h5, h4] at he
  have hbound : H (1 / 5) * Real.log 2 ≤ (3 / 4) * Real.log 2 := by
    nlinarith only [he, hlog]
  have hbound' : Real.log 2 * H (1 / 5) ≤ Real.log 2 * (3 / 4) := by
    simpa only [mul_comm] using hbound
  exact (mul_le_mul_iff_right₀ log_two_pos).mp hbound'

theorem log_thirty_one_lower : (3381 / 1000 : ℝ) < Real.log 31 := by
  have hpow : (2 : ℝ) ^ (49 : ℕ) ≤ (31 : ℝ) ^ (10 : ℕ) := by norm_num
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (49 : ℕ)) hpow
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  have h2 := Certificates.Mixed.log_two_gt_69
  nlinarith only [h, h2]

theorem slope_at_anchor_le :
    deriv Scalar.P (1 - H (1 / 32)) ≤ (56 / 5 : ℝ) := by
  have hh : 0 < H (1 / 32) := H_pos (by norm_num) (by norm_num)
  have hi : 0 < 1 - H (1 / 32) := by
    linarith [Certificates.SmallMean.entropy_one_over_32_lt]
  have hi' : 1 - H (1 / 32) < 1 := by linarith
  rw [Scalar.deriv_P hi hi', sub_sub_cancel,
    entropyInverse_H_lower (by norm_num) (by norm_num)]
  have he : Real.log 2 * (1 / 32) * (1 - 1 / 32) * J (1 / 32) =
      (31 / 1024) * Real.log 31 := by
    unfold J
    norm_num
    field_simp [log_two_pos.ne']
    norm_num
  rw [he]
  have hd : 0 < (31 / 1024 : ℝ) * Real.log 31 := by positivity
  have hfrac : (1 - 2 * (1 / 32 : ℝ)) / ((31 / 1024) * Real.log 31) ≤ 46 / 5 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [log_thirty_one_lower]
  linarith

theorem slope_le {I m : ℝ} (hI : 0 < I) (hIm : I ≤ H m)
    (hm : 0 ≤ m) (hm' : m ≤ 1 / 5) : deriv Scalar.P I ≤ 56 / 5 := by
  have hH : H m ≤ H (1 / 5) := H_strictMonoOn.monotoneOn
    ⟨hm, by linarith⟩ ⟨by norm_num, by norm_num⟩ hm'
  have hcap : I ≤ 1 - H (1 / 32) := by
    linarith [entropy_one_fifth_le, Certificates.SmallMean.entropy_one_over_32_lt]
  have ht0 : 0 < 1 - H (1 / 32) := by
    linarith [Certificates.SmallMean.entropy_one_over_32_lt]
  have ht1 : 1 - H (1 / 32) < 1 := by
    linarith [H_pos (p := (1 / 32 : ℝ)) (by norm_num) (by norm_num)]
  have hconv : ConvexOn ℝ (Ioo 0 1) Scalar.P :=
    Scalar.P_convexOn.subset Ioo_subset_Ico_self (convex_Ioo _ _)
  have hmono := hconv.monotoneOn_deriv (fun x hx =>
    (Scalar.hasDerivAt_P hx.1 hx.2).differentiableAt)
  have h := hmono ⟨hI, lt_of_le_of_lt hcap ht1⟩ ⟨ht0, ht1⟩ hcap
  exact h.trans slope_at_anchor_le

theorem ratio_tail_cost {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hr : a / b ≤ 1 / 16384) :
    7 * (b - a) ≤ interiorCost a b := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := hab.trans_lt hb
  have hratio : (2 : ℝ) ^ (14 : ℕ) ≤ b / a := by
    have hr' := (div_le_iff₀ hb0).mp hr
    apply (le_div_iff₀ ha).mpr
    norm_num
    linarith
  have hl := Real.log_le_log (show (0 : ℝ) < 2 ^ (14 : ℕ) by positivity) hratio
  rw [Real.log_pow] at hl
  have hc : 0 ≤ Real.log (1 - a) - Real.log (1 - b) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have he : J a - J b =
      (Real.log (b / a) + (Real.log (1 - a) - Real.log (1 - b))) / Real.log 2 := by
    unfold J
    rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) hb0.ne',
      Real.log_div hb0.ne' ha.ne']
    ring
  have hj : (14 : ℝ) ≤ J a - J b := by
    rw [he]
    apply (le_div_iff₀ log_two_pos).mpr
    norm_num at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ b - a by linarith)
  unfold interiorCost
  nlinarith only [hm]

end PsiSameRatioTail14SmallB

namespace InteriorLaw
theorem same_ratio_tail14_smallB_splitBound {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 39 / 100)
    (hr : μ.a / μ.b ≤ 1 / 16384) : μ.splitBound ≤ μ.cost := by
  have ha0 := μ.a_interior.1
  have hb0 := μ.b_interior.1
  have hm0 : 0 ≤ μ.midpoint := by
    unfold midpoint
    linarith
  have hm : μ.midpoint ≤ 1 / 5 := by
    have hr' := (div_le_iff₀ hb0).mp hr
    unfold midpoint
    linarith
  have hIm : μ.information ≤ H μ.midpoint := by
    unfold information meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hd : μ.entropyDrop ≤ (5 / 8) * (μ.b - μ.a) :=
    PsiSameRatioTail15.entropy_drop_le_five_eighths ha0 hab
      (by linarith : μ.b ≤ 1 / 2)
  have hcost : 7 * (μ.b - μ.a) ≤ interiorCost μ.a μ.b :=
    PsiSameRatioTail14SmallB.ratio_tail_cost ha0 hab μ.b_interior.2 hr
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
    have hs : deriv Scalar.P μ.information ≤ 56 / 5 :=
      PsiSameRatioTail14SmallB.slope_le hIp hIm hm0 hm
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

theorem sameSidePsiRatioTail14SmallBOwner {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 39 / 100)
    (hr : μ.a / μ.b ≤ 1 / 16384)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_splitBound hactive (μ.same_ratio_tail14_smallB_splitBound hab hb hr)

end GeneralCK

#print axioms GeneralCK.PsiSameRatioTail14SmallB.entropy_one_fifth_le
#print axioms GeneralCK.PsiSameRatioTail14SmallB.log_thirty_one_lower
#print axioms GeneralCK.PsiSameRatioTail14SmallB.slope_le
#print axioms GeneralCK.InteriorLaw.same_ratio_tail14_smallB_splitBound
#print axioms GeneralCK.sameSidePsiRatioTail14SmallBOwner

end


