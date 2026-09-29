-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameRatioTail
-- name    : CK_GeneralCK_PsiSameRatioTail
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T09:34:45.409988+00:00
-- url     : https://prove2.me/theorems/40614dbe-dc9c-4514-b733-e173c319fc8e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameRatioTail` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameRatioTail` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameRatioTail` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameRatioTail (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameRatioTail.lean)

import Definitions.Def_CK_GeneralCK_PsiLogSumOwner
import Definitions.Def_CK_GeneralCK_ScalarGap
import Definitions.Def_CK_GeneralCK_PhysicalSlope
import Definitions.Def_CK_GeneralCK_DeterministicCap
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanBounds
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants

-- ===== source module GeneralCK.PsiSameRatioTail =====
section

/-!
# The complete same-side small-ratio tail

This gives a premise-free owner for `a / b ≤ 2⁻³²`.  The proof uses the
entropy-chain estimate `entropyDrop ≤ b-a`, the log-odds cost estimate
`16*(b-a) ≤ interiorCost a b`, and the profile slope bound `P' ≤ 16` at
all feasible information values.  Fixed logarithms are checked using exact
rational series; no external numerical premise occurs.
-/

namespace GeneralCK
open Set

namespace PsiSameRatioTail

private theorem fixed_log_100_51 : Real.log (100 / 51 : ℝ) ≤ 674/1000 := by
  have h := Certificates.checkLog_sound (w := (49/151)) (n := 8)
    (lo := 0) (hi := 674/1000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.2

private theorem fixed_log_200_149 : Real.log (200 / 149 : ℝ) ≤ 295/1000 := by
  have h := Certificates.checkLog_sound (w := (51/349)) (n := 6)
    (lo := 0) (hi := 295/1000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.2

private theorem fixed_log_5_4 : Real.log (5 / 4 : ℝ) ≤ 224/1000 := by
  have h := Certificates.checkLog_sound (w := (1/9)) (n := 5)
    (lo := 0) (hi := 224/1000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.2

private theorem fixed_log_40_39 : Real.log (40 / 39 : ℝ) ≤ 26/1000 := by
  have h := Certificates.checkLog_sound (w := (1/79)) (n := 3)
    (lo := 0) (hi := 26/1000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.2

theorem entropy_51_200_le : H (51/200) ≤ (83/100 : ℝ) := by
  have hl := Certificates.PilotData.log_two
  norm_num only [div_one] at hl
  have hq : -Real.log (51/200 : ℝ) ≤ 1368/1000 := by
    have he : (51/200 : ℝ) = (2*(100/51))⁻¹ := by norm_num
    rw [he, Real.log_inv, neg_neg, Real.log_mul (by norm_num) (by norm_num)]
    linarith [fixed_log_100_51]
  have hc : -Real.log (1-(51/200 : ℝ)) ≤ 295/1000 := by
    have he : (1-(51/200 : ℝ)) = (200/149)⁻¹ := by norm_num
    rw [he, Real.log_inv, neg_neg]
    exact fixed_log_200_149
  have he := Certificates.SmallMean.entropy_log_identity (51/200)
  have hp := H_nonneg (p := (51/200 : ℝ)) (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hl.1 hp
  nlinarith

theorem entropy_1_40_le : H (1/40) ≤ (17/100 : ℝ) := by
  have hl := Certificates.PilotData.log_two
  norm_num only [div_one] at hl
  have hq : -Real.log (1/40 : ℝ) ≤ 3694/1000 := by
    have he : (1/40 : ℝ) = ((2:ℝ)^5*(5/4))⁻¹ := by norm_num
    rw [he, Real.log_inv, neg_neg, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    linarith [fixed_log_5_4]
  have hc : -Real.log (1-(1/40 : ℝ)) ≤ 26/1000 := by
    have he : (1-(1/40 : ℝ)) = (40/39)⁻¹ := by norm_num
    rw [he, Real.log_inv, neg_neg]
    exact fixed_log_40_39
  have he := Certificates.SmallMean.entropy_log_identity (1/40)
  have hp := H_nonneg (p := (1/40 : ℝ)) (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hl.1 hp
  nlinarith

theorem slope_at_threshold_le :
    deriv Scalar.P (1-H (1/40)) ≤ (16 : ℝ) := by
  have hh : 0 < H (1/40) := H_pos (by norm_num) (by norm_num)
  have hi : 0 < 1-H (1/40) := by linarith [entropy_1_40_le]
  have hi' : 1-H (1/40) < 1 := by linarith
  rw [Scalar.deriv_P hi hi', sub_sub_cancel,
    entropyInverse_H_lower (by norm_num) (by norm_num)]
  have hlog : (3 : ℝ) < Real.log 39 :=
    Certificates.Mixed.log_twenty_one_gt_three.trans_le
      (Real.log_le_log (by norm_num) (by norm_num))
  have he : Real.log 2*(1/40)*(1-1/40)*J (1/40) = (39/1600)*Real.log 39 := by
    unfold J
    norm_num
    field_simp [log_two_pos.ne']
    norm_num
  rw [he]
  have hd : 0 < (39/1600 : ℝ)*Real.log 39 := by positivity
  have hfrac : (1-2*(1/40 : ℝ))/((39/1600)*Real.log 39) ≤ 14 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  linarith

theorem slope_le_sixteen {I m : ℝ} (hI : 0 < I) (hIm : I ≤ H m)
    (hm : 0 ≤ m) (hm' : m ≤ 51/200) : deriv Scalar.P I ≤ 16 := by
  have hH : H m ≤ H (51/200) := H_strictMonoOn.monotoneOn
    ⟨hm, by linarith⟩ ⟨by norm_num, by norm_num⟩ hm'
  have hcap : I ≤ 1-H (1/40) := by
    linarith [entropy_51_200_le, entropy_1_40_le]
  have ht0 : 0 < 1-H (1/40) := by linarith [entropy_1_40_le]
  have ht1 : 1-H (1/40) < 1 := by
    linarith [H_pos (p := (1/40 : ℝ)) (by norm_num) (by norm_num)]
  have hconv : ConvexOn ℝ (Ioo 0 1) Scalar.P :=
    Scalar.P_convexOn.subset Ioo_subset_Ico_self (convex_Ioo _ _)
  have hmono := hconv.monotoneOn_deriv (fun x hx =>
    (Scalar.hasDerivAt_P hx.1 hx.2).differentiableAt)
  have h := hmono ⟨hI, lt_of_le_of_lt hcap ht1⟩ ⟨ht0, ht1⟩ hcap
  exact h.trans slope_at_threshold_le

theorem entropy_chord {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1/2) :
    2*p ≤ H p := by
  have h := Real.strictConcave_binEntropy.concaveOn.2
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1/2 : ℝ) ∈ Icc 0 1 by norm_num)
    (show 0 ≤ 1-2*p by linarith) (show 0 ≤ 2*p by positivity)
    (show (1-2*p)+2*p=1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.binEntropy_zero] at h
  rw [show Real.binEntropy (1/2 : ℝ) = Real.log 2 by
    simpa only [one_div] using Real.binEntropy_two_inv] at h
  have he : 2*p*(1/2 : ℝ)=p := by ring
  rw [he] at h
  unfold H
  exact (le_div_iff₀ log_two_pos).mpr h

theorem entropy_drop_le_difference {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1) :
    H ((a+b)/2)-(H a+H b)/2 ≤ b-a := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := hab.trans_lt hb
  have hs : 0 < a+b := by linarith
  have ht : 0 < 2-a-b := by linarith
  have hp := entropy_chord (p := a/(a+b)) (by positivity)
    ((div_le_iff₀ hs).mpr (by linarith))
  have hq := entropy_chord (p := (1-b)/(2-a-b)) (by positivity)
    ((div_le_iff₀ ht).mpr (by linarith))
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ (a+b)/2 by linarith)
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ 1-(a+b)/2 by linarith)
  have hep : ((a+b)/2)*(2*(a/(a+b))) = a := by field_simp
  have heq : (1-(a+b)/2)*(2*((1-b)/(2-a-b))) = 1-b := by field_simp; ring
  rw [hep] at hp'
  rw [heq] at hq'
  rw [deterministic_entropy_chain ha ha1 hb0 hb]
  nlinarith only [hp', hq']

theorem ratio_tail_cost {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hr : a/b ≤ 1/4294967296) :
    16*(b-a) ≤ interiorCost a b := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := hab.trans_lt hb
  have hratio : (2:ℝ)^32 ≤ b/a := by
    have hr' := (div_le_iff₀ hb0).mp hr
    apply (le_div_iff₀ ha).mpr
    norm_num
    linarith
  have hl := Real.log_le_log (show (0:ℝ) < 2^32 by positivity) hratio
  rw [Real.log_pow] at hl
  have hc : 0 ≤ Real.log (1-a)-Real.log (1-b) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have he : J a-J b = (Real.log (b/a)+(Real.log (1-a)-Real.log (1-b)))/Real.log 2 := by
    unfold J
    rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) hb0.ne',
      Real.log_div hb0.ne' ha.ne']
    ring
  have hj : (32 : ℝ) ≤ J a-J b := by
    rw [he]
    apply (le_div_iff₀ log_two_pos).mpr
    norm_num at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ b-a by linarith)
  unfold interiorCost
  nlinarith only [hm]

end PsiSameRatioTail

namespace InteriorLaw

/-- All entropy splits in the same-side small-ratio tail obey the scalar
comparison, whether or not the parent branch is active. -/
theorem same_ratio_tail_splitBound {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1/2)
    (hr : μ.a/μ.b ≤ 1/4294967296) : μ.splitBound ≤ μ.cost := by
  have ha0 := μ.a_interior.1
  have hb0 := μ.b_interior.1
  have hm0 : 0 ≤ μ.midpoint := by
    unfold midpoint
    linarith
  have hm : μ.midpoint ≤ 51/200 := by
    have hr' := (div_le_iff₀ hb0).mp hr
    unfold midpoint
    linarith
  have hIm : μ.information ≤ H μ.midpoint := by
    unfold information meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hd : μ.entropyDrop ≤ μ.b-μ.a :=
    PsiSameRatioTail.entropy_drop_le_difference ha0 hab μ.b_interior.2
  have hcost : 16*(μ.b-μ.a) ≤ interiorCost μ.a μ.b :=
    PsiSameRatioTail.ratio_tail_cost ha0 hab μ.b_interior.2 hr
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
    have hs : deriv Scalar.P μ.information ≤ 16 :=
      PsiSameRatioTail.slope_le_sixteen hIp hIm hm0 hm
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

/-- The first of the seven residual active-psi owners is now unconditional. -/
theorem sameSidePsiRatioTailOwner : SameSidePsiRatioTailOwner := by
  intro k μ hab _hsum _hmean _hinfo hside hratio hactive
  exact μ.gap_le_of_splitBound hactive.le
    (μ.same_ratio_tail_splitBound hab.le hside hratio)

#print axioms PsiSameRatioTail.slope_le_sixteen
#print axioms PsiSameRatioTail.entropy_drop_le_difference
#print axioms PsiSameRatioTail.ratio_tail_cost
#print axioms InteriorLaw.same_ratio_tail_splitBound
#print axioms sameSidePsiRatioTailOwner

end GeneralCK

end


