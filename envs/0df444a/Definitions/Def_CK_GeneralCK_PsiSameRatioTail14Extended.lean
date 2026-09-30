-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameRatioTail14Extended
-- name    : CK_GeneralCK_PsiSameRatioTail14Extended
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:29:15.855439+00:00
-- url     : https://prove2.me/theorems/0ec45af9-70f4-4817-8c66-5094bf807677
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameRatioTail14Extended` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameRatioTail14Extended` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameRatioTail14Extended` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameRatioTail14Extended (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameRatioTail14Extended.lean)

import Definitions.Def_CK_GeneralCK_PsiSameRatioTail14Entropy425

-- ===== source module GeneralCK.PsiSameRatioTail14Extended =====
section

/-! The exact entropy anchor at midpoint `213/1000` enlarges the checked
same-side active-Psi ratio-fourteen strip to `b≤17/40`. -/

namespace GeneralCK
open Set

namespace PsiSameRatioTail14Extended

theorem slope_le {I m : ℝ} (hI : 0 < I) (hIm : I ≤ H m)
    (hm : 0 ≤ m) (hm' : m ≤ 213 / 1000) :
    deriv Scalar.P I ≤ 56 / 5 := by
  have hH : H m ≤ H (213 / 1000) := H_strictMonoOn.monotoneOn
    ⟨hm, by linarith⟩ ⟨by norm_num, by norm_num⟩ hm'
  have hcap : I ≤ 1 - H (1 / 32) := by
    linarith [PsiSameRatioTail14Entropy425.entropy_213_le_three_quarters,
      Certificates.SmallMean.entropy_one_over_32_lt]
  have ht0 : 0 < 1 - H (1 / 32) := by
    linarith [Certificates.SmallMean.entropy_one_over_32_lt]
  have ht1 : 1 - H (1 / 32) < 1 := by
    linarith [H_pos (p := (1 / 32 : ℝ)) (by norm_num) (by norm_num)]
  have hconv : ConvexOn ℝ (Ioo 0 1) Scalar.P :=
    Scalar.P_convexOn.subset Ioo_subset_Ico_self (convex_Ioo _ _)
  have hmono := hconv.monotoneOn_deriv (fun x hx =>
    (Scalar.hasDerivAt_P hx.1 hx.2).differentiableAt)
  have h := hmono ⟨hI, lt_of_le_of_lt hcap ht1⟩ ⟨ht0, ht1⟩ hcap
  exact h.trans PsiSameRatioTail14SmallB.slope_at_anchor_le

end PsiSameRatioTail14Extended

namespace InteriorLaw

theorem same_ratio_tail14_extended_splitBound {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 17 / 40)
    (hr : μ.a / μ.b ≤ 1 / 16384) : μ.splitBound ≤ μ.cost := by
  have ha0 := μ.a_interior.1
  have hb0 := μ.b_interior.1
  have hm0 : 0 ≤ μ.midpoint := by
    unfold midpoint
    linarith
  have hm : μ.midpoint ≤ 213 / 1000 := by
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
      PsiSameRatioTail14Extended.slope_le hIp hIm hm0 hm
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

theorem sameSidePsiRatioTail14ExtendedOwner {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 17 / 40)
    (hr : μ.a / μ.b ≤ 1 / 16384)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_splitBound hactive (μ.same_ratio_tail14_extended_splitBound hab hb hr)

#print axioms PsiSameRatioTail14Extended.slope_le
#print axioms InteriorLaw.same_ratio_tail14_extended_splitBound
#print axioms sameSidePsiRatioTail14ExtendedOwner

end GeneralCK

end


