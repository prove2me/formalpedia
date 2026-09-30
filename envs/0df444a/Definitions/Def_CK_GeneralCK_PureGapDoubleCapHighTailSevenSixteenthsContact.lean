-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsContact
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsContact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:47:10.887234+00:00
-- url     : https://prove2.me/theorems/be03c7f7-965e-4dc6-91b8-acae5f8f1d91
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsContact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsContact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsContact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsContact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailSevenSixteenthsContact.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSign
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsIdentity

-- ===== source module GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsContact =====
section

/-! Wider true implicit-contact enclosure on x≤1/8. Draft until Lean audit. -/

namespace GeneralCK
open Certificates.Reflection

private theorem Cn_eq_log_sub_biasE {z : ℝ} (hz0 : -1 < z) (hz1 : z < 1) :
    SmallMean.Cn z = Real.log 2 - biasE z := by
  rw [Reflection.biasE_eq_log_mul_E hz0 hz1]
  unfold SmallMean.Cn Reflection.E
  ring

private theorem highTailL_eq {x : ℝ} :
    Real.log 2 * doubleCapHighTailFloor x =
      Real.log 2 - SmallMean.Cn (2 * x) / 2 := by
  unfold doubleCapHighTailFloor SmallMean.Cn
  ring

/-- Coarse but explicit enclosures of the *true* regular contact on the
high cap tail. No numerical approximation of the implicit contact is used. -/
theorem doubleCapHighTailSevenC_bounds {x : ℝ}
    (hx : 0 < x) (hx8 : x ≤ 1 / 8) :
    x ≤ doubleCapHighTailC x ∧
      doubleCapHighTailC x ≤ (26 / 25 : ℝ) * x := by
  have hx1 : x < 1 / 2 := by linarith
  let L : ℝ := Real.log 2 * doubleCapHighTailFloor x
  let c : ℝ := doubleCapHighTailC x
  have hLpos : 0 < L := mul_pos log_two_pos
    (doubleCapHighTailFloor_pos hx hx1)
  have hcMem := Reflection.regularContact_mem
    (x / (Real.log 2 * doubleCapHighTailFloor x))
  have hcMem' : -1 < c ∧ c < 1 := by
    change -1 < Reflection.regularContact
      (x / (Real.log 2 * doubleCapHighTailFloor x)) ∧
      Reflection.regularContact
        (x / (Real.log 2 * doubleCapHighTailFloor x)) < 1 at hcMem
    exact hcMem
  have hEcPos : 0 < biasE c := Reflection.biasE_pos_wide hcMem'.1 hcMem'.2
  have hEcLe : biasE c ≤ Real.log 2 :=
    Reflection.biasE_le_log_two_wide hcMem'.1 hcMem'.2
  have hCeq : c = (x / L) * biasE c := by
    simpa only [c, L] using doubleCapHighTailC_equation x
  have hcCross : c * L = x * biasE c := by
    have hMul := congrArg (fun z : ℝ => z * L) hCeq
    have hCancel : ((x / L) * biasE c) * L = x * biasE c := by
      field_simp [hLpos.ne']
    exact hMul.trans hCancel
  have hc0 : 0 < c := by
    rw [hCeq]
    exact mul_pos (div_pos hx hLpos) hEcPos
  have hu : x ^ 2 ≤ 1 / 64 := by
    have hsq := (sq_le_sq₀ hx.le
      (by norm_num : (0 : ℝ) ≤ 1 / 8)).2 hx8
    norm_num at hsq
    exact hsq
  have hgap : 0 < 1 - 4 * x ^ 2 := by nlinarith [hu]
  have hCn2 := SmallMean.Cn_le_half_sq_over_gap
    (show 0 ≤ 2 * x by positivity) (show 2 * x < 1 by linarith)
  have hCn2half : SmallMean.Cn (2 * x) / 2 ≤
      x ^ 2 / (1 - 4 * x ^ 2) := by
    have hgap2 : 0 < 1 - (2 * x) ^ 2 := by nlinarith [hgap]
    calc
      _ ≤ ((2 * x) ^ 2 / (2 * (1 - (2 * x) ^ 2))) / 2 :=
        div_le_div_of_nonneg_right hCn2 (by norm_num : (0 : ℝ) ≤ 2)
      _ = x ^ 2 / (1 - 4 * x ^ 2) := by
        field_simp [hgap.ne', hgap2.ne']
        ring
  have hCn2small : SmallMean.Cn (2 * x) / 2 ≤ 1 / 60 := by
    have hrat : x ^ 2 / (1 - 4 * x ^ 2) ≤ 1 / 60 := by
      apply (div_le_iff₀ hgap).2
      nlinarith [hu]
    exact hCn2half.trans hrat
  have hLlo : (101 / 150 : ℝ) ≤ L := by
    have hlog : (69 / 100 : ℝ) < Real.log 2 := by
      exact Certificates.Mixed.log_two_gt_69
    have hLeq : L = Real.log 2 - SmallMean.Cn (2 * x) / 2 :=
      highTailL_eq
    linarith [hCn2small]
  have hLhi : L ≤ Real.log 2 - x ^ 2 := by
    have hCn2lo := SmallMean.Cn_ge_half_sq
      (show 0 ≤ 2 * x by positivity) (show 2 * x ≤ 1 by linarith)
    have hLeq : L = Real.log 2 - SmallMean.Cn (2 * x) / 2 :=
      highTailL_eq
    nlinarith [hCn2lo]
  have hCnX := SmallMean.Cn_le_half_sq_over_gap hx.le (by linarith)
  have hCnXsmall : SmallMean.Cn x ≤ x ^ 2 := by
    have hgapX : 0 < 1 - x ^ 2 := by nlinarith [hu]
    have hrat : x ^ 2 / (2 * (1 - x ^ 2)) ≤ x ^ 2 := by
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hgapX)).2
      have hsmall : 0 ≤ 1 - 2 * x ^ 2 := by nlinarith [hu]
      have hm := mul_nonneg (sq_nonneg x) hsmall
      nlinarith [hm]
    exact hCnX.trans hrat
  have hEx : L ≤ biasE x := by
    have hEeq := Cn_eq_log_sub_biasE (by linarith : -1 < x)
      (by linarith : x < 1)
    linarith [hLhi, hCnXsmall]
  have hcGe : x ≤ c := by
    by_contra h
    have hcx : c < x := lt_of_not_ge h
    have hEcOrd : biasE x ≤ biasE c :=
      biasE_antitone ⟨hc0.le, hcMem'.2.le⟩
        ⟨hx.le, (by linarith : x ≤ 1)⟩ hcx.le
    have hEL : L ≤ biasE c := hEx.trans hEcOrd
    have hm := mul_le_mul_of_nonneg_left hEL hx.le
    nlinarith [hm, hcCross, hLpos]
  have hcLe : c ≤ (26 / 25 : ℝ) * x := by
    have hLogHi : Real.log 2 ≤ (7 / 10 : ℝ) := by
      have hp := Certificates.PilotData.log_two.2
      norm_num at hp
      linarith
    have h1 := mul_le_mul_of_nonneg_left hLlo hc0.le
    have h2 := mul_le_mul_of_nonneg_left (hEcLe.trans hLogHi) hx.le
    nlinarith [h1, h2, hcCross, hx]
  exact ⟨hcGe, hcLe⟩

#print axioms doubleCapHighTailSevenC_bounds

end GeneralCK

end


