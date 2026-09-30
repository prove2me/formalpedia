-- Prove2me | Definitions.Def_CK_GeneralCK_PsiFourFifteenthsParentClosure
-- name    : CK_GeneralCK_PsiFourFifteenthsParentClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:31:39.690709+00:00
-- url     : https://prove2.me/theorems/5789ec6b-3c40-455b-8cf8-587716226b5b
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiFourFifteenthsParentClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiFourFifteenthsParentClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiFourFifteenthsParentClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiFourFifteenthsParentClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiFourFifteenthsParentClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiParentFiveGainExtended
import Definitions.Def_CK_GeneralCK_PsiRatioEightContactRefinement

-- ===== source module GeneralCK.PsiFourFifteenthsParentClosure =====
section

/-! Parent ratio-eight exclusion through bias four fifteenths. -/

namespace GeneralCK.PsiFourFifteenthsParent
open Set

theorem parent_capacity_upper {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 2 / 7) :
    1 - H ((1 - q) / 2) ≤ (37 / 50) * q ^ 2 := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hs : q ^ 2 ≤ 4 / 49 := by nlinarith
  have hn : 0 < 1 - q ^ 2 := by linarith
  have hf : q ^ 2 / (12 * (1 - q ^ 2)) ≤ (1 / 135 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - q ^ 2))).mpr
    nlinarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hf (sq_nonneg q)
  have he : q ^ 2 * (q ^ 2 / (12 * (1 - q ^ 2))) = q ^ 4 / (12 * (1 - q ^ 2)) := by ring
  rw [he] at hm
  have hc := LowInformation.Cn_upper_sharp hq (by linarith : q < 1)
  change Real.log 2 * C ≤ q ^ 2 / 2 + q ^ 4 / (12 * (1 - q ^ 2)) at hc
  have hl := mul_le_mul_of_nonneg_right hL hC
  change C ≤ (37 / 50) * q ^ 2
  nlinarith only [hm, hc, hl, sq_nonneg q]

theorem parent_dominance_of_cost_bound {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 2 / 7) (hE : 0 < E) (hr : 8 * E ≤ q)
    (hbound : F q E * Real.log 2 < (5 / 2) * q ^ 2 + Real.log (1 + 18 * q ^ 2 / (25 * E))) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hCu : C ≤ (37 / 50) * q ^ 2 := parent_capacity_upper hq.le hqu
  have hs : q ^ 2 ≤ 4 / 49 := by nlinarith
  have hcap : E + C ≤ 77 / 800 := by nlinarith only [hCu, hr, hqu, hs]
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hClower := SmallMean.Cn_ge_half_sq hq.le (show q ≤ 1 by linarith)
  change q ^ 2 / 2 ≤ Real.log 2 * C at hClower
  have hCrational : 18 * q ^ 2 / 25 ≤ C := by
    have hh := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hh, hClower]
  have hg := PsiParentFiveGainExtended.eta_increment_ge_five_linear_log hE hC hcap
  have hl : Real.log (1 + 18 * q ^ 2 / (25 * E)) ≤ Real.log (1 + C / E) := by
    apply Real.log_le_log (by positivity)
    have hh := div_le_div_of_nonneg_right hCrational hE.le
    convert! add_le_add_left hh 1 using 1 <;> ring
  have hgm := mul_le_mul_of_nonneg_right hg log_two_pos.le
  have hid : (5 * C + Real.log (1 + C / E) / Real.log 2) * Real.log 2 =
      5 * C * Real.log 2 + Real.log (1 + C / E) := by field_simp
  rw [hid] at hgm
  have hcost : F q E < eta E - eta (E + C) := by
    apply (mul_lt_mul_iff_left₀ log_two_pos).mp
    nlinarith only [hbound, hl, hgm, hClower]
  unfold phi psi
  rw [show |1 - 2 * ((1 - q) / 2)| = q by
    rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq]]
  have he : E + 1 - H ((1 - q) / 2) = E + C := by dsimp [C]; ring
  rw [he]
  linarith only [hcost]

theorem log_fifty_nine_fourths_lt : Real.log (59 / 4 : ℝ) < 27 / 10 := by
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 59 / 64)
  have he : Real.log (59 / 4 : ℝ) = 4 * Real.log 2 + Real.log (59 / 64) := by
    rw [show (59 / 4 : ℝ) = 2 ^ (4 : ℕ) * (59 / 64) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (4 : ℕ) ≠ 0)
        (by norm_num : (59 / 64 : ℝ) ≠ 0), Real.log_pow]
    norm_num
  rw [he]
  linarith only [hu, hL]

theorem logarithmic_four_fifteenths {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < (15 / 4) * Real.log (1 + 24 * x / 125) + 27 / 40 := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (59 / 4 : ℝ) * (1 + 24 * x / 125) ^ 15 - x ^ 8 =
      (7446644923601680072704 / 28421709430404007434844970703125) * (x - 8) ^ 15 +
      (295073305097716572880896 / 5684341886080801486968994140625) * (x - 8) ^ 14 +
      (27281986000493044800946176 / 5684341886080801486968994140625) * (x - 8) ^ 13 +
      (1561514782055997744787488768 / 5684341886080801486968994140625) * (x - 8) ^ 12 +
      (61875023238968910637204242432 / 5684341886080801486968994140625) * (x - 8) ^ 11 +
      (8989925251428524641330466390016 / 28421709430404007434844970703125) * (x - 8) ^ 10 +
      (39580643120872809879191081189376 / 5684341886080801486968994140625) * (x - 8) ^ 9 +
      (666479793970169951997150973914671 / 5684341886080801486968994140625) * (x - 8) ^ 8 +
      (8514370080392140740436735619730368 / 5684341886080801486968994140625) * (x - 8) ^ 7 +
      (81020394088679367656659456074336512 / 5684341886080801486968994140625) * (x - 8) ^ 6 +
      (2799159611622201794209950282883084288 / 28421709430404007434844970703125) * (x - 8) ^ 5 +
      (2709803661158542605368517479825521664 / 5684341886080801486968994140625) * (x - 8) ^ 4 +
      (8675561592851011631177622098676255104 / 5684341886080801486968994140625) * (x - 8) ^ 3 +
      (16514447636539693355368328896926662192 / 5684341886080801486968994140625) * (x - 8) ^ 2 +
      (14521559885817038578284287263843761398 / 5684341886080801486968994140625) * (x - 8) +
      27918606847618123850895503479915131287 / 113686837721616029739379882812500 := by ring
  have hp : 0 < (59 / 4 : ℝ) * (1 + 24 * x / 125) ^ 15 - x ^ 8 := by rw [he]; positivity
  have hh := Real.log_lt_log (by positivity : 0 < x ^ 8)
    (show x ^ 8 < (59 / 4 : ℝ) * (1 + 24 * x / 125) ^ 15 by linarith)
  rw [Real.log_pow, Real.log_mul (by norm_num : (59 / 4 : ℝ) ≠ 0)
    (by positivity : (1 + 24 * x / 125) ^ 15 ≠ 0), Real.log_pow] at hh
  linarith only [hh, log_fifty_nine_fourths_lt]

theorem parent_dominance_ratio8 {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 4 / 15)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hquarter : q ≤ 1 / 4
  · exact PsiQuarterParent.parent_dominance_ratio8 hq hquarter hE hr
  · let x := q / E
    have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
    have hF := PsiRatioEightContactRefinement.F_log_bound hq hE hr
    have hp := mul_lt_mul_of_pos_left (logarithmic_four_fifteenths hx) hq
    have hs := strictConcaveOn_log_Ioi.concaveOn.2
      (show 0 < 1 + 24 * x / 125 by positivity) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show 0 ≤ (15 / 4) * q by positivity) (show 0 ≤ 1 - (15 / 4) * q by linarith)
      (show (15 / 4) * q + (1 - (15 / 4) * q) = 1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
    have hs' : (15 / 4) * q * Real.log (1 + 24 * x / 125) ≤
        Real.log (1 + 18 * q ^ 2 / (25 * E)) := by
      convert! hs using 1
      congr 1
      dsimp [x]
      ring
    have hlinear := mul_nonneg hq.le (show 0 ≤ q - 1 / 4 by linarith [lt_of_not_ge hquarter])
    apply parent_dominance_of_cost_bound hq (by linarith) hE hr
    change F q E * Real.log 2 ≤ q * (2 * Real.log x - 1 / 20) at hF
    nlinarith only [hF, hp, hs', hlinear]

theorem active_bias_lt_eight_entropy {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 4 / 15)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    1 - μ.a - μ.b < 8 * μ.meanEntropy := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_contra hn
  have h := parent_dominance_ratio8 (by linarith [le_of_not_gt hn]) hq hE (le_of_not_gt hn)
  have hm : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  rw [hm] at h
  exact (not_lt_of_ge hactive) h

end GeneralCK.PsiFourFifteenthsParent

#print axioms GeneralCK.PsiFourFifteenthsParent.parent_capacity_upper
#print axioms GeneralCK.PsiFourFifteenthsParent.parent_dominance_of_cost_bound
#print axioms GeneralCK.PsiFourFifteenthsParent.log_fifty_nine_fourths_lt
#print axioms GeneralCK.PsiFourFifteenthsParent.logarithmic_four_fifteenths
#print axioms GeneralCK.PsiFourFifteenthsParent.parent_dominance_ratio8
#print axioms GeneralCK.PsiFourFifteenthsParent.active_bias_lt_eight_entropy

end


