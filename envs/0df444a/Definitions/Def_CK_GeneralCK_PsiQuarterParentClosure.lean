-- Prove2me | Definitions.Def_CK_GeneralCK_PsiQuarterParentClosure
-- name    : CK_GeneralCK_PsiQuarterParentClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:16:44.500745+00:00
-- url     : https://prove2.me/theorems/4953fb30-7d8d-438d-a6e9-2da036306254
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiQuarterParentClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiQuarterParentClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiQuarterParentClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiQuarterParentClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiQuarterParentClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiParentElevenHalvesGain

-- ===== source module GeneralCK.PsiQuarterParentClosure =====
section

/-! Parent ratio-eight exclusion through bias one quarter. -/

namespace GeneralCK.PsiQuarterParent
open Set

theorem parent_capacity_upper {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 1 / 4) :
    1 - H ((1 - q) / 2) ≤ (3 / 4) * q ^ 2 := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hs : q ^ 2 ≤ 1 / 16 := by nlinarith
  have hn : 0 < 1 - q ^ 2 := by linarith
  have hf : q ^ 2 / (12 * (1 - q ^ 2)) ≤ (1 / 180 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - q ^ 2))).mpr
    nlinarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hf (sq_nonneg q)
  have he : q ^ 2 * (q ^ 2 / (12 * (1 - q ^ 2))) = q ^ 4 / (12 * (1 - q ^ 2)) := by ring
  rw [he] at hm
  have hc := LowInformation.Cn_upper_sharp hq (by linarith : q < 1)
  change Real.log 2 * C ≤ q ^ 2 / 2 + q ^ 4 / (12 * (1 - q ^ 2)) at hc
  have hl := mul_le_mul_of_nonneg_right hL hC
  change C ≤ (3 / 4) * q ^ 2
  nlinarith only [hm, hc, hl, sq_nonneg q]

theorem parent_dominance_of_cost_bound {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 1 / 4) (hE : 0 < E) (hr : 8 * E ≤ q)
    (hbound : F q E * Real.log 2 < (11 / 4) * q ^ 2 + Real.log (1 + 18 * q ^ 2 / (25 * E))) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hCu : C ≤ (3 / 4) * q ^ 2 := parent_capacity_upper hq.le hqu
  have hs : q ^ 2 ≤ 1 / 16 := by nlinarith
  have hcap : E + C ≤ 2 / 25 := by nlinarith only [hCu, hr, hqu, hs]
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hClower := SmallMean.Cn_ge_half_sq hq.le (show q ≤ 1 by linarith)
  change q ^ 2 / 2 ≤ Real.log 2 * C at hClower
  have hCrational : 18 * q ^ 2 / 25 ≤ C := by
    have hh := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hh, hClower]
  have hg := PsiParentElevenHalvesGain.eta_increment_ge_eleven_halves_linear_log hE hC hcap
  have hl : Real.log (1 + 18 * q ^ 2 / (25 * E)) ≤ Real.log (1 + C / E) := by
    apply Real.log_le_log (by positivity)
    have hh := div_le_div_of_nonneg_right hCrational hE.le
    convert! add_le_add_left hh 1 using 1 <;> ring
  have hgm := mul_le_mul_of_nonneg_right hg log_two_pos.le
  have hid : ((11 / 2) * C + Real.log (1 + C / E) / Real.log 2) * Real.log 2 =
      (11 / 2) * C * Real.log 2 + Real.log (1 + C / E) := by field_simp
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

theorem log_eight_thirds_le_one : Real.log (8 / 3 : ℝ) ≤ 1 := by
  have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  norm_num at h
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have he : Real.log (8 / 3 : ℝ) = 2 * Real.log 2 - Real.log (3 / 2) := by
    rw [Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      show Real.log (8 : ℝ) = 3 * Real.log 2 by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num]
    ring
  rw [he]
  linarith only [h, hL]

theorem logarithmic_two_ninths {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < (9 / 2) * Real.log (1 + 4 * x / 25) + 1 / 2 := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (8 / 3 : ℝ) * (1 + 4 * x / 25) ^ 9 - x ^ 4 =
      (2097152 / 11444091796875) * (x - 8) ^ 9 +
      (89653248 / 3814697265625) * (x - 8) ^ 8 +
      (5110235136 / 3814697265625) * (x - 8) ^ 7 +
      (169915318272 / 3814697265625) * (x - 8) ^ 6 +
      (3631939928064 / 3814697265625) * (x - 8) ^ 5 +
      (47940446709287 / 3814697265625) * (x - 8) ^ 4 +
      (369603555261664 / 3814697265625) * (x - 8) ^ 3 +
      (1537878799544448 / 3814697265625) * (x - 8) ^ 2 +
      (2884699082752096 / 3814697265625) * (x - 8) + 1312231881024152 / 3814697265625 := by ring
  have hp : 0 < (8 / 3 : ℝ) * (1 + 4 * x / 25) ^ 9 - x ^ 4 := by rw [he]; positivity
  have hh := Real.log_lt_log (by positivity : 0 < x ^ 4)
    (show x ^ 4 < (8 / 3 : ℝ) * (1 + 4 * x / 25) ^ 9 by linarith)
  rw [Real.log_pow, Real.log_mul (by norm_num : (8 / 3 : ℝ) ≠ 0)
    (by positivity : (1 + 4 * x / 25) ^ 9 ≠ 0), Real.log_pow] at hh
  linarith only [hh, log_eight_thirds_le_one]

theorem parent_dominance_two_ninths {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 2 / 9)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hfifth : q ≤ 1 / 5
  · exact PsiFifthBiasAutomatic.parent_dominance_ratio8 hq hfifth hE hr
  · let x := q / E
    have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
    have hF := (le_div_iff₀ log_two_pos).mp
      (PsiParentDominance.F_le_logarithmic_ratio8 hq hE hr)
    have hp := mul_lt_mul_of_pos_left (logarithmic_two_ninths hx) hq
    have hs := strictConcaveOn_log_Ioi.concaveOn.2
      (show 0 < 1 + 4 * x / 25 by positivity) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show 0 ≤ (9 / 2) * q by positivity) (show 0 ≤ 1 - (9 / 2) * q by linarith)
      (show (9 / 2) * q + (1 - (9 / 2) * q) = 1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
    have hs' : (9 / 2) * q * Real.log (1 + 4 * x / 25) ≤
        Real.log (1 + 18 * q ^ 2 / (25 * E)) := by
      convert! hs using 1
      congr 1
      dsimp [x]
      ring
    have hlinear := mul_nonneg hq.le (show 0 ≤ q - 1 / 5 by linarith [lt_of_not_ge hfifth])
    apply parent_dominance_of_cost_bound hq (by linarith) hE hr
    change F q E * Real.log 2 ≤ 2 * q * Real.log x at hF
    nlinarith only [hF, hp, hs', hlinear, sq_nonneg q]

theorem log_eleven_sixths_lt : Real.log (11 / 6 : ℝ) < 11 / 18 := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 11 / 6)
    (show (11 / 6 : ℝ) < (73 / 72) ^ (44 : ℕ) by norm_num)
  rw [Real.log_pow] at h
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 73 / 72)
  norm_num at hu
  linarith only [h, hu]

theorem logarithmic_quarter {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < 4 * Real.log (1 + 9 * x / 50) + 11 / 18 := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (11 / 6 : ℝ) * (1 + 9 * x / 50) ^ 4 - x ^ 2 =
      (24057 / 12500000) * (x - 8) ^ 4 +
      (163053 / 1562500) * (x - 8) ^ 3 +
      (1752911 / 1562500) * (x - 8) ^ 2 +
      (1240373 / 390625) * (x - 8) + 2304251 / 2343750 := by ring
  have hp : 0 < (11 / 6 : ℝ) * (1 + 9 * x / 50) ^ 4 - x ^ 2 := by rw [he]; positivity
  have hh := Real.log_lt_log (by positivity : 0 < x ^ 2)
    (show x ^ 2 < (11 / 6 : ℝ) * (1 + 9 * x / 50) ^ 4 by linarith)
  rw [Real.log_pow, Real.log_mul (by norm_num : (11 / 6 : ℝ) ≠ 0)
    (by positivity : (1 + 9 * x / 50) ^ 4 ≠ 0), Real.log_pow] at hh
  linarith only [hh, log_eleven_sixths_lt]

theorem parent_dominance_ratio8 {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 1 / 4)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hmid : q ≤ 2 / 9
  · exact parent_dominance_two_ninths hq hmid hE hr
  · let x := q / E
    have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
    have hF := (le_div_iff₀ log_two_pos).mp
      (PsiParentDominance.F_le_logarithmic_ratio8 hq hE hr)
    have hp := mul_lt_mul_of_pos_left (logarithmic_quarter hx) hq
    have hs := strictConcaveOn_log_Ioi.concaveOn.2
      (show 0 < 1 + 9 * x / 50 by positivity) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show 0 ≤ 4 * q by positivity) (show 0 ≤ 1 - 4 * q by linarith)
      (show 4 * q + (1 - 4 * q) = 1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
    have hs' : 4 * q * Real.log (1 + 9 * x / 50) ≤
        Real.log (1 + 18 * q ^ 2 / (25 * E)) := by
      convert! hs using 1
      congr 1
      dsimp [x]
      ring
    have hlinear := mul_nonneg hq.le (show 0 ≤ q - 2 / 9 by linarith [lt_of_not_ge hmid])
    apply parent_dominance_of_cost_bound hq hqu hE hr
    change F q E * Real.log 2 ≤ 2 * q * Real.log x at hF
    nlinarith only [hF, hp, hs', hlinear]

theorem active_bias_lt_eight_entropy {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 1 / 4)
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

end GeneralCK.PsiQuarterParent

#print axioms GeneralCK.PsiQuarterParent.parent_capacity_upper
#print axioms GeneralCK.PsiQuarterParent.parent_dominance_of_cost_bound
#print axioms GeneralCK.PsiQuarterParent.log_eight_thirds_le_one
#print axioms GeneralCK.PsiQuarterParent.logarithmic_two_ninths
#print axioms GeneralCK.PsiQuarterParent.parent_dominance_two_ninths
#print axioms GeneralCK.PsiQuarterParent.log_eleven_sixths_lt
#print axioms GeneralCK.PsiQuarterParent.logarithmic_quarter
#print axioms GeneralCK.PsiQuarterParent.parent_dominance_ratio8
#print axioms GeneralCK.PsiQuarterParent.active_bias_lt_eight_entropy

end


