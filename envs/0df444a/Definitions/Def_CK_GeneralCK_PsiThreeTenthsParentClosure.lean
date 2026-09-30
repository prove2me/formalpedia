-- Prove2me | Definitions.Def_CK_GeneralCK_PsiThreeTenthsParentClosure
-- name    : CK_GeneralCK_PsiThreeTenthsParentClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:57:09.096882+00:00
-- url     : https://prove2.me/theorems/9825dc2a-64c5-43e3-b317-7ef67d1f32ad
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiThreeTenthsParentClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiThreeTenthsParentClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiThreeTenthsParentClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiThreeTenthsParentClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiThreeTenthsParentClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiThreeTenthsParentGain
import Definitions.Def_CK_GeneralCK_PsiThreeTenthsContactRefinement

-- ===== source module GeneralCK.PsiThreeTenthsParentClosure =====
section

/-! Parent ratio-eight exclusion through bias three tenths. -/

namespace GeneralCK.PsiThreeTenthsParent

theorem parent_capacity_upper {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 10) :
    1 - H ((1 - q) / 2) ≤ (37 / 50) * q ^ 2 := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hs : q ^ 2 ≤ 9 / 100 := by nlinarith
  have hn : 0 < 1 - q ^ 2 := by linarith
  have hf : q ^ 2 / (12 * (1 - q ^ 2)) ≤ (3 / 364 : ℝ) := by
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
    (hq : 0 < q) (hqu : q ≤ 3 / 10) (hE : 0 < E) (hr : 8 * E ≤ q)
    (hbound : F q E * Real.log 2 < (5 / 2) * q ^ 2 + Real.log (1 + 18 * q ^ 2 / (25 * E))) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hCu : C ≤ (37 / 50) * q ^ 2 := parent_capacity_upper hq.le hqu
  have hs : q ^ 2 ≤ 9 / 100 := by nlinarith
  have hcap : E + C ≤ 1041 / 10000 := by nlinarith only [hCu, hr, hqu, hs]
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hClower := SmallMean.Cn_ge_half_sq hq.le (show q ≤ 1 by linarith)
  change q ^ 2 / 2 ≤ Real.log 2 * C at hClower
  have hCrational : 18 * q ^ 2 / 25 ≤ C := by
    have hh := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hh, hClower]
  have hg := PsiThreeTenthsParentGain.eta_increment_ge_five_linear_log hE hC hcap
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

theorem logarithmic_gain_lower {t : ℝ} (ht : 3 / 2 ≤ t) :
    t / (1 + t) + 9 / 40 ≤ Real.log (1 + t) := by
  have ht0 : 0 ≤ t := by linarith
  have h := Real.le_log_one_add_of_nonneg ht0
  have he : 2 * t / (t + 2) - t / (1 + t) = t ^ 2 / ((t + 2) * (1 + t)) := by
    field_simp
    ring
  have hf : (9 / 40 : ℝ) ≤ t ^ 2 / ((t + 2) * (1 + t)) := by
    apply (le_div_iff₀ (by positivity : 0 < (t + 2) * (1 + t))).mpr
    nlinarith [sq_nonneg (t - 3 / 2)]
  rw [← he] at hf
  linarith only [hf, h]

/-- A log-ratio tangent preserves the quadratic parent increment. -/
theorem logarithmic_parent_scale {q Q k : ℝ} (hq : 0 < q) (hqq : q ≤ Q)
    (hQu : Q ≤ 3 / 10) (hk : 0 ≤ k) (ht : 3 / 2 ≤ k * q) :
    q * Real.log (1 + k * Q) + (5 / 2) * q * Q * (Q - q) ≤ Q * Real.log (1 + k * q) := by
  have hQ : 0 < Q := hq.trans_le hqq
  have hd : 0 ≤ Q - q := sub_nonneg.mpr hqq
  have hden : 0 < 1 + k * q := by positivity
  have hnum : 0 < 1 + k * Q := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hnum hden)
  rw [Real.log_div hnum.ne' hden.ne'] at hl
  have he : (1 + k * Q) / (1 + k * q) - 1 = k * (Q - q) / (1 + k * q) := by
    field_simp
    ring
  rw [he] at hl
  have hstep := mul_le_mul_of_nonneg_left hl hq.le
  have hs : q * (Real.log (1 + k * Q) - Real.log (1 + k * q)) ≤
      (Q - q) * ((k * q) / (1 + k * q)) := by
    convert! hstep using 1 <;> ring
  have hg := mul_le_mul_of_nonneg_left (logarithmic_gain_lower ht) hd
  have hqQ : q * Q ≤ 9 / 100 := by
    nlinarith [mul_nonneg hQ.le hd]
  have hb := mul_le_mul_of_nonneg_right
    (show (5 / 2) * q * Q ≤ 9 / 40 by nlinarith only [hqQ]) hd
  nlinarith only [hs, hg, hb]

theorem log_twenty_three_halves_lt : Real.log (23 / 2 : ℝ) < 2443 / 1000 := by
  have hL : Real.log 2 ≤ (69315 / 100000 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hp := Real.log_lt_log (by norm_num : (0 : ℝ) < 6 / 5)
    (show (6 / 5 : ℝ) < (1251 / 1250) ^ (228 : ℕ) by norm_num)
  rw [Real.log_pow] at hp
  norm_num at hp
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1251 / 1250)
  have hs := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 575 / 576)
  have he : Real.log (23 / 2 : ℝ) =
      3 * Real.log 2 + 2 * Real.log (6 / 5) + Real.log (575 / 576) := by
    rw [show (23 / 2 : ℝ) = (2 ^ (3 : ℕ) * (6 / 5) ^ (2 : ℕ)) * (575 / 576) by norm_num,
      Real.log_mul (by norm_num : ((2 : ℝ) ^ (3 : ℕ) * (6 / 5) ^ (2 : ℕ)) ≠ 0)
        (by norm_num : (575 / 576 : ℝ) ≠ 0),
      Real.log_mul (by norm_num : (2 : ℝ) ^ (3 : ℕ) ≠ 0)
        (by norm_num : (6 / 5 : ℝ) ^ (2 : ℕ) ≠ 0), Real.log_pow, Real.log_pow]
    norm_num
  rw [he]
  linarith only [hp, hu, hs, hL]

theorem logarithmic_three_tenths {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < (10 / 3) * Real.log (1 + 27 * x / 125) + 2443 / 3000 := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (23 / 2 : ℝ) * (1 + 27 * x / 125) ^ 10 - x ^ 6 =
      (4735496038176927 / 1862645149230957031250) * (x - 8) ^ 10 +
      (59807561074753041 / 186264514923095703125) * (x - 8) ^ 9 +
      (6798126108830262327 / 372529029846191406250) * (x - 8) ^ 8 +
      (114477086573388614988 / 186264514923095703125) * (x - 8) ^ 7 +
      (2343891092953558222582 / 186264514923095703125) * (x - 8) ^ 6 +
      (147026085815332362064686 / 931322574615478515625) * (x - 8) ^ 5 +
      (224764974095645950974123 / 186264514923095703125) * (x - 8) ^ 4 +
      (1005252589871941876342348 / 186264514923095703125) * (x - 8) ^ 3 +
      (4700622432233185550909463 / 372529029846191406250) * (x - 8) ^ 2 +
      (2094062031317968201070481 / 186264514923095703125) * (x - 8) +
      676828571460265057964223 / 1862645149230957031250 := by ring
  have hp : 0 < (23 / 2 : ℝ) * (1 + 27 * x / 125) ^ 10 - x ^ 6 := by rw [he]; positivity
  have hh := Real.log_lt_log (by positivity : 0 < x ^ 6)
    (show x ^ 6 < (23 / 2 : ℝ) * (1 + 27 * x / 125) ^ 10 by linarith)
  rw [Real.log_pow, Real.log_mul (by norm_num : (23 / 2 : ℝ) ≠ 0)
    (by positivity : (1 + 27 * x / 125) ^ 10 ≠ 0), Real.log_pow] at hh
  linarith only [hh, log_twenty_three_halves_lt]

theorem parent_dominance_ratio8 {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 3 / 10)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hold : q ≤ 2 / 7
  · exact PsiTwoSeventhsParent.parent_dominance_ratio8 hq hold hE hr
  · let x := q / E
    have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
    have ht : 3 / 2 ≤ (18 * x / 25) * q := by
      nlinarith [mul_nonneg (show 0 ≤ q - 2 / 7 by linarith [lt_of_not_ge hold])
        (show 0 ≤ x - 8 by linarith)]
    have hs := logarithmic_parent_scale (Q := (3 / 10 : ℝ)) (k := 18 * x / 25)
      hq hqu (by norm_num) (by positivity) ht
    have hargQ : 1 + (18 * x / 25) * (3 / 10) = 1 + 27 * x / 125 := by ring
    have hargq : 1 + (18 * x / 25) * q = 1 + 18 * q ^ 2 / (25 * E) := by dsimp [x]; ring
    rw [hargQ, hargq] at hs
    have hsm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 10 / 3)
    have hp := mul_lt_mul_of_pos_left (logarithmic_three_tenths hx) hq
    have hF := PsiThreeTenthsContactRefinement.F_log_bound hq hE hr
    change F q E * Real.log 2 ≤ q * (2 * Real.log x - 2 / 31) at hF
    apply parent_dominance_of_cost_bound hq hqu hE hr
    nlinarith only [hF, hp, hsm, hq]

theorem active_bias_lt_eight_entropy {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 3 / 10)
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

end GeneralCK.PsiThreeTenthsParent

#print axioms GeneralCK.PsiThreeTenthsParent.parent_capacity_upper
#print axioms GeneralCK.PsiThreeTenthsParent.parent_dominance_of_cost_bound
#print axioms GeneralCK.PsiThreeTenthsParent.logarithmic_gain_lower
#print axioms GeneralCK.PsiThreeTenthsParent.logarithmic_parent_scale
#print axioms GeneralCK.PsiThreeTenthsParent.log_twenty_three_halves_lt
#print axioms GeneralCK.PsiThreeTenthsParent.logarithmic_three_tenths
#print axioms GeneralCK.PsiThreeTenthsParent.parent_dominance_ratio8
#print axioms GeneralCK.PsiThreeTenthsParent.active_bias_lt_eight_entropy

end


