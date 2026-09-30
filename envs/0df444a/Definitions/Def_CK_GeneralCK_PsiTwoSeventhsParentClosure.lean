-- Prove2me | Definitions.Def_CK_GeneralCK_PsiTwoSeventhsParentClosure
-- name    : CK_GeneralCK_PsiTwoSeventhsParentClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:35:40.029006+00:00
-- url     : https://prove2.me/theorems/b749c474-8d65-4475-b00e-9bea98661205
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiTwoSeventhsParentClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiTwoSeventhsParentClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiTwoSeventhsParentClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiTwoSeventhsParentClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiTwoSeventhsParentClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiFourFifteenthsParentClosure

-- ===== source module GeneralCK.PsiTwoSeventhsParentClosure =====
section

/-! Automatic ratio-eight clipping through bias two sevenths. -/

namespace GeneralCK.PsiTwoSeventhsParent
open Set

theorem log_thirty_seven_lt : Real.log (37 : ℝ) < 109 / 30 := by
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 37 / 32)
  have he : Real.log (37 : ℝ) = 5 * Real.log 2 + Real.log (37 / 32) := by
    rw [show (37 : ℝ) = 2 ^ (5 : ℕ) * (37 / 32) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (5 : ℕ) ≠ 0)
        (by norm_num : (37 / 32 : ℝ) ≠ 0), Real.log_pow]
    norm_num
  rw [he]
  linarith only [hu, hL]

theorem log_one_thirteen_twenty_fifths_lt : Real.log (113 / 25 : ℝ) < 679 / 450 := by
  have hL : Real.log 2 ≤ (69315 / 100000 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hp := Real.log_lt_log (by norm_num : (0 : ℝ) < 113 / 100)
    (show (113 / 100 : ℝ) < (2001 / 2000) ^ (245 : ℕ) by norm_num)
  rw [Real.log_pow] at hp
  norm_num at hp
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2001 / 2000)
  have he : Real.log (113 / 25 : ℝ) = 2 * Real.log 2 + Real.log (113 / 100) := by
    rw [show (113 / 25 : ℝ) = 2 ^ (2 : ℕ) * (113 / 100) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (2 : ℕ) ≠ 0)
        (by norm_num : (113 / 100 : ℝ) ≠ 0), Real.log_pow]
    norm_num
  rw [he]
  linarith only [hp, hu, hL]

theorem logarithmic_five_eighteenths {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < (18 / 5) * Real.log (1 + x / 5) + 109 / 150 := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (37 / 1 : ℝ) * (1 + x / 5) ^ 18 - x ^ 10 =
      (37 / 3814697265625) * (x - 8) ^ 18 +
      (8658 / 3814697265625) * (x - 8) ^ 17 +
      (956709 / 3814697265625) * (x - 8) ^ 16 +
      (66331824 / 3814697265625) * (x - 8) ^ 15 +
      (646735284 / 762939453125) * (x - 8) ^ 14 +
      (117705821688 / 3814697265625) * (x - 8) ^ 13 +
      (3315380644212 / 3814697265625) * (x - 8) ^ 12 +
      (73885625785296 / 3814697265625) * (x - 8) ^ 11 +
      (1316890863646541 / 3814697265625) * (x - 8) ^ 10 +
      (3754336464162924 / 762939453125) * (x - 8) ^ 9 +
      (212212911669156054 / 3814697265625) * (x - 8) ^ 8 +
      (1875872358053839056 / 3814697265625) * (x - 8) ^ 7 +
      (12721459131908279508 / 3814697265625) * (x - 8) ^ 6 +
      (64516254791449677048 / 3814697265625) * (x - 8) ^ 5 +
      (47157950877774700116 / 762939453125) * (x - 8) ^ 4 +
      (585404481881428135344 / 3814697265625) * (x - 8) ^ 3 +
      (886923424585981079901 / 3814697265625) * (x - 8) ^ 2 +
      (641177002307971063378 / 3814697265625) * (x - 8) +
      64850057222423545773 / 3814697265625 := by ring
  have hp : 0 < (37 / 1 : ℝ) * (1 + x / 5) ^ 18 - x ^ 10 := by rw [he]; positivity
  have hh := Real.log_lt_log (by positivity : 0 < x ^ 10)
    (show x ^ 10 < (37 / 1 : ℝ) * (1 + x / 5) ^ 18 by linarith)
  rw [Real.log_pow, Real.log_mul (by norm_num : (37 / 1 : ℝ) ≠ 0)
    (by positivity : (1 + x / 5) ^ 18 ≠ 0), Real.log_pow] at hh
  linarith only [hh, log_thirty_seven_lt]

theorem parent_dominance_five_eighteenths {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 5 / 18)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hquarter : q ≤ 4 / 15
  · exact PsiFourFifteenthsParent.parent_dominance_ratio8 hq hquarter hE hr
  · let x := q / E
    have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
    have hF := PsiRatioEightContactRefinement.F_log_bound_refined hq hE hr
    have hp := mul_lt_mul_of_pos_left (logarithmic_five_eighteenths hx) hq
    have hs := strictConcaveOn_log_Ioi.concaveOn.2
      (show 0 < 1 + x / 5 by positivity) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show 0 ≤ (18 / 5) * q by positivity) (show 0 ≤ 1 - (18 / 5) * q by linarith)
      (show (18 / 5) * q + (1 - (18 / 5) * q) = 1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
    have hs' : (18 / 5) * q * Real.log (1 + x / 5) ≤
        Real.log (1 + 18 * q ^ 2 / (25 * E)) := by
      convert! hs using 1
      congr 1
      dsimp [x]
      ring
    have hlinear := mul_nonneg hq.le (show 0 ≤ q - 4 / 15 by linarith [lt_of_not_ge hquarter])
    apply PsiFourFifteenthsParent.parent_dominance_of_cost_bound hq (by linarith) hE hr
    change F q E * Real.log 2 ≤ q * (2 * Real.log x - 3 / 50) at hF
    nlinarith only [hF, hp, hs', hlinear]

theorem logarithmic_two_sevenths {x : ℝ} (hx : 8 ≤ x) :
    2 * Real.log x < (7 / 2) * Real.log (1 + 36 * x / 175) + 679 / 900 := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (113 / 25 : ℝ) * (1 + 36 * x / 175) ^ 7 - x ^ 4 =
      (8855150542848 / 125662689208984375) * (x - 8) ^ 7 +
      (113887075037184 / 17951812744140625) * (x - 8) ^ 6 +
      (4394142978518016 / 17951812744140625) * (x - 8) ^ 5 +
      (15247491146114851 / 3590362548828125) * (x - 8) ^ 4 +
      (127384127903016608 / 3590362548828125) * (x - 8) ^ 3 +
      (2454309134794515792 / 17951812744140625) * (x - 8) ^ 2 +
      (3309074729778803812 / 17951812744140625) * (x - 8) +
      686771871877393471 / 125662689208984375 := by ring
  have hp : 0 < (113 / 25 : ℝ) * (1 + 36 * x / 175) ^ 7 - x ^ 4 := by rw [he]; positivity
  have hh := Real.log_lt_log (by positivity : 0 < x ^ 4)
    (show x ^ 4 < (113 / 25 : ℝ) * (1 + 36 * x / 175) ^ 7 by linarith)
  rw [Real.log_pow, Real.log_mul (by norm_num : (113 / 25 : ℝ) ≠ 0)
    (by positivity : (1 + 36 * x / 175) ^ 7 ≠ 0), Real.log_pow] at hh
  linarith only [hh, log_one_thirteen_twenty_fifths_lt]

theorem parent_dominance_ratio8 {q E : ℝ} (hq : 0 < q) (hqu : q ≤ 2 / 7)
    (hE : 0 < E) (hr : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hquarter : q ≤ 5 / 18
  · exact parent_dominance_five_eighteenths hq hquarter hE hr
  · let x := q / E
    have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hr
    have hF := PsiRatioEightContactRefinement.F_log_bound_refined hq hE hr
    have hp := mul_lt_mul_of_pos_left (logarithmic_two_sevenths hx) hq
    have hs := strictConcaveOn_log_Ioi.concaveOn.2
      (show 0 < 1 + 36 * x / 175 by positivity) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show 0 ≤ (7 / 2) * q by positivity) (show 0 ≤ 1 - (7 / 2) * q by linarith)
      (show (7 / 2) * q + (1 - (7 / 2) * q) = 1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hs
    have hs' : (7 / 2) * q * Real.log (1 + 36 * x / 175) ≤
        Real.log (1 + 18 * q ^ 2 / (25 * E)) := by
      convert! hs using 1
      congr 1
      dsimp [x]
      ring
    have hlinear := mul_nonneg hq.le (show 0 ≤ q - 5 / 18 by linarith [lt_of_not_ge hquarter])
    apply PsiFourFifteenthsParent.parent_dominance_of_cost_bound hq (by linarith) hE hr
    change F q E * Real.log 2 ≤ q * (2 * Real.log x - 3 / 50) at hF
    nlinarith only [hF, hp, hs', hlinear]

theorem active_bias_lt_eight_entropy {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 2 / 7)
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

end GeneralCK.PsiTwoSeventhsParent

#print axioms GeneralCK.PsiTwoSeventhsParent.log_thirty_seven_lt
#print axioms GeneralCK.PsiTwoSeventhsParent.log_one_thirteen_twenty_fifths_lt
#print axioms GeneralCK.PsiTwoSeventhsParent.logarithmic_five_eighteenths
#print axioms GeneralCK.PsiTwoSeventhsParent.parent_dominance_five_eighteenths
#print axioms GeneralCK.PsiTwoSeventhsParent.logarithmic_two_sevenths
#print axioms GeneralCK.PsiTwoSeventhsParent.parent_dominance_ratio8
#print axioms GeneralCK.PsiTwoSeventhsParent.active_bias_lt_eight_entropy

end


