-- Prove2me | Definitions.Def_CK_GeneralCK_PsiLargerEntropyRedesign
-- name    : CK_GeneralCK_PsiLargerEntropyRedesign
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T08:20:42.364174+00:00
-- url     : https://prove2.me/theorems/15a27ada-4ec5-4b37-ac96-d9c98736d98b
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiLargerEntropyRedesign` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiLargerEntropyRedesign` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiLargerEntropyRedesign` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiLargerEntropyRedesign (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiLargerEntropyRedesign.lean)

import Definitions.Def_CK_GeneralCK_PsiLowEntropyRedesign

-- ===== source module GeneralCK.PsiLargerEntropyRedesign =====
section

/-!+# A larger analytic active-psi region

Sharper bookkeeping extends the retained-child argument to entropy `1/80`.
The contact supporting plane remains a separate cost theorem.
-/

namespace GeneralCK.PsiLargerEntropyRedesign
open PsiChildEntropyCoupling PsiSignedSplit

theorem parent_gain_rational {E q : ℝ} (hE : 0 < E)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hphysical : E + (1 - H ((1 - q) / 2)) ≤ 1) :
    q ^ 2 / (Real.log 2 * (2 * Real.log 2 * E + q ^ 2)) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  let c := 1 - H ((1 - q) / 2)
  let c0 := q ^ 2 / (2 * Real.log 2)
  have hc : 0 ≤ c := sub_nonneg.mpr (H_le_one _)
  have hc0 : 0 ≤ c0 := by dsimp [c0]; positivity
  have hcle : c0 ≤ c := by
    have h := SmallMean.Cn_ge_half_sq hq hq1
    unfold SmallMean.Cn at h
    dsimp [c0, c]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log 2)).mpr
    nlinarith
  have hgain : c / (Real.log 2 * (E + c)) ≤ eta E - eta (E + c) :=
    eta_increment_ge_rational hE hc hphysical
  have hmono : c0 / (Real.log 2 * (E + c0)) ≤ c / (Real.log 2 * (E + c)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hcle (mul_nonneg log_two_pos.le hE.le)
    nlinarith
  have he : c0 / (Real.log 2 * (E + c0)) =
      q ^ 2 / (Real.log 2 * (2 * Real.log 2 * E + q ^ 2)) := by
    dsimp [c0]
    field_simp
  rw [he] at hmono
  exact hmono.trans hgain

theorem parent_entropy_le_one {E q : ℝ} (hE : 0 < E)
    (hEi : E ≤ 1 / 80) (hq : 0 ≤ q) (hqE : q ≤ 8 * E) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  rcases hq.eq_or_lt with he | hp
  · rw [← he]
    norm_num [H_half]
    linarith
  · have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    have hsmall := mul_nonneg hq (show 0 ≤ 1 / 10 - q by linarith)
    nlinarith

theorem parent_gain_larger_entropy {E q : ℝ} (hE : 0 < E)
    (hEi : E ≤ 1 / 80) (hq : 0 ≤ q) (hqE : q ≤ 8 * E) :
    (50 / 77) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hgain := parent_gain_rational hE hq (by linarith)
    (parent_entropy_le_one hE hEi hq hqE)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hqSq : q ^ 2 ≤ 64 * E ^ 2 := by nlinarith [sq_nonneg (8 * E - q)]
  have hLE : Real.log 2 * E ≤ (7 / 10 : ℝ) * (1 / 80) :=
    mul_le_mul hL hEi hE.le (by norm_num)
  have hLsq : (Real.log 2) ^ 2 ≤ (49 / 100 : ℝ) := by nlinarith [log_two_pos]
  have hcoef : 2 * (Real.log 2) ^ 2 + 64 * Real.log 2 * E ≤ 77 / 50 := by nlinarith
  have hden : Real.log 2 * (2 * Real.log 2 * E + q ^ 2) ≤ (77 / 50) * E := by
    have h1 := mul_le_mul_of_nonneg_right hcoef hE.le
    have h2 := mul_le_mul_of_nonneg_left hqSq log_two_pos.le
    nlinarith
  have hb := div_le_div_of_nonneg_left (sq_nonneg q)
    (by positivity : 0 < Real.log 2 * (2 * Real.log 2 * E + q ^ 2)) hden
  have he : q ^ 2 / ((77 / 50) * E) = (50 / 77) * (q ^ 2 / E) := by ring
  rw [he] at hb
  exact hb.trans hgain

theorem capacity_quadratic_third {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1 / 3) :
    capacity z ≤ (49 / 96) * z ^ 2 := by
  have hz1 : z < 1 := by linarith
  rw [capacity_eq_Cn (by rw [abs_of_nonneg hz]; exact hz1)]
  have hs : z ^ 2 ≤ 1 / 9 := by nlinarith
  have hn : 0 < 1 - z ^ 2 := by nlinarith
  have hf : z ^ 2 / (12 * (1 - z ^ 2)) ≤ (1 / 96 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - z ^ 2))).mpr
    nlinarith only [hs]
  have h := LowInformation.Cn_upper_sharp hz hz1
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg z)
  have he : z ^ 2 * (z ^ 2 / (12 * (1 - z ^ 2))) = z ^ 4 / (12 * (1 - z ^ 2)) := by ring
  rw [he] at hh
  linarith

theorem split_loss_le_four_sq {c q : ℝ} (hc : 1 / 3 ≤ c)
    (hq : 0 ≤ q) (hq' : q ≤ 1 / 10) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ 4 * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (1 / 3 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (1 / 3 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (1 / 3 : ℝ)) = 13 * q / 4 by ring] at h
  have hb := capacity_quadratic_third (z := 13 * q / 4) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

theorem objective_ge_neg_four_sq {c q t : ℝ} (hc : 1 / 3 ≤ c)
    (hq : 0 ≤ q) (hq' : q ≤ 1 / 10) (ht : |t| < 1) :
    -(4 * q ^ 2) ≤ objective c (13 * q / 6) t := by
  have hcpos : 0 < c := by linarith
  have hk : |13 * q / 6| < 2 * c := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  obtain ⟨hz, heq, _⟩ := objective_minimum hcpos hk
  have h := objective_lower hcpos.le hz ht
  rw [mul_div_cancel₀ _ (show 2 * c ≠ 0 by positivity)] at h
  linarith [split_loss_le_four_sq hc hq hq']

theorem signed_split_ge_neg_four_sq {c q E A t : ℝ}
    (hc : 1 / 3 ≤ c) (hq : 0 ≤ q) (hq' : q ≤ 1 / 10)
    (hE : 0 < E) (hA : 0 ≤ A) (hA' : A ≤ 13 * q / (3 * E)) (ht : |t| < 1) :
    -(4 * q ^ 2) ≤ c * barrier t + E * t * A / 2 + (13 * q / 6) * (tilt t - t) := by
  by_cases ht0 : 0 ≤ t
  · have hb : 0 ≤ c * barrier t := mul_nonneg (by linarith) (barrier_nonneg ht)
    have hl : 0 ≤ E * t * A / 2 := by positivity
    have hm : 0 ≤ (13 * q / 6) * (tilt t - t) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (tilt_ge_self ht0 (abs_lt.mp ht).2))
    nlinarith [sq_nonneg q]
  · have hEA : E * A ≤ 13 * q / 3 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 3 * E)).mp hA'
      nlinarith
    have hlin := mul_le_mul_of_nonpos_left hEA (le_of_not_ge ht0)
    have hobj := objective_ge_neg_four_sq (t := -t) hc hq hq' (by simpa using ht)
    unfold objective at hobj
    rw [barrier_neg, tilt_neg] at hobj
    nlinarith

/-- A uniform retained-child margin on the much larger interval `E<=1/80`.
No endpoint-cost hypothesis occurs in this scalar comparison. -/
theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 80) (hd : 8 * E ≤ d) (hd1 : d ≤ 1)
    (hq : 0 ≤ q) (hqE : q ≤ 8 * E) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (9 / 100) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  have hqd : q ≤ d := hqE.trans hd
  have hg := parent_gain_larger_entropy hE hEi hq hqE
  have hr := PsiRadialDeficit.radial_average_loss_le_half hE hd q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith), abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (q ^ 2 / E) / 2 := by
    rw [show q ^ 2 / (2 * E) = (q ^ 2 / E) / 2 by ring] at hr
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  have hc : 1 / 3 ≤ endpointCoefficient d := endpoint_coefficient_ge_third (by linarith) hd1
  have hs := signed_split_ge_neg_four_sq hc hq (by linarith) hE hA hA' ht
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2)) hq hqd hE (by linarith) ht
  have hsmall : 4 * q ^ 2 ≤ (1 / 20) * (q ^ 2 / E) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hE).mpr
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ 1 / 20 - 4 * E by linarith)]
  have hnonneg : 0 ≤ q ^ 2 / E := by positivity
  linarith

end GeneralCK.PsiLargerEntropyRedesign

#print axioms GeneralCK.PsiLargerEntropyRedesign.parent_gain_rational
#print axioms GeneralCK.PsiLargerEntropyRedesign.retained_child_margin

end


