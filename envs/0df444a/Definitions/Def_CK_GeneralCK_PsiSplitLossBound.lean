-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSplitLossBound
-- name    : CK_GeneralCK_PsiSplitLossBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:37:14.577395+00:00
-- url     : https://prove2.me/theorems/a96bf0e0-c9bf-431d-9665-a4ef53f57616
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSplitLossBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSplitLossBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSplitLossBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSplitLossBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSplitLossBound.lean)

import Definitions.Def_CK_GeneralCK_PsiSignedSplit
import Definitions.Def_CK_GeneralCK_LowInformationMeans

-- ===== source module GeneralCK.PsiSplitLossBound =====
section

/-!
# A uniform quadratic bound for the signed entropy-split loss

The exact loss from `PsiSignedSplit` is an entropy deficit in natural units.
Existing sharp small-mean estimates bound it by `4*q^2`, uniformly in the
barrier coefficient `c >= 1/3`. No certificate or support-plane premise is
needed for this analytic estimate.
-/
namespace GeneralCK.PsiSignedSplit

theorem capacity_eq_Cn {z : ℝ} (hz : |z| < 1) :
    capacity z = SmallMean.Cn z := by
  have hz' := abs_lt.mp hz
  have hp : 1 + z ≠ 0 := by linarith
  have hm : 1 - z ≠ 0 := by linarith
  unfold capacity SmallMean.Cn H Real.binEntropy
  rw [show 1 - (1 - z) / 2 = (1 + z) / 2 by ring]
  simp only [Real.log_inv]
  rw [Real.log_div hm (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hp (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [log_two_pos.ne']
  ring

/-- Sharp enough for the signed split, with a rational coefficient. -/
theorem capacity_small_quadratic {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1 / 5) :
    capacity z ≤ (145 / 288) * z ^ 2 := by
  have hz1 : z < 1 := by linarith
  rw [capacity_eq_Cn (by rw [abs_of_nonneg hz]; exact hz1)]
  have hs : z ^ 2 ≤ 1 / 25 := by nlinarith
  have hn : 0 < 1 - z ^ 2 := by nlinarith
  have hf : z ^ 2 / (12 * (1 - z ^ 2)) ≤ (1 / 288 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - z ^ 2))).mpr
    nlinarith only [hs]
  have h := LowInformation.Cn_upper_sharp hz hz1
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg z)
  have he : z ^ 2 * (z ^ 2 / (12 * (1 - z ^ 2))) =
      z ^ 4 / (12 * (1 - z ^ 2)) := by ring
  rw [he] at hh
  linarith

theorem signed_ratio_lt_one {c q : ℝ} (hc : 1 / 3 ≤ c)
    (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) :
    |(13 * q / 6) / (2 * c)| < 1 := by
  have hcpos : 0 < c := by linarith
  have hk : |13 * q / 6| < 2 * c := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  exact (objective_minimum hcpos hk).1

/-- The exact attained loss is at most `4*q^2`, even on the larger range
`q <= 1/100`. In particular it covers the requested `q <= 8*10^-6` range. -/
theorem split_loss_le_four_sq {c q : ℝ} (hc : 1 / 3 ≤ c)
    (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ 4 * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (1 / 3 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (1 / 3 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  have he : (13 * q / 6) / (2 * (1 / 3 : ℝ)) = 13 * q / 4 := by ring
  rw [he] at h
  have hb := capacity_small_quadratic (z := 13 * q / 4)
    (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

/-- A split-uniform bound with no optimizer remaining. -/
theorem objective_ge_neg_four_sq {c q t : ℝ} (hc : 1 / 3 ≤ c)
    (hq : 0 ≤ q) (hq' : q ≤ 1 / 100) (ht : |t| < 1) :
    -(4 * q ^ 2) ≤ objective c (13 * q / 6) t := by
  have hcpos : 0 < c := by linarith
  have hz := signed_ratio_lt_one hc hq hq'
  have h := objective_lower hcpos.le hz ht
  have he : 2 * c * ((13 * q / 6) / (2 * c)) = 13 * q / 6 :=
    mul_div_cancel₀ _ (by positivity : 2 * c ≠ 0)
  rw [he] at h
  linarith [split_loss_le_four_sq hc hq hq']

theorem tilt_eq_A {t : ℝ} (ht : |t| < 1) : tilt t = SmallMean.A t := by
  have hh := abs_lt.mp ht
  unfold tilt SmallMean.A
  rw [Real.log_div (by linarith : 1 + t ≠ 0) (by linarith : 1 - t ≠ 0)]

theorem tilt_ge_self {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1) : t ≤ tilt t := by
  rw [tilt_eq_A (by rw [abs_of_nonneg ht]; exact ht')]
  exact SmallMean.A_lower ht ht'

@[simp] theorem barrier_neg (t : ℝ) : barrier (-t) = barrier t := by
  simp [barrier]

@[simp] theorem tilt_neg (t : ℝ) : tilt (-t) = -tilt t := by
  unfold tilt
  rw [show 1 + -t = 1 - t by ring, show 1 - -t = 1 + t by ring]
  ring

/-- The sign of the allocation is retained. The linear term helps for
nonnegative allocations; on the negative side its upper slope is absorbed
into the exact signed-split objective. -/
theorem signed_slope_split_ge_neg_four_sq {c q E A t : ℝ}
    (hc : 1 / 3 ≤ c) (hq : 0 ≤ q) (hq' : q ≤ 1 / 100)
    (hE : 0 < E) (hA : 0 ≤ A) (hA' : A ≤ 13 * q / (3 * E))
    (ht : |t| < 1) :
    -(4 * q ^ 2) ≤
      c * barrier t + E * t * A / 2 + (13 * q / 6) * (tilt t - t) := by
  by_cases ht0 : 0 ≤ t
  · have hb : 0 ≤ c * barrier t := mul_nonneg (by linarith) (barrier_nonneg ht)
    have hl : 0 ≤ E * t * A / 2 := by positivity
    have ht1 : t < 1 := (abs_lt.mp ht).2
    have hm : 0 ≤ (13 * q / 6) * (tilt t - t) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (tilt_ge_self ht0 ht1))
    nlinarith [sq_nonneg q]
  · have htneg : t ≤ 0 := le_of_not_ge ht0
    have hEA : E * A ≤ 13 * q / 3 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 3 * E)).mp hA'
      nlinarith
    have hlin := mul_le_mul_of_nonpos_left hEA htneg
    have hobj := objective_ge_neg_four_sq (t := -t) hc hq hq'
      (by simpa only [abs_neg] using ht)
    unfold objective at hobj
    rw [barrier_neg, tilt_neg] at hobj
    nlinarith

/-- Uniform positive barrier coefficient for the low-entropy endpoint
argument. The bound is valid throughout `0 <= d <= 1`. -/
theorem endpoint_coefficient_ge_third {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1) :
    1 / 3 ≤ (1 + d) / (2 * Real.log 2) - 13 * d / 12 := by
  have hlog : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1 + d)
  have hfrac : 5 * (1 + d) / 7 ≤ (1 + d) / (2 * Real.log 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).mpr
    nlinarith
  linarith

end GeneralCK.PsiSignedSplit

#print axioms GeneralCK.PsiSignedSplit.capacity_eq_Cn
#print axioms GeneralCK.PsiSignedSplit.capacity_small_quadratic
#print axioms GeneralCK.PsiSignedSplit.split_loss_le_four_sq
#print axioms GeneralCK.PsiSignedSplit.objective_ge_neg_four_sq
#print axioms GeneralCK.PsiSignedSplit.signed_slope_split_ge_neg_four_sq
#print axioms GeneralCK.PsiSignedSplit.endpoint_coefficient_ge_third

end


