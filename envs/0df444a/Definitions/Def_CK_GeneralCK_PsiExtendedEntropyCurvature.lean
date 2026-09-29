-- Prove2me | Definitions.Def_CK_GeneralCK_PsiExtendedEntropyCurvature
-- name    : CK_GeneralCK_PsiExtendedEntropyCurvature
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:08:55.596164+00:00
-- url     : https://prove2.me/theorems/a7caa70d-684a-43e3-8cbf-a7f0df2c2f5d
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiExtendedEntropyCurvature` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiExtendedEntropyCurvature` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiExtendedEntropyCurvature` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiExtendedEntropyCurvature (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiExtendedEntropyCurvature.lean)

import Definitions.Def_CK_GeneralCK_EntropyCurvatureReduction
import Definitions.Def_CK_GeneralCK_EntropyParabola
import Definitions.Def_CK_GeneralCK_Certificates_PilotData

-- ===== source module GeneralCK.PsiExtendedEntropyCurvature =====
section

/-!
# Quantitative entropy curvature beyond a child's feasible cap

The active-psi factor-eight proof evaluates radialPhi at the common average
entropy, which can exceed one child's entropy cap. Feasible-fiber convexity
alone does not justify that step. Here we prove the quantitative eta curvature
bound on the entire small positive entropy interval.
-/

namespace GeneralCK.PsiExtendedEntropyCurvature
open Set

private theorem curvature_polynomial {v l n : ℝ} (hv : 0 < v)
    (hv1 : v < 1) (hl : 2 ≤ l) (hn : v * (l + 1) ≤ n) :
    v ^ 2 * (1 - v) ^ 2 * l ^ 3 ≤
      n ^ 2 * ((v ^ 2 + (1 - v) ^ 2) * l - (1 - 2 * v)) := by
  have hbase : 0 ≤ v * (l + 1) := by positivity
  have hsq : (v * (l + 1)) ^ 2 ≤ n ^ 2 := by nlinarith
  have hnum : (1 - v) ^ 2 * (l - 1) ≤
      (v ^ 2 + (1 - v) ^ 2) * l - (1 - 2 * v) := by
    nlinarith [mul_nonneg (sq_nonneg v) (show 0 ≤ l + 1 by linarith)]
  have hcoef : 0 ≤ (1 - v) ^ 2 * (l - 1) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hm := mul_le_mul hsq hnum hcoef (sq_nonneg n)
  have hp : l ^ 3 ≤ (l + 1) ^ 2 * (l - 1) := by nlinarith
  have hp' := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ v ^ 2 * (1 - v) ^ 2 by positivity)
  nlinarith only [hm, hp']

theorem entropy_natural_lower {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    v * (Real.log ((1 - v) / v) + 1) ≤ H v * Real.log 2 := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 - v by linarith)
  rw [Real.log_div (by linarith : 1 - v ≠ 0) hv.ne']
  unfold H Real.binEntropy
  rw [div_mul_cancel₀ _ log_two_pos.ne']
  simp only [Real.log_inv]
  nlinarith

theorem etaCurvature_lower_of_logit {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (hl : 2 ≤ Real.log ((1 - entropyInverse h) / entropyInverse h)) :
    1 / (Real.log 2 * h ^ 2) ≤ Scalar.etaCurvature h := by
  let v := entropyInverse h
  let l := Real.log ((1 - v) / v)
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hv1 : v < 1 := by linarith
  have hl' : 2 ≤ l := hl
  have he : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hn := entropy_natural_lower hv hv1
  rw [he] at hn
  have hp := curvature_polynomial hv hv1 hl' hn
  have hJ : J v = l / Real.log 2 := rfl
  have hden : 0 < v ^ 2 * (1 - v) ^ 2 * l ^ 3 := by positivity
  have hcurv : Scalar.etaCurvature h =
      Real.log 2 * ((v ^ 2 + (1 - v) ^ 2) * l - (1 - 2 * v)) /
        (v ^ 2 * (1 - v) ^ 2 * l ^ 3) := by
    change Scalar.curvatureNumerator v /
      ((Real.log 2 * v * (1 - v) * J v) ^ 2 * J v) = _
    unfold Scalar.curvatureNumerator
    rw [hJ]
    field_simp [log_two_pos.ne']
  rw [hcurv]
  apply (div_le_div_iff₀ (by positivity : 0 < Real.log 2 * h ^ 2) hden).mpr
  nlinarith only [hp]

theorem small_entropy_logit {h : ℝ} (hh : 0 < h) (hhi : h ≤ 11 / 100) :
    2 ≤ Real.log ((1 - entropyInverse h) / entropyInverse h) := by
  have hh1 : h < 1 := by linarith
  have hv : 0 < entropyInverse h := entropyInverse_pos hh hh1.le
  have hH := H_gt_parabola (p := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
  have hhc : h ≤ H (1 / 16) := by linarith
  have hvle := entropyInverse_mono hh.le (H_le_one (1 / 16)) hhc
  rw [entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 16)
    (by norm_num : (1 / 16 : ℝ) ≤ 1 / 2)] at hvle
  have hratio : (8 : ℝ) ≤ (1 - entropyInverse h) / entropyInverse h :=
    (le_div_iff₀ hv).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hratio
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [h8] at hlog
  have hL := Certificates.PilotData.log_two.1
  norm_num only [div_one] at hL
  linarith

/-- Manuscript (80), with the whole interval and its constant discharged. -/
theorem etaCurvature_lower {h : ℝ} (hh : 0 < h) (hhi : h ≤ 11 / 100) :
    1 / (Real.log 2 * h ^ 2) ≤ Scalar.etaCurvature h :=
  etaCurvature_lower_of_logit hh (by linarith) (small_entropy_logit hh hhi)

/-- Manuscript (81). No assumption of the form `h ≤ H ((1-r)/2)` occurs. -/
theorem radialPhi_curvature_lower {r h : ℝ} (hr : 0 < r)
    (hh : 0 < h) (hhi : h ≤ 11 / 100) :
    (1 / Real.log 2 - 13 * r / 6) / h ^ 2 ≤
      deriv (deriv (radialPhi r)) h := by
  have heta := etaCurvature_lower hh hhi
  have hF := deriv2_F_entropy_le hr hh
  rw [EntropyCurvature.deriv2_radialPhi_entropy hr hh (by linarith)]
  have he : (1 / Real.log 2 - 13 * r / 6) / h ^ 2 =
      1 / (Real.log 2 * h ^ 2) - 13 * r / (6 * h ^ 2) := by ring
  rw [he]
  linarith

theorem radialPhi_curvature_lower_nonneg {r h : ℝ} (hr : 0 ≤ r)
    (hh : 0 < h) (hhi : h ≤ 11 / 100) :
    (1 / Real.log 2 - 13 * r / 6) / h ^ 2 ≤
      deriv (deriv (radialPhi r)) h := by
  rcases hr.eq_or_lt with he | hp
  · rw [← he, EntropyCurvature.radialPhi_zero,
      (Scalar.hasDerivAt_deriv_eta hh (by linarith)).deriv]
    simpa only [mul_zero, zero_div, sub_zero, div_div] using etaCurvature_lower hh hhi
  · exact radialPhi_curvature_lower hp hh hhi

noncomputable def compensation (r : ℝ) : ℝ := 1 / Real.log 2 - 13 * r / 6

noncomputable def compensated (r h : ℝ) : ℝ :=
  radialPhi r h + compensation r * Real.log h

private theorem radialPhi_differentiable {r h : ℝ} (hr : 0 ≤ r)
    (hh : 0 < h) (hh1 : h < 1) : DifferentiableAt ℝ (radialPhi r) h := by
  rcases hr.eq_or_lt with he | hp
  · rw [← he, EntropyCurvature.radialPhi_zero]
    exact (hasDerivAt_eta hh hh1).differentiableAt
  · exact (EntropyCurvature.hasDerivAt_radialPhi_entropy hp hh hh1).differentiableAt

private theorem radialPhi_deriv_differentiable {r h : ℝ} (hr : 0 ≤ r)
    (hh : 0 < h) (hh1 : h < 1) : DifferentiableAt ℝ (deriv (radialPhi r)) h := by
  rcases hr.eq_or_lt with he | hp
  · rw [← he, EntropyCurvature.radialPhi_zero]
    exact (Scalar.hasDerivAt_deriv_eta hh hh1).differentiableAt
  · exact (EntropyCurvature.hasDerivAt_deriv_radialPhi_entropy hp hh hh1).differentiableAt

theorem hasDerivAt_compensated {r h : ℝ} (hr : 0 ≤ r)
    (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (compensated r)
      (deriv (radialPhi r) h + compensation r / h) h := by
  convert! (radialPhi_differentiable hr hh hh1).hasDerivAt.add
    ((Real.hasDerivAt_log hh.ne').const_mul (compensation r)) using 1

private theorem hasDerivAt_compensatedSlope {r h : ℝ} (hr : 0 ≤ r)
    (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (fun x => deriv (radialPhi r) x + compensation r / x)
      (deriv (deriv (radialPhi r)) h - compensation r / h ^ 2) h := by
  convert! (radialPhi_deriv_differentiable hr hh hh1).hasDerivAt.add
    ((hasDerivAt_const h (compensation r)).div (hasDerivAt_id h) hh.ne') using 1
  dsimp
  ring

/-- The logarithmic correction restores convexity on the whole small-entropy
interval, including entropies above a child's feasible cap. The coefficient
may be negative; its sign is not assumed. -/
theorem compensated_convexOn {r : ℝ} (hr : 0 ≤ r) :
    ConvexOn ℝ (Ioc 0 (11 / 100)) (compensated r) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 (11 / 100))
    (f' := fun h => deriv (radialPhi r) h + compensation r / h)
    (f'' := fun h => deriv (deriv (radialPhi r)) h - compensation r / h ^ 2)
  · intro h hh
    exact (hasDerivAt_compensated hr hh.1 (by linarith [hh.2])).continuousAt.continuousWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact (hasDerivAt_compensated hr hi.1 (by linarith [hi.2])).hasDerivWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact (hasDerivAt_compensatedSlope hr hi.1 (by linarith [hi.2])).hasDerivWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact sub_nonneg.mpr (radialPhi_curvature_lower_nonneg hr hi.1 hi.2)

/-- Quantitative tangent estimate used for the two child entropies. Unlike
feasible-fiber convexity, this applies with no relation between `r` and `E`. -/
theorem radialPhi_tangent_lower {r E h : ℝ} (hr : 0 ≤ r)
    (hE : 0 < E) (hEi : E ≤ 11 / 100) (hh : 0 < h) (hhi : h ≤ 11 / 100) :
    radialPhi r E + deriv (radialPhi r) E * (h - E) +
      compensation r * ((h - E) / E - Real.log (h / E)) ≤ radialPhi r h := by
  have hc := compensated_convexOn hr
  have hd := hasDerivAt_compensated hr hE (by linarith)
  have ht : (deriv (radialPhi r) E + compensation r / E) * (h - E) ≤
      compensated r h - compensated r E := by
    rcases lt_trichotomy E h with hlt | he | hgt
    · have hs := hc.le_slope_of_hasDerivAt ⟨hE, hEi⟩ ⟨hh, hhi⟩ hlt hd
      rw [slope_def_field] at hs
      exact (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    · simp [← he]
    · have hs := hc.slope_le_of_hasDerivAt ⟨hh, hhi⟩ ⟨hE, hEi⟩ hgt hd
      rw [slope_def_field] at hs
      have hm := (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
      nlinarith only [hm]
  unfold compensated at ht
  rw [Real.log_div hh.ne' hE.ne']
  linear_combination ht

end GeneralCK.PsiExtendedEntropyCurvature

#print axioms GeneralCK.PsiExtendedEntropyCurvature.etaCurvature_lower
#print axioms GeneralCK.PsiExtendedEntropyCurvature.radialPhi_curvature_lower
#print axioms GeneralCK.PsiExtendedEntropyCurvature.radialPhi_tangent_lower

end


