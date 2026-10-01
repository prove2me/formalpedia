-- Prove2me | Definitions.Def_CK_GeneralCK_FCAnalytic
-- name    : CK_GeneralCK_FCAnalytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:27:52.804399+00:00
-- url     : https://prove2.me/theorems/64a085a1-1bba-4785-8acd-b16d9c25e99c
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCAnalytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCAnalytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCAnalytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCAnalytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCAnalytic.lean)

import Definitions.Def_CK_GeneralCK_OppositeCornerPhiAffineCertificate
import Definitions.Def_CK_GeneralCK_PsiExtendedEntropyCurvature
import Definitions.Def_CK_GeneralCK_EntropyParabola

-- ===== source module GeneralCK.FCAnalytic =====
section

/-!
# Lane F-C analytic layer, part 1: the eta curvature upper bound

`eta'' h ≤ 2/h²` on `(0, 1/500]`.  The measured value of `h²·eta'' h` is ≈ 1.61,
so the constant `2` carries ≈ 24% headroom.  The route deliberately avoids
interval arithmetic on the singular quotient: it rewrites through the
non-singular closed form first and only then does rational algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCAnalytic

open GeneralCK

theorem log_two_lb : (69 / 100 : ℝ) ≤ Real.log 2 := by
  have hl := Certificates.PilotData.log_two.1
  norm_num at hl
  linarith

theorem log_two_ub : Real.log 2 ≤ (7 / 10 : ℝ) := by
  have hl := Certificates.PilotData.log_two.2
  norm_num at hl
  linarith

/-- Companion of `PsiExtendedEntropyCurvature.entropy_natural_lower`. -/
theorem entropy_natural_upper {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    H v * Real.log 2 ≤ v * (Real.log ((1 - v) / v) + 1 / (1 - v)) := by
  have hvc : 0 < 1 - v := by linarith
  have hlog : -Real.log (1 - v) ≤ v / (1 - v) := by
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hvc)
    rw [Real.log_inv] at hl
    have heq : (1 - v)⁻¹ - 1 = v / (1 - v) := by
      field_simp
      ring
    rwa [heq] at hl
  have hmul : v * (1 / (1 - v)) = v / (1 - v) := by
    field_simp
  rw [Real.log_div hvc.ne' hv.ne']
  unfold H Real.binEntropy
  rw [div_mul_cancel₀ _ log_two_pos.ne']
  simp only [Real.log_inv]
  nlinarith only [hlog, hmul]

/-- The parabola lower bound on `H` transfers to an upper bound on `entropyInverse`. -/
theorem entropyInverse_le_of_parabola {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (hp2 : p < 1 / 2)
    (hle : h ≤ 4 * p * (1 - p)) : entropyInverse h ≤ p := by
  have hH := H_gt_parabola hp hp2
  have hhc : h ≤ H p := by linarith
  have hmono := entropyInverse_mono hh.le (H_le_one p) hhc
  rwa [entropyInverse_H_lower hp.le hp2.le] at hmono

theorem entropyInverse_small {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 500) :
    entropyInverse h ≤ 1 / 1000 :=
  entropyInverse_le_of_parabola hh (by norm_num) (by norm_num) (by linarith)

theorem log_999_lower : (99 / 10 : ℝ) * Real.log 2 ≤ Real.log 999 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (99 : ℕ))
    (by norm_num : (2 : ℝ) ^ (99 : ℕ) ≤ 999 ^ (10 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

/-- On `(0, 1/500]` the logit of the entropy inverse is at least `68/10`. -/
theorem logit_large {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 500) :
    (68 / 10 : ℝ) ≤ Real.log ((1 - entropyInverse h) / entropyInverse h) := by
  have hh1 : h < 1 := by linarith
  have hv : 0 < entropyInverse h := entropyInverse_pos hh hh1.le
  have hvle := entropyInverse_small hh hhi
  have hratio : (999 : ℝ) ≤ (1 - entropyInverse h) / entropyInverse h :=
    (le_div_iff₀ hv).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 999) hratio
  linarith [log_999_lower, log_two_lb]

/-- Non-singular closed form of the eta curvature. -/
theorem etaCurvature_form {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    Scalar.etaCurvature h =
      Real.log 2 * ((entropyInverse h ^ 2 + (1 - entropyInverse h) ^ 2) *
          Real.log ((1 - entropyInverse h) / entropyInverse h) -
          (1 - 2 * entropyInverse h)) /
        (entropyInverse h ^ 2 * (1 - entropyInverse h) ^ 2 *
          Real.log ((1 - entropyInverse h) / entropyInverse h) ^ 3) := by
  have hv : 0 < entropyInverse h := entropyInverse_pos hh hh1.le
  have hvhalf : entropyInverse h < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hJ : J (entropyInverse h)
      = Real.log ((1 - entropyInverse h) / entropyInverse h) / Real.log 2 := rfl
  have hjne := (J_pos hv hvhalf).ne'
  have hlne : Real.log ((1 - entropyInverse h) / entropyInverse h) ≠ 0 := by
    intro hz
    exact hjne (by simp [J, hz])
  change Scalar.curvatureNumerator (entropyInverse h) /
    ((Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h)) ^ 2 *
      J (entropyInverse h)) = _
  unfold Scalar.curvatureNumerator
  rw [hJ]
  field_simp [log_two_pos.ne', hv.ne', show (1 : ℝ) - entropyInverse h ≠ 0 by linarith]

/-- `eta'' h ≤ 2/h²` on `(0, 1/500]`.  Measured value of `h² · eta'' h` ≈ 1.61. -/
theorem etaCurvature_upper {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 500) :
    Scalar.etaCurvature h ≤ 2 / h ^ 2 := by
  have hh1 : h < 1 := by linarith
  set v := entropyInverse h with hvdef
  set l := Real.log ((1 - v) / v) with hldef
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hv1 : v < 1 := by linarith
  have hvle : v ≤ 1 / 1000 := entropyInverse_small hh hhi
  have hl : (68 / 10 : ℝ) ≤ l := logit_large hh hhi
  have he : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hvc : 0 < 1 - v := by linarith
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := log_two_lb
  have hup := entropy_natural_upper hv hv1
  rw [he] at hup
  have hinv : 1 / (1 - v) ≤ 101 / 100 := by
    rw [div_le_div_iff₀ hvc (by norm_num)]
    linarith
  have hkey : h * Real.log 2 ≤ v * (l + 101 / 100) := by
    have hstep : v * (l + 1 / (1 - v)) ≤ v * (l + 101 / 100) := by
      nlinarith only [hinv, hv]
    linarith
  have hAnn : 0 ≤ h * Real.log 2 := by positivity
  have hBnn : 0 ≤ v * (l + 101 / 100) := by nlinarith only [hv, hl]
  have hsq0 : (h * Real.log 2) ^ 2 ≤ (v * (l + 101 / 100)) ^ 2 := by
    nlinarith only [hkey, hAnn, hBnn]
  have hsq : h ^ 2 * Real.log 2 ^ 2 ≤ v ^ 2 * (l + 101 / 100) ^ 2 := by
    have e1 : (h * Real.log 2) ^ 2 = h ^ 2 * Real.log 2 ^ 2 := by ring
    have e2 : (v * (l + 101 / 100)) ^ 2 = v ^ 2 * (l + 101 / 100) ^ 2 := by ring
    linarith [hsq0, e1, e2]
  rw [etaCurvature_form hh hh1]
  have hden : 0 < v ^ 2 * (1 - v) ^ 2 * l ^ 3 := by positivity
  have hh2pos : (0 : ℝ) < h ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hh2pos]
  set num := (v ^ 2 + (1 - v) ^ 2) * l - (1 - 2 * v) with hnumdef
  have hlnn : (0 : ℝ) ≤ l := by linarith
  have hvv : (0 : ℝ) ≤ 2 * v - 2 * v ^ 2 := by nlinarith only [hv, hv1]
  have hnumnn : 0 ≤ num := by
    rw [hnumdef]
    nlinarith only [hl, hv, hvhalf]
  have hnumle : num ≤ l := by
    rw [hnumdef]
    nlinarith only [mul_nonneg hvv hlnn, hv, hvhalf, hlnn]
  have h1mv : (999 / 1000 : ℝ) ≤ 1 - v := by linarith
  have hsq1mv : (998001 / 1000000 : ℝ) ≤ (1 - v) ^ 2 := by nlinarith only [h1mv, hvc]
  have hquad : (l + 101 / 100) ^ 2 ≤ (137724 / 100000) * l ^ 2 := by
    nlinarith only [hl, sq_nonneg (l - 68 / 10)]
  have hpoly : (l + 101 / 100) ^ 2 ≤ (138 / 100) * (1 - v) ^ 2 * l ^ 2 := by
    nlinarith only [hquad, hsq1mv, sq_nonneg l]
  have hmain : Real.log 2 * (Real.log 2 * num * h ^ 2)
      ≤ Real.log 2 * (2 * (v ^ 2 * (1 - v) ^ 2 * l ^ 3)) := by
    have e1 : Real.log 2 * (Real.log 2 * num * h ^ 2) = num * (h ^ 2 * Real.log 2 ^ 2) := by
      ring
    have hposA : (0 : ℝ) ≤ h ^ 2 * Real.log 2 ^ 2 := by positivity
    have hposB : (0 : ℝ) ≤ v ^ 2 * (l + 101 / 100) ^ 2 := by positivity
    have hstep1 : num * (h ^ 2 * Real.log 2 ^ 2) ≤ l * (v ^ 2 * (l + 101 / 100) ^ 2) := by
      nlinarith only [hnumnn, hnumle, hsq, hposA, hposB, hlnn]
    have hstep2 : l * (v ^ 2 * (l + 101 / 100) ^ 2)
        ≤ l * (v ^ 2 * ((138 / 100) * (1 - v) ^ 2 * l ^ 2)) := by
      have hc : (0 : ℝ) ≤ l * v ^ 2 := by positivity
      nlinarith only [hpoly, hc]
    have hstep3 : l * (v ^ 2 * ((138 / 100) * (1 - v) ^ 2 * l ^ 2))
        ≤ Real.log 2 * (2 * (v ^ 2 * (1 - v) ^ 2 * l ^ 3)) := by
      have hbase : (0 : ℝ) ≤ v ^ 2 * (1 - v) ^ 2 * l ^ 3 := by positivity
      nlinarith only [hL, hbase]
    rw [e1]
    linarith [hstep1, hstep2, hstep3]
  exact le_of_mul_le_mul_left hmain hLpos

/-- Interior non-vacuity witness: `h = 1/1000` lies STRICTLY inside `(0, 1/500)`
and its entropy inverse lies STRICTLY inside `(0, 1/1000)`, so the hypotheses of
`etaCurvature_upper` are met off every boundary face of the region. -/
theorem etaCurvature_upper_interior_witness :
    (0 : ℝ) < 1 / 1000 ∧ (1 / 1000 : ℝ) < 1 / 500 ∧
      0 < entropyInverse (1 / 1000) ∧ entropyInverse (1 / 1000) < 1 / 1000 ∧
      Scalar.etaCurvature (1 / 1000) ≤ 2 / (1 / 1000 : ℝ) ^ 2 := by
  have hpos : 0 < entropyInverse (1 / 1000 : ℝ) :=
    entropyInverse_pos (by norm_num) (by norm_num)
  have hlt : entropyInverse (1 / 1000 : ℝ) ≤ 1 / 2000 :=
    entropyInverse_le_of_parabola (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by norm_num, by norm_num, hpos, by linarith,
    etaCurvature_upper (by norm_num) (by norm_num)⟩

#check @entropy_natural_upper
#check @entropyInverse_le_of_parabola
#check @logit_large
#check @etaCurvature_form
#check @etaCurvature_upper
#check @etaCurvature_upper_interior_witness
#print axioms entropy_natural_upper
#print axioms entropyInverse_le_of_parabola
#print axioms logit_large
#print axioms etaCurvature_form
#print axioms etaCurvature_upper
#print axioms etaCurvature_upper_interior_witness

end GeneralCK.FCAnalytic

end


