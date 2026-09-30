-- Prove2me | Definitions.Def_CK_GeneralCK_PsiParentContactEnvelope
-- name    : CK_GeneralCK_PsiParentContactEnvelope
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:17:24.730619+00:00
-- url     : https://prove2.me/theorems/b2bf74ba-8f0d-4776-a2b6-3ca59fe9eaf3
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiParentContactEnvelope` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiParentContactEnvelope` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiParentContactEnvelope` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiParentContactEnvelope (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiParentContactEnvelope.lean)

import Definitions.Def_CK_GeneralCK_PsiOuterEntropy2048

-- ===== source module GeneralCK.PsiParentContactEnvelope =====
section

/-!
# Sharper logarithmic radial-contact envelopes

An entropy estimate at the actual radial contact improves the earlier
quadratic odds bound. The resulting polynomial envelopes keep logarithmic
growth of the radial cost and are uniform over their whole ratio tails.
-/

namespace GeneralCK.PsiParentContactEnvelope

theorem contact_le_one_div_65 {q E : ℝ} (hq : 0 < q) (hE : 0 < E)
    (hr : 16 * E ≤ q) : radialContact q E ≤ 1 / 65 := by
  apply (radialContact_le_iff hq hE (by norm_num) (by norm_num)).mpr
  have hh := H_gt_parabola (p := (1 / 65 : ℝ)) (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hh.le hq.le
  nlinarith only [hm, hr, hE]

theorem entropy_logit_upper {v : ℝ} (hv : 0 < v) (hvu : v ≤ 1 / 65) :
    H v * Real.log 2 ≤ v * (Real.log ((1 - v) / v) + 65 / 64) := by
  have hvc : 0 < 1 - v := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hvc)
  have hm := mul_le_mul_of_nonneg_left hl hvc.le
  rw [show (1 - v) * ((1 - v)⁻¹ - 1) = v by field_simp; ring, Real.log_inv] at hm
  have hn : 0 ≤ -Real.log (1 - v) :=
    neg_nonneg.mpr (Real.log_nonpos hvc.le (by linarith))
  have hc : -Real.log (1 - v) ≤ (65 / 64) * v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hvu) hn]
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy,
    Real.log_div hvc.ne' hv.ne']
  simp only [Real.log_inv]
  nlinarith only [hc]

/-- The odds at the actual contact satisfy an improved implicit upper
bound. This uses the proved contact equation, not an inverse witness. -/
theorem contact_odds_implicit {q E : ℝ} (hq : 0 < q) (hE : 0 < E)
    (hr : 16 * E ≤ q) :
    Real.log 2 * ((1 - radialContact q E) / radialContact q E - 1) ≤
      (q / E) * (2 * Real.log (q / E) + 65 / 64) := by
  let v := radialContact q E
  let y := (1 - v) / v
  let x := q / E
  have hv : 0 < v := radialContact_pos hq hE
  have hvu : v ≤ 1 / 65 := contact_le_one_div_65 hq hE hr
  have hx : 0 < x := div_pos hq hE
  have hyv : v * y = 1 - v := by dsimp [y]; field_simp
  have hxe : E * x = q := mul_div_cancel₀ _ hE.ne'
  have heq := radialContact_equation hq hE
  have hh := mul_le_mul_of_nonneg_left (entropy_logit_upper hv hvu) hq.le
  have hc : Real.log 2 * (y - 1) ≤ x * (Real.log y + 65 / 64) := by
    apply (mul_le_mul_iff_right₀ (mul_pos hE hv)).mp
    change q * H v = E * (1 - 2 * v) at heq
    change q * (H v * Real.log 2) ≤ q * (v * (Real.log y + 65 / 64)) at hh
    calc
      (E * v) * (Real.log 2 * (y - 1)) = q * (H v * Real.log 2) := by
        linear_combination E * Real.log 2 * hyv - Real.log 2 * heq
      _ ≤ q * (v * (Real.log y + 65 / 64)) := hh
      _ = (E * v) * (x * (Real.log y + 65 / 64)) := by rw [← hxe]; ring
  have hF := PsiParentDominance.F_le_logarithmic_ratio8 hq hE (by linarith)
  have hid : F q E * Real.log 2 = q * Real.log y := by
    unfold F
    rw [if_neg hq.ne']
    change q * (Real.log y / Real.log 2) * Real.log 2 = _
    field_simp
  have hlog : Real.log y ≤ 2 * Real.log x := by
    have hh := (le_div_iff₀ log_two_pos).mp hF
    rw [hid] at hh
    apply (mul_le_mul_iff_left₀ hq).mp
    convert! hh using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left hlog hx.le
  change Real.log 2 * (y - 1) ≤ x * (2 * Real.log x + 65 / 64)
  nlinarith only [hc, hm]

/-- A general polynomial envelope obtained by a logarithmic tangent at
`2^n`. Only the sign of its remainder coefficient is required. -/
theorem contact_odds_polynomial {q E n r : ℝ} (hq : 0 < q) (hE : 0 < E)
    (hratio : 16 * E ≤ q) (hr : 0 < r)
    (hlog : Real.log r = n * Real.log 2)
    (hremainder : 0 ≤ 2 * (q / E) / r - 63 / 64) :
    (1 - radialContact q E) / radialContact q E ≤
      1 + 2 * n * (q / E) + (3 / 2) * (q / E) * (2 * (q / E) / r - 63 / 64) := by
  let x := q / E
  let y := (1 - radialContact q E) / radialContact q E
  have hx : 0 < x := div_pos hq hE
  have hL : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have hh := Certificates.PilotData.log_two.1
    norm_num at hh
    linarith
  have hc := contact_odds_implicit hq hE hratio
  change Real.log 2 * (y - 1) ≤ x * (2 * Real.log x + 65 / 64) at hc
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hr)
  rw [Real.log_div hx.ne' hr.ne', hlog] at hl
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * x by positivity)
  have hb : Real.log 2 * (y - 1 - 2 * n * x) ≤ x * (2 * x / r - 63 / 64) := by
    linear_combination hc + hm
  have hs := mul_nonneg (show 0 ≤ (3 / 2) * Real.log 2 - 1 by linarith)
    (mul_nonneg hx.le hremainder)
  apply (mul_le_mul_iff_right₀ log_two_pos).mp
  change Real.log 2 * y ≤ Real.log 2 * (1 + 2 * n * x + (3 / 2) * x * (2 * x / r - 63 / 64))
  nlinarith only [hb, hs]

theorem F_le_logarithmic_polynomial16 {q E : ℝ} (hq : 0 < q) (hE : 0 < E)
    (hr : 16 * E ≤ q) :
    F q E ≤ q * Real.log (1 + (837 / 128) * (q / E) + (3 / 16) * (q / E) ^ 2) /
      Real.log 2 := by
  have hx : 16 ≤ q / E := (le_div_iff₀ hE).mpr hr
  have hh := contact_odds_polynomial (n := 4) (r := 16) hq hE hr (by norm_num)
    (by rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num)
    (by linarith)
  have he : 1 + 2 * (4 : ℝ) * (q / E) + (3 / 2) * (q / E) * (2 * (q / E) / 16 - 63 / 64) =
      1 + (835 / 128) * (q / E) + (3 / 16) * (q / E) ^ 2 := by ring
  rw [he] at hh
  have hh' : (1 - radialContact q E) / radialContact q E ≤
      1 + (837 / 128) * (q / E) + (3 / 16) * (q / E) ^ 2 := by
    linarith only [hh, hx]
  have hv := radialContact_pos hq hE
  have hvh := radialContact_lt_half hq hE
  have hl := Real.log_le_log (div_pos (by linarith : 0 < 1 - radialContact q E) hv) hh'
  unfold F
  rw [if_neg hq.ne']
  unfold J
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hq.le) log_two_pos.le
  convert! h using 1 <;> ring

theorem F_le_logarithmic_polynomial64 {q E : ℝ} (hq : 0 < q) (hE : 0 < E)
    (hr : 32 * E ≤ q) :
    F q E ≤ q * Real.log (1 + (1347 / 128) * (q / E) + (3 / 64) * (q / E) ^ 2) /
      Real.log 2 := by
  have hx : 32 ≤ q / E := (le_div_iff₀ hE).mpr hr
  have hh := contact_odds_polynomial (n := 6) (r := 64) hq hE (by linarith) (by norm_num)
    (by rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; norm_num)
    (by linarith)
  have he : 1 + 2 * (6 : ℝ) * (q / E) + (3 / 2) * (q / E) * (2 * (q / E) / 64 - 63 / 64) =
      1 + (1347 / 128) * (q / E) + (3 / 64) * (q / E) ^ 2 := by ring
  rw [he] at hh
  have hv := radialContact_pos hq hE
  have hvh := radialContact_lt_half hq hE
  have hl := Real.log_le_log (div_pos (by linarith : 0 < 1 - radialContact q E) hv) hh
  unfold F
  rw [if_neg hq.ne']
  unfold J
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hq.le) log_two_pos.le
  convert! h using 1 <;> ring

end GeneralCK.PsiParentContactEnvelope

#print axioms GeneralCK.PsiParentContactEnvelope.contact_le_one_div_65
#print axioms GeneralCK.PsiParentContactEnvelope.entropy_logit_upper
#print axioms GeneralCK.PsiParentContactEnvelope.contact_odds_implicit
#print axioms GeneralCK.PsiParentContactEnvelope.contact_odds_polynomial
#print axioms GeneralCK.PsiParentContactEnvelope.F_le_logarithmic_polynomial16
#print axioms GeneralCK.PsiParentContactEnvelope.F_le_logarithmic_polynomial64

end


