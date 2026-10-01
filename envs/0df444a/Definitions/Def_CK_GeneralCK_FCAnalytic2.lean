-- Prove2me | Definitions.Def_CK_GeneralCK_FCAnalytic2
-- name    : CK_GeneralCK_FCAnalytic2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:13:08.460987+00:00
-- url     : https://prove2.me/theorems/303540d0-daf0-42fd-87ab-21199b907023
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCAnalytic2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCAnalytic2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCAnalytic2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCAnalytic2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCAnalytic2.lean)

import Definitions.Def_CK_GeneralCK_OppositeCornerPhiAffineCertificate
import Definitions.Def_CK_GeneralCK_RadialConcavity
import Definitions.Def_CK_GeneralCK_Certificates_PilotData

-- ===== source module GeneralCK.FCAnalytic2 =====
section

/-!
# Lane F-C analytic layer, part 2
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCAnalytic2

open GeneralCK

theorem log_two_lb : (69 / 100 : ℝ) ≤ Real.log 2 := by
  have hl := Certificates.PilotData.log_two.1
  norm_num at hl
  linarith

theorem log_two_ub : Real.log 2 ≤ (7 / 10 : ℝ) := by
  have hl := Certificates.PilotData.log_two.2
  norm_num at hl
  linarith

/-- The symmetric entropy defect is at most `s²/(1-s)`.  Only `log x ≤ x - 1`
is used, three times. -/
theorem sym_defect_upper {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    (1 - s) * Real.log (1 - s) + (1 + s) * Real.log (1 + s) ≤ s ^ 2 / (1 - s) := by
  have hm : (0 : ℝ) < 1 - s := by linarith
  have hp : (0 : ℝ) < 1 + s := by linarith
  have hsq : (0 : ℝ) < 1 - s ^ 2 := by nlinarith only [hm, hp]
  have hA : Real.log (1 - s ^ 2) ≤ -s ^ 2 := by
    have h := Real.log_le_sub_one_of_pos hsq
    linarith
  have hB : Real.log (1 + s) ≤ s := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith
  have hC : -Real.log (1 - s) ≤ s / (1 - s) := by
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hm)
    rw [Real.log_inv] at hl
    have heq : (1 - s)⁻¹ - 1 = s / (1 - s) := by
      field_simp
      ring
    rwa [heq] at hl
  have hsplit : Real.log (1 - s ^ 2) = Real.log (1 - s) + Real.log (1 + s) := by
    rw [show (1 : ℝ) - s ^ 2 = (1 - s) * (1 + s) by ring]
    exact Real.log_mul hm.ne' hp.ne'
  have hid : (1 - s) * Real.log (1 - s) + (1 + s) * Real.log (1 + s)
      = Real.log (1 - s ^ 2) + s * Real.log (1 + s) - s * Real.log (1 - s) := by
    rw [hsplit]; ring
  have hfrac : s ^ 2 / (1 - s) = -s ^ 2 + (s * s + s * (s / (1 - s))) := by
    field_simp
    ring
  have h1 : s * Real.log (1 + s) ≤ s * s := mul_le_mul_of_nonneg_left hB hs
  have h2 : s * (-Real.log (1 - s)) ≤ s * (s / (1 - s)) := mul_le_mul_of_nonneg_left hC hs
  rw [hid, hfrac]
  have h2' : -(s * Real.log (1 - s)) = s * (-Real.log (1 - s)) := by ring
  linarith [hA, h1, h2, h2']

/-- `1 - H ((1-s)/2) ≤ (3/4) s²` on `[0, 1/1000]`; the exact limit is `1/(2 log 2)`. -/
theorem one_sub_H_near_half {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1 / 1000) :
    1 - H ((1 - s) / 2) ≤ (3 / 4) * s ^ 2 := by
  have hm : (0 : ℝ) < 1 - s := by linarith
  have hp : (0 : ℝ) < 1 + s := by linarith
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := log_two_lb
  have hcomp : (1 : ℝ) - (1 - s) / 2 = (1 + s) / 2 := by ring
  have hHid : H ((1 - s) / 2) * Real.log 2
      = Real.log 2 - ((1 - s) * Real.log (1 - s) + (1 + s) * Real.log (1 + s)) / 2 := by
    unfold H Real.binEntropy
    rw [div_mul_cancel₀ _ hLpos.ne']
    rw [hcomp]
    rw [show (((1 : ℝ) - s) / 2)⁻¹ = 2 / (1 - s) by
          rw [inv_div], show (((1 : ℝ) + s) / 2)⁻¹ = 2 / (1 + s) by rw [inv_div]]
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hm.ne',
      Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne']
    ring
  have hdef := sym_defect_upper hs (by linarith)
  have hbound : s ^ 2 / (1 - s) ≤ (3 / 2) * s ^ 2 * Real.log 2 := by
    rw [div_le_iff₀ hm]
    have hfac : (1 : ℝ) ≤ 3 / 2 * Real.log 2 * (1 - s) := by
      nlinarith only [hL, hs, hs1]
    nlinarith only [hfac, sq_nonneg s]
  have hfinal : (1 - (3 / 4) * s ^ 2) * Real.log 2 ≤ H ((1 - s) / 2) * Real.log 2 := by
    rw [hHid]
    nlinarith only [hdef, hbound]
  have hres := le_of_mul_le_mul_right hfinal hLpos
  linarith

theorem log_ten_lower : (16 / 5 : ℝ) * Real.log 2 ≤ Real.log 10 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (16 : ℕ))
    (by norm_num : (2 : ℝ) ^ (16 : ℕ) ≤ 10 ^ (5 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem log_eleven_lower : (17 / 5 : ℝ) * Real.log 2 ≤ Real.log 11 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (17 : ℕ))
    (by norm_num : (2 : ℝ) ^ (17 : ℕ) ≤ 11 ^ (5 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem H_eleventh_lower : (9 / 22 : ℝ) ≤ H (1 / 11) := by
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hratio : (1 : ℝ) / 11 ≤ Real.log (11 / 10) := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10 / 11)
    have hinv : Real.log (10 / 11 : ℝ) = -Real.log (11 / 10 : ℝ) := by
      rw [show (10 : ℝ) / 11 = ((11 : ℝ) / 10)⁻¹ by norm_num, Real.log_inv]
    rw [hinv] at hl
    linarith
  have hHid : H (1 / 11) * Real.log 2
      = (1 / 11) * Real.log 11 + (10 / 11) * Real.log (11 / 10) := by
    unfold H Real.binEntropy
    rw [div_mul_cancel₀ _ hLpos.ne']
    rw [show (1 : ℝ) - 1 / 11 = 10 / 11 by norm_num]
    rw [show ((1 : ℝ) / 11)⁻¹ = 11 by norm_num,
      show ((10 : ℝ) / 11)⁻¹ = 11 / 10 by norm_num]
  have hlow : (9 / 22 : ℝ) * Real.log 2 ≤ H (1 / 11) * Real.log 2 := by
    rw [hHid]
    nlinarith only [log_eleven_lower, hratio, log_two_ub]
  exact le_of_mul_le_mul_right hlow hLpos

theorem contact_two_upper : radialContact 2 1 ≤ (1 : ℝ) / 11 := by
  apply (radialContact_le_iff (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 11) (by norm_num : (1 : ℝ) / 11 ≤ 1 / 2)).2
  have h := H_eleventh_lower
  linarith

theorem J_eleventh_lower : (16 / 5 : ℝ) ≤ J (1 / 11) := by
  unfold J
  rw [show ((1 : ℝ) - 1 / 11) / (1 / 11) = 10 by norm_num]
  rw [le_div_iff₀ log_two_pos]
  linarith [log_ten_lower]

theorem F_two_one_lower : (32 / 5 : ℝ) ≤ F 2 1 := by
  have hm := J_antitone (radialContact_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1)) (by norm_num : (1 : ℝ) / 11 ≤ 1 / 2) contact_two_upper
  have hJ := J_eleventh_lower
  simp only [F, show (2 : ℝ) ≠ 0 by norm_num, ↓reduceIte]
  linarith

theorem F_zero_one : F 0 1 = 0 := by simp [F]

/-- Convexity in the radius plus `F 0 1 = 0` makes the slope from the origin monotone. -/
theorem F_slope_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : F x 1 / x ≤ F y 1 / y := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hw1 : (0 : ℝ) ≤ x / y := div_nonneg hx.le hy.le
  have hw0 : (0 : ℝ) ≤ 1 - x / y := by
    have hle : x / y ≤ 1 := (div_le_one hy).mpr hxy
    linarith
  have hsum : (1 - x / y) + x / y = 1 := by ring
  have hc := (convexOn_F_radius (h := 1) (by norm_num)).2
    (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp)
    (show y ∈ Set.Ici (0 : ℝ) from hy.le) hw0 hw1 hsum
  simp only [smul_eq_mul, mul_zero, zero_add, F_zero_one] at hc
  rw [div_mul_cancel₀ _ hy.ne'] at hc
  rw [div_le_div_iff₀ hx hy]
  have hstep : F x 1 * y ≤ x / y * F y 1 * y := mul_le_mul_of_nonneg_right hc hy.le
  have hcollapse : x / y * F y 1 * y = F y 1 * x := by field_simp
  linarith [hstep, hcollapse]

/-- Homogeneity normalisation: `F d E = E · F (d/E) 1`. -/
theorem F_scale_one {d E : ℝ} (hE : 0 < E) : F d E = E * F (d / E) 1 := by
  have h := F_scale (d / E) 1 E
  rw [mul_div_cancel₀ d hE.ne', mul_one] at h
  exact h

/-- Interior non-vacuity witness for the anchor: the contact radius sits
STRICTLY inside `(0, 1/11)`, so `F_two_one_lower` is not a boundary statement. -/
theorem F_two_one_interior_witness :
    0 < radialContact 2 1 ∧ radialContact 2 1 ≤ (1 : ℝ) / 11 ∧ (32 / 5 : ℝ) ≤ F 2 1 :=
  ⟨radialContact_pos (by norm_num) (by norm_num), contact_two_upper, F_two_one_lower⟩

#check @sym_defect_upper
#check @one_sub_H_near_half
#check @H_eleventh_lower
#check @F_two_one_lower
#check @F_slope_mono
#check @F_scale_one
#print axioms sym_defect_upper
#print axioms one_sub_H_near_half
#print axioms H_eleventh_lower
#print axioms F_two_one_lower
#print axioms F_slope_mono
#print axioms F_scale_one
#print axioms F_two_one_interior_witness

end GeneralCK.FCAnalytic2

end


