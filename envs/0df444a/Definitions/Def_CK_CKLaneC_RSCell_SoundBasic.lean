-- Prove2me | Definitions.Def_CK_CKLaneC_RSCell_SoundBasic
-- name    : CK_CKLaneC_RSCell_SoundBasic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T05:37:35.990729+00:00
-- url     : https://prove2.me/theorems/a3a5cfd0-c80c-47d1-910b-813466b7fe8c
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSCell.SoundBasic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSCell.SoundBasic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSCell.SoundBasic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSCell.SoundBasic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSCell/SoundBasic.lean)

import Definitions.Def_CK_CKLaneC_RSCell_Defs
import Definitions.Def_CK_CKLaneC_RSEnc_Residual
import Mathlib.Analysis.Complex.ExponentialBounds

-- ===== source module CKLaneC.RSCell.SoundBasic =====
section

/-!
# Lane C, RA-stat interior: soundness of the cell checker, part 1 (constants, h(δ), J)
-/

namespace CKLaneC.RSCell

open CKLaneC.TM3 GeneralCK

theorem hone : 0 < one := by unfold one; exact pow_pos (by norm_num) _
theorem hone' : (0 : ℝ) < (one : ℝ) := by exact_mod_cast hone
theorem hne : (one : ℝ) ≠ 0 := hone'.ne'
theorem hP : 3 ≤ P := by norm_num

theorem ONEi_div : ((ONEi : ℤ) : ℝ) / (one : ℝ) = 1 := by
  unfold ONEi; rw [Int.cast_natCast]; exact div_self hne

theorem half_mul_two : (one / 2 : ℕ) * 2 = one := by decide

theorem half_cast : ((one / 2 : ℕ) : ℝ) = (one : ℝ) / 2 := by
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]; exact_mod_cast half_mul_two

theorem half_div : ((half : ℤ) : ℝ) / (one : ℝ) = 1 / 2 := by
  unfold half; rw [Int.cast_natCast, half_cast, div_right_comm, div_self hne]

/-! ## Convenience forms of the TM lemmas -/

theorem C_mul {A B : TM} {f g : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) (hB : Contains one B g) :
    Contains one (mul A B) (fun x y z => f x y z * g x y z) := Contains.mul hone N hA hB

theorem C_recip {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) :
    Contains one (recip A) (fun x y z => (f x y z)⁻¹) := Contains.recip hone N hA

theorem C_log {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) :
    Contains one (log A) (fun x y z => Real.log (f x y z)) := Contains.log P hP N hA

theorem C_addOne {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) :
    Contains one (TM.addc A ONEi) (fun x y z => f x y z + 1) := by
  have := Contains.addc hA ONEi
  refine Contains.congr this (fun x y z _ _ _ => ?_)
  rw [ONEi_div]

theorem C_oneSub {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) :
    Contains one (TM.addc (TM.neg A) ONEi) (fun x y z => 1 - f x y z) := by
  have := C_addOne (Contains.neg hA)
  refine Contains.congr this (fun x y z _ _ _ => ?_)
  ring

theorem C_half {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) :
    Contains one (mulc A half) (fun x y z => f x y z / 2) := by
  have := Contains.mulc hone hA half
  refine Contains.congr this (fun x y z _ _ _ => ?_)
  rw [half_div]; ring

/-! ## Constants -/

theorem LN2_P_ge : ((one / 2 : ℕ) : ℤ) ≤ LN2 P := by decide +kernel

theorem Lc_contains : Contains one Lc (fun _ _ _ => Real.log 2) := by
  apply Contains.const
  have h := LN2_sound P (by norm_num)
  have e : Real.log 2 - ((LN2 P : ℤ) : ℝ) / (one : ℝ) = -(((LN2 P : ℤ) : ℝ) - 2 ^ P * Real.log 2) / (one : ℝ) := by
    have : ((one : ℕ) : ℝ) = (2 : ℝ) ^ P := by simp [one]
    rw [this]; field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos hone']
  exact div_le_div_of_nonneg_right h hone'.le

theorem invLc_contains : Contains one invLc (fun _ _ _ => 1 / Real.log 2) := by
  apply Contains.const
  have hL := LN2_sound P (by norm_num)
  have hlog := Real.log_two_gt_d9
  have hlogpos : (0 : ℝ) < Real.log 2 := by linarith
  have hge : ((one : ℝ) / 2) ≤ ((LN2 P : ℤ) : ℝ) := by
    have := LN2_P_ge
    have h2 : (((one / 2 : ℕ) : ℤ) : ℝ) = (one : ℝ) / 2 := by rw [Int.cast_natCast, half_cast]
    rw [← h2]; exact_mod_cast this
  have hLpos : (0 : ℝ) < ((LN2 P : ℤ) : ℝ) := by linarith [hone']
  have hLposZ : (0 : ℤ) < LN2 P := by exact_mod_cast hLpos
  have hq := ediv_err (((one * one : ℕ) : ℤ)) (LN2 P) hLposZ
  have hcast : ((one : ℕ) : ℝ) = (2 : ℝ) ^ P := by simp [one]
  set Lz := ((LN2 P : ℤ) : ℝ)
  set q := ((((one * one : ℕ) : ℤ) / LN2 P : ℤ) : ℝ)
  -- |1/L - one/Lz| ≤ LN2E/(L Lz)
  have h1 : |1 / Real.log 2 - (one : ℝ) / Lz| ≤ (LN2E P : ℝ) * 3 / one := by
    have e : 1 / Real.log 2 - (one : ℝ) / Lz = (Lz - one * Real.log 2) / (Real.log 2 * Lz) := by
      field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hlogpos hLpos)]
    rw [hcast]
    have hE0 : (0 : ℝ) ≤ (LN2E P : ℝ) := Nat.cast_nonneg _
    rw [div_le_div_iff₀ (mul_pos hlogpos hLpos) (by positivity)]
    have hkey : (2 : ℝ) ^ P ≤ 3 * (Real.log 2 * Lz) := by
      obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (2 : ℝ) ^ P := ⟨_, rfl⟩
      have hXpos : 0 < X := by rw [hX]; positivity
      have h1 : X / 2 ≤ Lz := by rw [hX, ← hcast]; exact hge
      rw [← hX]
      have h2 : X / 2 * 0.6931471803 ≤ Lz * Real.log 2 := mul_le_mul h1 hlog.le (by norm_num) (by linarith)
      have h3 : Lz * Real.log 2 = Real.log 2 * Lz := mul_comm _ _
      linarith
    calc |Lz - 2 ^ P * Real.log 2| * 2 ^ P ≤ (LN2E P : ℝ) * 2 ^ P :=
          mul_le_mul_of_nonneg_right hL (by positivity)
      _ ≤ (LN2E P : ℝ) * (3 * (Real.log 2 * Lz)) := mul_le_mul_of_nonneg_left hkey hE0
      _ = (LN2E P : ℝ) * 3 * (Real.log 2 * Lz) := by ring
  have h2 : |(one : ℝ) / Lz - q / one| ≤ 1 / one := by
    have e : (one : ℝ) / Lz - q / one = -(q - (((one * one : ℕ) : ℤ) : ℝ) / Lz) / one := by
      push_cast; field_simp; ring
    rw [e, abs_div, abs_neg, abs_of_pos hone']
    exact div_le_div_of_nonneg_right hq hone'.le
  calc |1 / Real.log 2 - q / one|
      ≤ |1 / Real.log 2 - (one : ℝ) / Lz| + |(one : ℝ) / Lz - q / one| := abs_sub_le _ _ _
    _ ≤ (LN2E P : ℝ) * 3 / one + 1 / one := add_le_add h1 h2
    _ = ((1 + 3 * LN2E P : ℕ) : ℝ) / one := by push_cast; ring

/-! ## `h(δ)` and `J` in log form -/

theorem hdelta_eq {δ : ℝ} (h1 : -1 < δ) (h2 : δ < 1) :
    CKLaneC.RSEnc.hdelta δ
      = 1 - ((δ + 1) * Real.log (δ + 1) + (1 - δ) * Real.log (1 - δ)) * (1 / Real.log 2) / 2 := by
  unfold CKLaneC.RSEnc.hdelta H
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have ha : (0 : ℝ) < 1 - δ := by linarith
  have hb : (0 : ℝ) < δ + 1 := by linarith
  rw [Real.binEntropy]
  have e1 : 1 - (1 - δ) / 2 = (δ + 1) / 2 := by ring
  rw [e1, Real.log_inv, Real.log_inv, Real.log_div ha.ne' (by norm_num), Real.log_div hb.ne' (by norm_num)]
  field_simp
  ring

theorem C_hOfLogs {D lp lm : TM} {df : ℝ → ℝ → ℝ → ℝ} (hD : Contains one D df)
    (hlp : Contains one lp (fun x y z => Real.log (df x y z + 1)))
    (hlm : Contains one lm (fun x y z => Real.log (1 - df x y z)))
    (hr : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → -1 < df x y z ∧ df x y z < 1) :
    Contains one (hOfLogs D lp lm) (fun x y z => CKLaneC.RSEnc.hdelta (df x y z)) := by
  have hs := Contains.add (C_mul (C_addOne hD) hlp) (C_mul (C_oneSub hD) hlm)
  have h := C_oneSub (C_half (C_mul hs invLc_contains))
  refine Contains.congr h (fun x y z hx hy hz => ?_)
  obtain ⟨h1, h2⟩ := hr x y z hx hy hz
  rw [hdelta_eq h1 h2]

theorem J_eq_logs {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    J v = (Real.log (2 * (1 - v)) - Real.log (2 * v)) * (1 / Real.log 2) := by
  unfold J
  rw [Real.log_div (by linarith) hv.ne', Real.log_mul (by norm_num) (by linarith),
    Real.log_mul (by norm_num) hv.ne']
  ring

end CKLaneC.RSCell

end


