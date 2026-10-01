-- Prove2me | Definitions.Def_Yukon_c5a0e39377dc346e7a8ed2ec
-- name    : Yukon_c5a0e39377dc346e7a8ed2ec
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:37.470483+00:00
-- url     : https://prove2.me/theorems/e54cce5f-77e0-46e3-9c35-2c68375adc85
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeNormalize6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeNormalize6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeNormalize6812.lean
--
--   provider-v8:02ced4d8f57c6590b9689f27052e2f9267423e2b39f07f6340c8a515c287774b
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODowMmNlZDRkOGY1N2M2NTkwYjk2ODlmMjcwNTJlMmY5MjY3NDIzZTJiMzlmMDdmNjM0MGM4YTUxNWMyODc3NzRiIiwiaGFzaCI6ImIzNjIwYTI0MjgyNWRkMjk3YjRhZmZlNGQ1MWE3NzhiZTFjY2FhYmEyN2JkODljZTBmODI3N2ZjNjRhZmNhZDQiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uX2M1YTBlMzkzNzdkYzM0NmU3YThlZDJlYyIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free bridge: normalizing a restricted valuation

The restriction of a place `ν` of a slice function field to the subfield `L0` is a
valuation `w` with value group `e ℤ`.  If it is nontrivial, `w = v ^ e` for a normalized
valuation `v` (`∃ x, v x = exp (-1)`), and pole/zero orders scale by `e`.
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open WithZero

variable {L : Type*} [Field L]

/-- Normalization of a nontrivial `ℤᵐ⁰`-valuation on a field. -/
theorem exists_normalization (w : Valuation L ℤᵐ⁰) (hnt : ∃ x : L, w x ≠ 0 ∧ w x ≠ 1) :
    ∃ (e : ℕ) (v : Valuation L ℤᵐ⁰), 1 ≤ e ∧ (∃ x, v x = exp (-1)) ∧
      ∀ x, w x = v x ^ e := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ x, w x = exp (-(n : ℤ)) := by
    obtain ⟨x, hx0, hx1⟩ := hnt
    have hm : w x = exp (w x).log := (exp_log hx0).symm
    have hm0 : (w x).log ≠ 0 := by intro h; rw [h, exp_zero] at hm; exact hx1 hm
    rcases lt_or_gt_of_ne hm0 with h | h
    · exact ⟨(-(w x).log).toNat, by omega, x, hm.trans (by congr 1; omega)⟩
    · refine ⟨((w x).log).toNat, by omega, x⁻¹, ?_⟩
      calc w x⁻¹ = (w x)⁻¹ := map_inv₀ _ _
        _ = (exp (w x).log)⁻¹ := by rw [exp_log hx0]
        _ = exp (-(((w x).log).toNat : ℤ)) := by rw [← exp_neg]; congr 1; omega
  set e := Nat.find hex with he_def
  have he : 0 < e ∧ ∃ x, w x = exp (-(e : ℤ)) := Nat.find_spec hex
  obtain ⟨u, hu⟩ := he.2
  have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu; exact exp_ne_zero hu.symm
  have hdvd : ∀ x, w x ≠ 0 → (e : ℤ) ∣ (w x).log := by
    intro x hx
    have hy : w (x * u ^ ((w x).log / e)) = exp ((w x).log % e) := by
      rw [map_mul, map_zpow₀, hu, ← exp_zsmul, ← exp_log hx, ← exp_add, log_exp]
      congr 1; rw [Int.emod_def]; simp only [smul_eq_mul]; ring
    by_contra hnd
    have hr0 : 0 ≤ (w x).log % e := Int.emod_nonneg _ (by omega)
    have hr1 : (w x).log % e ≠ 0 := fun h => hnd (Int.dvd_of_emod_eq_zero h)
    have hr2 : (w x).log % e < e := Int.emod_lt_of_pos _ (by omega)
    apply Nat.find_min hex (m := ((w x).log % e).toNat) (by omega)
    refine ⟨by omega, (x * u ^ ((w x).log / e))⁻¹, ?_⟩
    rw [map_inv₀, hy, ← exp_neg]; congr 1; omega
  let v : Valuation L ℤᵐ⁰ :=
    { toFun := fun x => if w x = 0 then 0 else exp ((w x).log / e)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by
        intro x y
        by_cases hx : w x = 0
        · simp [hx]
        by_cases hy : w y = 0
        · simp [hy]
        have hxy : w (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx hy
        show (if w (x * y) = 0 then 0 else exp ((w (x * y)).log / e)) =
          (if w x = 0 then 0 else exp ((w x).log / e)) *
            (if w y = 0 then 0 else exp ((w y).log / e))
        rw [if_neg hxy, if_neg hx, if_neg hy, map_mul, log_mul hx hy,
          Int.add_ediv_of_dvd_left (hdvd x hx), exp_add]
      map_add_le_max' := by
        intro x y
        by_cases hxy : w (x + y) = 0
        · simp [hxy]
        have hle := w.map_add x y
        have key : ∀ z, w (x + y) ≤ w z →
            (if w (x + y) = 0 then 0 else exp ((w (x + y)).log / e)) ≤
              (if w z = 0 then 0 else exp ((w z).log / e)) := by
          intro z hz
          have hz0 : w z ≠ 0 := by
            intro h; rw [h] at hz; exact hxy (le_antisymm hz zero_le)
          simp only [hxy, hz0, if_false, exp_le_exp]
          exact Int.ediv_le_ediv (by omega) ((log_le_log hxy hz0).2 hz)
        show (if w (x + y) = 0 then 0 else exp ((w (x + y)).log / e)) ≤
          max (if w x = 0 then 0 else exp ((w x).log / e))
            (if w y = 0 then 0 else exp ((w y).log / e))
        rcases le_total (w x) (w y) with h | h
        · exact (key y (hle.trans (max_eq_right h).le)).trans (le_max_right _ _)
        · exact (key x (hle.trans (max_eq_left h).le)).trans (le_max_left _ _) }
  have hv : ∀ x, v x = if w x = 0 then 0 else exp ((w x).log / e) := fun _ => rfl
  refine ⟨e, v, he.1, ⟨u, ?_⟩, fun x => ?_⟩
  · rw [hv, if_neg (by rw [hu]; exact exp_ne_zero), hu, log_exp]
    congr 1
    rw [Int.neg_ediv_of_dvd (dvd_refl _), Int.ediv_self (by omega)]
  · rw [hv]
    by_cases hx : w x = 0
    · rw [if_pos hx, hx, zero_pow (by omega)]
    · rw [if_neg hx, ← exp_nsmul, nsmul_eq_mul, Int.mul_ediv_cancel' (hdvd x hx), exp_log hx]

/-- Pole orders scale by `e` under `w = v ^ e`. -/
theorem poleOrder_pow (v w : Valuation L ℤᵐ⁰) (e : ℕ) (hw : ∀ x, w x = v x ^ e) (x : L) :
    max 0 (w x).log = e * max 0 (v x).log := by
  rw [hw, log_pow, nsmul_eq_mul, mul_max_of_nonneg _ _ (by positivity), mul_zero]

/-- Zero orders scale by `e` under `w = v ^ e`. -/
theorem zeroOrder_pow (v w : Valuation L ℤᵐ⁰) (e : ℕ) (hw : ∀ x, w x = v x ^ e) (x : L) :
    max 0 (-(w x).log) = e * max 0 (-(v x).log) := by
  rw [hw, log_pow, nsmul_eq_mul, mul_max_of_nonneg _ _ (by positivity), mul_zero, mul_neg]

end ProximityPrize.SubmissionLower.HFree6812


