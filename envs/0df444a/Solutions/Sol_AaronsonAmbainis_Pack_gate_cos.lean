-- Prove2me | solution 1 for AaronsonAmbainis.Pack.gate_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:30.971738+00:00
-- url     : https://prove2.me/submissions/a59c57b2-a1e2-4fcb-943d-effd7b4c4a86

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Gate

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
namespace AaronsonAmbainis.Pack
theorem _root_.solution (M : ℕ) (hM : 0 < M) :
    ((M ^ 2 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ))) ≤ 2 := by
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- abbreviate the real number `m`
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have hle : Real.pi * (M : ℝ) / 2 ≤ m := by
    rw [hm]; exact Nat.le_ceil _
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (div_pos (mul_pos hpi hMr) two_pos) hle
  -- the cosine bound
  have hcos : 1 - (Real.pi / m) ^ 2 / 2 ≤ Real.cos (Real.pi / m) :=
    Real.one_sub_sq_div_two_le_cos
  have h1 : 1 - Real.cos (Real.pi / m) ≤ (Real.pi / m) ^ 2 / 2 := by linarith
  -- `M π / m ≤ 2`
  have h3 : (M : ℝ) * Real.pi / m ≤ 2 := by
    rw [div_le_iff₀ hmpos]; linarith
  have h4 : 0 ≤ (M : ℝ) * Real.pi / m :=
    div_nonneg (mul_nonneg hMr.le hpi.le) hmpos.le
  have h5 : ((M : ℝ) * Real.pi / m) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ h4 h3 2
  have h6 : (M : ℝ) ^ 2 * ((Real.pi / m) ^ 2 / 2) = ((M : ℝ) * Real.pi / m) ^ 2 / 2 := by
    ring
  have hM2 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := sq_nonneg _
  have hcast : ((M ^ 2 : ℕ) : ℝ) = (M : ℝ) ^ 2 := by push_cast; ring
  rw [hcast]
  calc (M : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m))
      ≤ (M : ℝ) ^ 2 * ((Real.pi / m) ^ 2 / 2) := mul_le_mul_of_nonneg_left h1 hM2
    _ = ((M : ℝ) * Real.pi / m) ^ 2 / 2 := h6
    _ ≤ 2 := by linarith
end AaronsonAmbainis.Pack
