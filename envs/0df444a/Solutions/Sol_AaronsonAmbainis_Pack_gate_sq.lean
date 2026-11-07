-- Prove2me | solution 1 for AaronsonAmbainis.Pack.gate_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:31.587181+00:00
-- url     : https://prove2.me/submissions/7d5b5d5d-a67e-42fa-89eb-cf079056ab04

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Gate

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
namespace AaronsonAmbainis.Pack
theorem _root_.solution (M : ℕ) :
    4 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2 ≤ (Real.pi * (M : ℝ) + 2) ^ 2 := by
  have hMr : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h0 : (0 : ℝ) ≤ Real.pi * (M : ℝ) / 2 := div_nonneg (mul_nonneg hpi.le hMr) two_pos.le
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have hlt : m < Real.pi * (M : ℝ) / 2 + 1 := by
    rw [hm]; exact Nat.ceil_lt_add_one h0
  have hm0 : (0 : ℝ) ≤ m := by
    rw [hm]; exact Nat.cast_nonneg _
  have h2 : 2 * m ≤ Real.pi * (M : ℝ) + 2 := by linarith
  have h3 : (2 * m) ^ 2 ≤ (Real.pi * (M : ℝ) + 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg two_pos.le hm0) h2 2
  calc 4 * m ^ 2 = (2 * m) ^ 2 := by ring
    _ ≤ (Real.pi * (M : ℝ) + 2) ^ 2 := h3
end AaronsonAmbainis.Pack
