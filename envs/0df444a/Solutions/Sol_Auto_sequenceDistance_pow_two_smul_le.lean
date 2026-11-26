-- Prove2me | solution 1 for Auto.sequenceDistance_pow_two_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:34.7029+00:00
-- url     : https://prove2.me/submissions/4da37ada-3d1d-4db7-ae81-d1df0338b249

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
public import Theorems.Thm_Auto_aux_spacedSequence_monotone
public import Theorems.Thm_Auto_aux_pow_two_mul_le_shift
public import Theorems.Thm_Auto_aux_pow_two_mul_shift_le
public import Theorems.Thm_Auto_aux_sequenceDistance_le_of_within

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a : ℤ → ℝ} (ha : SpacedSequence a) (h : ℤ) :
    SequenceDistance a (fun j => (2 : ℝ) ^ h * a j) ≤ (Int.natAbs h : WithTop ℕ) := by
  classical
  rcases Int.eq_nat_or_neg h with ⟨m, rfl | rfl⟩
  · have hpow : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have hwithin : WithinSequenceDistance a (fun j => (2 : ℝ) ^ (m : ℤ) * a j) m := by
      intro j
      constructor
      · calc
          a (j - m) ≤ a j := aux_spacedSequence_monotone ha (by omega)
          _ ≤ (2 : ℝ) ^ (m : ℤ) * a j := by
            rw [zpow_natCast]
            nlinarith [(ha j).1]
      · calc
          (2 : ℝ) ^ (m : ℤ) * a j = (2 : ℝ) ^ m * a j := by rw [zpow_natCast]
          _ ≤ a (j + m) := aux_pow_two_mul_le_shift ha j m
    simpa [zpow_natCast] using aux_sequenceDistance_le_of_within hwithin
  · have hpow_pos : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) _
    have hpow : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have hinv (j : ℤ) : (2 : ℝ) ^ (-(m : ℤ)) * a j = a j / (2 : ℝ) ^ m := by
      rw [zpow_neg, zpow_natCast]
      field_simp
    have hwithin : WithinSequenceDistance a (fun j => (2 : ℝ) ^ (-(m : ℤ)) * a j) m := by
      intro j
      constructor
      · change a (j - (m : ℤ)) ≤ (2 : ℝ) ^ (-(m : ℤ)) * a j
        rw [hinv j]
        apply (le_div_iff₀ hpow_pos).2
        simpa [mul_comm] using aux_pow_two_mul_shift_le ha j m
      · calc
          (2 : ℝ) ^ (-(m : ℤ)) * a j = a j / (2 : ℝ) ^ m := hinv j
          _ ≤ a j := by
            apply (div_le_iff₀ hpow_pos).2
            nlinarith [(ha j).1]
          _ ≤ a (j + m) := aux_spacedSequence_monotone ha (by omega)
    simpa [Int.natAbs_neg, zpow_natCast] using aux_sequenceDistance_le_of_within hwithin
end Auto
