-- Prove2me | solution 1 for Auto.sequenceDistance_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:44.519788+00:00
-- url     : https://prove2.me/submissions/b57c09ad-abca-44da-b7e8-0c0933e91b50

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a b : ℤ → ℝ} (h : SequenceDistance a b = 0) : a = b := by
  classical
  by_cases hab : ∃ k : ℕ, WithinSequenceDistance a b k
  · have hfind : (Nat.find hab : WithTop ℕ) = 0 := by
      simpa [SequenceDistance, hab] using h
    have hfind' : Nat.find hab = 0 := by exact_mod_cast hfind
    have hwithin : WithinSequenceDistance a b 0 := by
      simpa [hfind'] using Nat.find_spec hab
    funext j
    exact le_antisymm (by simpa using (hwithin j).1) (by simpa using (hwithin j).2)
  · simp [SequenceDistance, hab] at h
end Auto
