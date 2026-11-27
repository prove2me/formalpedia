-- Prove2me | solution 1 for AndricaConjecture.andrica_gap_form
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jakevej
-- created : 2026-11-27T03:18:57.151399+00:00
-- url     : https://prove2.me/submissions/859aa686-e157-4494-96c0-aba81a923890
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AndricaConjecture_andrica_conjecture
import Theorems.Thm_AndricaConjecture_andrica_iff_gap_form

theorem solution (n : Nat) :
    (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : Real) <
      2 * Real.sqrt (Nat.nth Nat.Prime n : Real) + 1 := by
  exact (AndricaConjecture.andrica_iff_gap_form n).mp
    (AndricaConjecture.andrica_conjecture n)
