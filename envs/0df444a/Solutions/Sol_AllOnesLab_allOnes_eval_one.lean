-- Prove2me | solution 1 for AllOnesLab.allOnes_eval_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:53:27.432088+00:00
-- url     : https://prove2.me/submissions/394ec9d2-c6df-45ad-a97c-3deb482cbcd4

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) : (allOnes n).eval 1 = (n + 1 : ZMod 2) := by
  have h : (allOnes n).eval 1 = ∑ _i ∈ Finset.range (n + 1), (1 : ZMod 2) := by
    rw [allOnes, eval_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
end AllOnesLab
