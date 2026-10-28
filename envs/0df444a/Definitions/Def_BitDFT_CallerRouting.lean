-- Prove2me | Definitions.Def_BitDFT_CallerRouting
-- name    : BitDFT_CallerRouting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:07:36.501698+00:00
-- url     : https://prove2.me/theorems/cf63bb41-013c-4f38-abff-954433f94782
-- title:
--   Reserve child-machine banks by a fixed tape permutation
-- statement:
--   For every nonnegative integer k, a permutation of 5+k tape indices fixes native input and output indices 0 and 1, sends the preprocessor workspace indices 2,3,4 to k+2,k+3,k+4, and sends the k appended fresh tapes to the child-bank indices 2 through k+1. The inverse is explicit, and all index and inverse laws are proved.
-- source:
--   Physical tape layout for composing the proved preprocessor with an arbitrary k-tape Fourier machine.

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace BitDFT.CallerRouting

/-- Keep native tapes 0 and 1 fixed, move the preprocessor's three workspace
    tapes behind the child's k reserved tapes, and put the extra tapes in the
    child bank positions. -/
def permutation (k : ℕ) : Fin (5+k) ≃ Fin (5+k) where
  toFun i := ⟨if i.val < 2 then i.val else if i.val < 5 then i.val+k else i.val-3, by
    have := i.isLt
    split_ifs <;> omega⟩
  invFun i := ⟨if i.val < 2 then i.val else if i.val < k+2 then i.val+3 else i.val-k, by
    have := i.isLt
    split_ifs <;> omega⟩
  left_inv := by
    intro i
    apply Fin.ext
    dsimp
    split_ifs <;> omega
  right_inv := by
    intro i
    apply Fin.ext
    dsimp
    split_ifs <;> omega

theorem native_zero (k : ℕ) : permutation k ⟨0,by omega⟩ = ⟨0,by omega⟩ := by
  apply Fin.ext
  simp [permutation]

theorem native_one (k : ℕ) : permutation k ⟨1,by omega⟩ = ⟨1,by omega⟩ := by
  apply Fin.ext
  simp [permutation]

theorem workspace (k : ℕ) (i : Fin (5+k)) (hlo : 2 ≤ i.val) (hhi : i.val < 5) :
    (permutation k i).val = i.val+k := by
  dsimp [permutation]
  split_ifs <;> omega

theorem child_bank (k : ℕ) (i : Fin (5+k)) (hlo : 5 ≤ i.val) :
    (permutation k i).val = i.val-3 := by
  dsimp [permutation]
  split_ifs <;> omega

end BitDFT.CallerRouting


