-- Prove2me | Definitions.Def_Width4HSG_Main_Splice
-- name    : Width4HSG_Main_Splice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:17:59.425269+00:00
-- url     : https://prove2.me/theorems/07bef5b1-5842-4343-be0c-406e89f42e56
-- title:
--   Position-preserving width reduction and iterated splices
-- statement:
--   The width-four splice uses zeros before a, the first source word from a through b, and the second source word afterwards. The t-fold aligned splice uses t source words and nondecreasing cuts from zero to n. Cuts may coincide, so empty blocks are allowed, and each bit retains its original coordinate.
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, p. 85, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_ROBP

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

def widthFourSplice {n : ℕ} (H K : Finset (Bits n)) : Finset (Bits n) := by
  classical
  exact Finset.univ.filter (fun z => ∃ a b : Fin (n+1), a ≤ b ∧
    ∃ x ∈ H, ∃ y ∈ K, ∀ i, z i =
      if i.val < a.val then false else if i.val < b.val then x i else y i)

def alignedSplice {n : ℕ} (H : Set (Bits n)) (t : ℕ) : Set (Bits n) :=
  {z | ∃ cuts : Fin (t+1) → Fin (n+1),
    cuts 0 = 0 ∧ cuts (Fin.last t) = Fin.last n ∧ Monotone cuts ∧
    ∃ x : Fin t → Bits n, (∀ j, x j ∈ H) ∧
      ∀ (j : Fin t) (i : Fin n),
        (cuts j.castSucc).val ≤ i.val → i.val < (cuts j.succ).val → z i = x j i}

end Width4HSG.Main


