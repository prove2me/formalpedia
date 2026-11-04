-- Prove2me | Definitions.Def_Submission_ThreeSum_MaskErase
-- name    : Submission_ThreeSum_MaskErase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:32.211792+00:00
-- url     : https://prove2.me/theorems/53658a0a-ba41-4ad1-bf84-d25652c228cd
-- title:
--   Mask Erase
-- statement:
--   Definitions and structural lemmas for Mask Erase, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean

import Definitions.Def_Submission_ThreeSum_SubsetAddress
set_option autoImplicit false
namespace ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
def eraseMask : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | L+1, a, m =>
    if m < 2^L then eraseMask L a m
    else if a = L then m-2^L
    else 2^L + eraseMask L a (m-2^L)
end ThreeSum.MaskErase


