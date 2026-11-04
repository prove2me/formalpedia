-- Prove2me | Definitions.Def_Submission_ThreeSum_MaskDecode
-- name    : Submission_ThreeSum_MaskDecode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:33.859476+00:00
-- url     : https://prove2.me/theorems/c0681ba5-7da5-40d9-8bdb-20fd48153785
-- title:
--   Mask Decode
-- statement:
--   Definitions and structural lemmas for Mask Decode, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskDecode.lean

import Definitions.Def_Submission_ThreeSum_SubsetAddress
set_option autoImplicit false
namespace ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
def decode (L m : ℕ) : Finset (Fin L) := univ.filter fun i => i.val ∈ m.bitIndices
end ThreeSum.MaskDecode


