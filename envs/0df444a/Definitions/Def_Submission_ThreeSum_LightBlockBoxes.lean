-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockBoxes
-- name    : Submission_ThreeSum_LightBlockBoxes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:28:59.254201+00:00
-- url     : https://prove2.me/theorems/ce5cd3a0-78f4-40d2-9afe-51329224ec4b
-- title:
--   Light Block Boxes
-- statement:
--   Definitions and structural lemmas for Light Block Boxes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockBoxes.lean

import Definitions.Def_Submission_ThreeSum_LightBlockQuery
set_option autoImplicit false
namespace ThreeSum.LightBlockBoxes
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery
variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
def leafWeight {h J : ℕ} (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512*h)))) : Finset (Fin (width h J)) → ℤ :=
  SignedLeaf.value (leftSource pMod B b q) (rightSource pMod shift C c q)
    (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
end ThreeSum.LightBlockBoxes


