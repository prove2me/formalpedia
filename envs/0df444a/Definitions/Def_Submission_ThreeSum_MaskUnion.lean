-- Prove2me | Definitions.Def_Submission_ThreeSum_MaskUnion
-- name    : Submission_ThreeSum_MaskUnion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:51.775121+00:00
-- url     : https://prove2.me/theorems/e492b16f-9963-4adf-ab79-b9a59c13225b
-- title:
--   Mask Union
-- statement:
--   Definitions and structural lemmas for Mask Union, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
set_option autoImplicit false
namespace ThreeSum.MaskUnion
open Finset ThreeSum.SubsetAddress
def scanSet {W : ℕ} (A B : Finset (Fin W)) (j : ℕ) : Finset (Fin W) :=
  A ∪ (B ∩ BoxStages.initialCoords W j)
end ThreeSum.MaskUnion


