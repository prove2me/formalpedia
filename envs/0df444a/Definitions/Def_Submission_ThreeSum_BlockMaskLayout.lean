-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockMaskLayout
-- name    : Submission_ThreeSum_BlockMaskLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:44.868673+00:00
-- url     : https://prove2.me/theorems/ee876dfd-0138-4893-a8ea-a3d1e16a814d
-- title:
--   Block Mask Layout
-- statement:
--   Definitions and structural lemmas for Block Mask Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockMaskLayout.lean

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_MaskDifference
set_option autoImplicit false
namespace ThreeSum.BlockMaskLayout
open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators
def rowMask {J L : ℕ} (rows : Fin J → Finset (Fin L)) (i : Fin J) : ℕ :=
  2^(i.val*L)*subsetMask (rows i)
def prefixMask {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) : ℕ :=
  subsetMask (indexSet (join (prefixIndices J k) rows))
def rawMasks {J L : ℕ} (rows : Fin J → Finset (Fin L)) : List ℕ :=
  List.ofFn (fun i => subsetMask (rows i))
def packedMasks {J L : ℕ} (rows : Fin J → Finset (Fin L)) : List ℕ := List.ofFn (rowMask rows)
end ThreeSum.BlockMaskLayout


