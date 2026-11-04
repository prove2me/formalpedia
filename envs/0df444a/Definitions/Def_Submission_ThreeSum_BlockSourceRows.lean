-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockSourceRows
-- name    : Submission_ThreeSum_BlockSourceRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:36:18.268119+00:00
-- url     : https://prove2.me/theorems/741278b1-4eff-4d22-ad0a-b6ffd168ccc6
-- title:
--   Block Source Rows
-- statement:
--   Definitions and structural lemmas for Block Source Rows, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceRows.lean

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
namespace ThreeSum.BlockSourceRows
open Finset BlockRows BlockIndex LightSourceRowScan
open LocalHashMoments
open scoped BigOperators
set_option maxHeartbeats 1000000
def bits {J L : ℕ} (S : Finset (Coord J L)) (j : Fin J) (i : ℕ) : ℕ :=
  LightMaskBits.bit (J*L) (SubsetAddress.subsetMask (indexSet S)) (j.val*L+i)
end ThreeSum.BlockSourceRows


