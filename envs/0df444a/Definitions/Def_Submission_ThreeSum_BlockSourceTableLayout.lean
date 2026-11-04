-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
-- name    : Submission_ThreeSum_BlockSourceTableLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:36:13.512088+00:00
-- url     : https://prove2.me/theorems/d961a50f-24ee-40a8-bb50-001d9aa9ce68
-- title:
--   Block Source Table Layout
-- statement:
--   Definitions and structural lemmas for Block Source Table Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceTableLayout.lean

import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
set_option autoImplicit false
namespace ThreeSum.BlockSourceTableLayout
open SubsetAddress BlockIndex BlockEncoding BlockRows GlobalEncoding
def sets (h J cut i : ℕ) : Finset (Coord J (512*h)) :=
  unindexSet (SourceTableLayout.setAt (J*(512*h)) cut i)
end ThreeSum.BlockSourceTableLayout


