-- Prove2me | Definitions.Def_Submission_ThreeSum_LightCoverKeyData
-- name    : Submission_ThreeSum_LightCoverKeyData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:28:59.214007+00:00
-- url     : https://prove2.me/theorems/677b4828-c295-42b1-b596-7de9cc1d6d06
-- title:
--   Light Cover Key Data
-- statement:
--   Definitions and structural lemmas for Light Cover Key Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
set_option autoImplicit false
namespace ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
def keyEnd (free h J : ℕ) : ℕ :=
  LightCoverKeys.keyHeader free h J+1+LightGlobalKeys.localCount h^J
structure Stored (μ : ℕ → ℤ) (free h J : ℕ) : Prop where
  count : μ (LightCoverKeys.keyHeader free h J)=((LightGlobalKeys.localCount h^J : ℕ) : ℤ)
  keys : Seg μ (LightCoverKeys.keyHeader free h J+1) (globalKeys h J)
  header : Seg μ free (LightLocalCoverInit.values free h)
  data : Data μ h (maps (LightLocalCoverInit.base free) h)
    (hist0 (LightLocalCoverInit.base free) h) (hist1 (LightLocalCoverInit.base free) h)
    (matrixPtr (LightLocalCoverInit.base free) h)
  rows : ScheduleRows μ h (scheduleMaps (LightLocalCoverInit.base free) h)
  indices : ∀ s : Occurrence h, μ (candidates (LightLocalCoverInit.base free) h+s.val)=
    (candidateAt h s : ℤ)
  masks : ∀ i < outputCount (512*h) h, μ (LightCoverKeys.afterCover free h+i)=
    (LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)
end ThreeSum.LightCoverKeyData


