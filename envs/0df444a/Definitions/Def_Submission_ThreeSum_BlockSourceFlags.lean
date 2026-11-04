-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockSourceFlags
-- name    : Submission_ThreeSum_BlockSourceFlags
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:12.479681+00:00
-- url     : https://prove2.me/theorems/22e0e0e2-f106-482a-b2c3-e18bcd7de6c5
-- title:
--   Block Source Flags
-- statement:
--   Definitions and structural lemmas for Block Source Flags, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
set_option autoImplicit false
namespace ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000
def candidateIndices (h s : ℕ) : ℕ := (LightLocalCoverSchedule.indices h).getD s 0
def bits {J L : ℕ} (S : Finset (Coord J L)) : ℕ → ℕ :=
  LightMaskBits.bit (J*L) (SubsetAddress.subsetMask (indexSet S))
def leftCount (h k : ℕ) : ℕ → ℕ :=
  LocalCoverMatrix.leftCount (LightLocalCoverSchedule.candidate h k) h
def rightCount (h k : ℕ) : ℕ → ℕ :=
  LocalCoverMatrix.rightCount (LightLocalCoverSchedule.candidate h k) h
end ThreeSum.BlockSourceFlags


