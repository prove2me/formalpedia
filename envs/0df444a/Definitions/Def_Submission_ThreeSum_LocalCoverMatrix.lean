-- Prove2me | Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
-- name    : Submission_ThreeSum_LocalCoverMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:38.978149+00:00
-- url     : https://prove2.me/theorems/5ed89754-3477-4f0e-bd41-dc6bc6136eb5
-- title:
--   Local Cover Matrix
-- statement:
--   Definitions and structural lemmas for Local Cover Matrix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
set_option autoImplicit false
namespace ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}
def bits (L k i : ℕ) : ℕ → ℕ := LightMaskBits.bit L (maskAt L k i)
def leftCount (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  fun r => LightHistogram.count (leftCode w k) r (LocalMaskGraph.vertexCount L k)
def rightCount (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  fun r => LightHistogram.count (rightCode w k) r (LocalMaskGraph.vertexCount L k)
def key (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  LightPairFlags.pairKey (LocalMaskGraph.vertexCount L k) (localPrime h)
    (leftCode w k) (rightCode w k)
def valid (w : Weight L (LocalField h)) (k B : ℕ) : ℕ → ℕ :=
  LightPairFlags.pairFlag L (LocalMaskGraph.vertexCount L k) B (bits L k)
    (leftCode w k) (rightCode w k) (leftCount w k) (rightCount w k)
def entry (w : Weight L (LocalField h)) (k B r : ℕ) : ℕ :=
  LightSupportMark.bit (key w k) (valid w k B) r
    (LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k)
end ThreeSum.LocalCoverMatrix


