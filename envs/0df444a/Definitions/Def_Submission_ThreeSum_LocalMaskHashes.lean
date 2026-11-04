-- Prove2me | Definitions.Def_Submission_ThreeSum_LocalMaskHashes
-- name    : Submission_ThreeSum_LocalMaskHashes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:43.497471+00:00
-- url     : https://prove2.me/theorems/a9471035-65b2-4899-b1e7-0543217f92ff
-- title:
--   Local Mask Hashes
-- statement:
--   Definitions and structural lemmas for Local Mask Hashes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskHashes.lean

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
set_option autoImplicit false
namespace ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}
def coeff (b : Bool) (w : Weight L (LocalField h)) : ℕ → ℕ :=
  OneHotMask.extend (fun i => (w (i,b)).val)
def leftCode (w : Weight L (LocalField h)) (k i : ℕ) : ℕ :=
  LightHashHistogram.code L (localPrime h) (maskAt L k) (coeff false w) (coeff true w) i
def rightCode (w : Weight L (LocalField h)) (k i : ℕ) : ℕ :=
  LightHashHistogram.code L (localPrime h) (maskAt L k) (coeff true w) (coeff false w) i
end ThreeSum.LocalMaskHashes


