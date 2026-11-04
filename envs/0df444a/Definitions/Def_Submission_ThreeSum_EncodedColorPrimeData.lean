-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
-- name    : Submission_ThreeSum_EncodedColorPrimeData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:41:24.486204+00:00
-- url     : https://prove2.me/theorems/907ad8bc-c154-4666-bf85-524f9f058a31
-- title:
--   Encoded Color Prime Data
-- statement:
--   Definitions and structural lemmas for Encoded Color Prime Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeData.lean

import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
set_option autoImplicit false
namespace ThreeSum.EncodedColorPrimeData
open Light
def poolBase (free : ℕ) : ℕ := free+6
def prefixBase (free y : ℕ) : ℕ := poolBase free+3*y
def nextFree (free M y : ℕ) : ℕ := prefixBase free y+LightBandPrimeDepth.depth M y+1
def values (free M y p : ℕ) : List ℤ :=
  [p,LightBandPrimeDepth.depth M y,nextFree free M y,poolBase free,LightPrimePool.size y,prefixBase free y]
structure Stored (μ : ℕ → ℤ) (free M y : ℕ) (qs : ℕ → ℕ) : Prop where
  header : Seg μ free (values free M y (qs (LightBandPrimeDepth.depth M y)))
  pool : SegN μ (poolBase free) (LightPrimePool.values y)
  prefixes : ∀ i ≤ LightBandPrimeDepth.depth M y, μ (prefixBase free y+i)=(qs i : ℤ)
end ThreeSum.EncodedColorPrimeData


