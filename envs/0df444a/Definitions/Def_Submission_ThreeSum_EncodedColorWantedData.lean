-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
-- name    : Submission_ThreeSum_EncodedColorWantedData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:20:42.494577+00:00
-- url     : https://prove2.me/theorems/12ad5143-0d38-48f2-8bba-3cc4317cfee5
-- title:
--   Encoded Color Wanted Data
-- statement:
--   Definitions and structural lemmas for Encoded Color Wanted Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedData.lean

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
set_option autoImplicit false
namespace ThreeSum.EncodedColorWantedData
open Light WantedResidueKeys
def nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : ℕ :=
  LightWantedSetup.pairBase out NL NR M+2*total M left right NL NR shift
end ThreeSum.EncodedColorWantedData


