-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
-- name    : Submission_ThreeSum_SourceFiniteInputs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:13:09.566537+00:00
-- url     : https://prove2.me/theorems/586e8a6f-70a7-43fe-b24b-5c51f6b5efb4
-- title:
--   Source Finite Inputs
-- statement:
--   Definitions and structural lemmas for Source Finite Inputs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
set_option autoImplicit false
namespace ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule
def maps (free h : ℕ) : ℕ := scheduleMaps (LightLocalCoverInit.base free) h
def candidates (free h : ℕ) : ℕ := LightLocalCoverLayout.candidates (LightLocalCoverInit.base free) h
def leftCounts (free h : ℕ) : ℕ := hist0 (LightLocalCoverInit.base free) h
def rightCounts (free h : ℕ) : ℕ := hist1 (LightLocalCoverInit.base free) h
end ThreeSum.SourceFiniteInputs


