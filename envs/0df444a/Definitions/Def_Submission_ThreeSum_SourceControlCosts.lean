-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceControlCosts
-- name    : Submission_ThreeSum_SourceControlCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:47:16.246261+00:00
-- url     : https://prove2.me/theorems/604234b7-84ec-4b98-b2cf-50a5325a8d1b
-- title:
--   Source Control Costs
-- statement:
--   Definitions and structural lemmas for Source Control Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
set_option autoImplicit false
namespace ThreeSum.SourceControlCosts
open Scales TrimScales StageBounds CostLedger BandScales
def factor (h J : ℕ) : ℕ :=
  1400*(J*(512*h)+1)^2+20*J+
    14*Nat.log 2 ((512*h)*LocalCoverBounds.localPrime h+1)+
    14*Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+2044
end ThreeSum.SourceControlCosts


