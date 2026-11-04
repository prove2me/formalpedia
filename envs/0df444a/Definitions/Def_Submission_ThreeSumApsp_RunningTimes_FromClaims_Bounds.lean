-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
-- name    : Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:14:05.04927+00:00
-- url     : https://prove2.me/theorems/22a05598-3d83-41d7-871d-75e789c9b68a
-- title:
--   Bounds
-- statement:
--   Definitions and structural lemmas for Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
set_option autoImplicit false
section
@[expose] section
namespace ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
end ThreeSumApsp.FromClaims


