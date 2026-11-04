-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceControlsProgram
-- name    : Submission_ThreeSum_LightSourceControlsProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:35:48.268195+00:00
-- url     : https://prove2.me/theorems/2c1c7192-8b12-4a5f-b1f8-864745126df8
-- title:
--   Light Source Controls Program
-- statement:
--   Definitions and structural lemmas for Light Source Controls Program, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceControlsProgram.lean

import Definitions.Def_Submission_ThreeSum_LightSourceControls
set_option autoImplicit false
namespace ThreeSum.LightSourceControlsProgram
open Light
def program : Program := LightDownsetSize.program ++
  [LightNatPower.body,log2Body,LightSourceControlsMax.body,
    LightSourceControlsSpan.body 11,LightSourceControls.body 9 0 10 12]
def programProcs : LightSourceControls.Procs program 13 :=
  ⟨9,0,10,12,11,1,2,3,4,5,6,7,8,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightSourceControlsProgram


