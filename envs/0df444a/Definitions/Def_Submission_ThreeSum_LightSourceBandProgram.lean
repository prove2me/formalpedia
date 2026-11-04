-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandProgram
-- name    : Submission_ThreeSum_LightSourceBandProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:01:12.927126+00:00
-- url     : https://prove2.me/theorems/a4637ed8-bfd5-4063-9cee-c914d63d267f
-- title:
--   Light Source Band Program
-- statement:
--   Definitions and structural lemmas for Light Source Band Program, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandProgram.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
set_option autoImplicit false
namespace ThreeSum.LightSourceBandProgram
open Light
def program : Program :=
  LightSourceBucketOriginal.program ++
    [LightSourceBandStep.body 0,LightSourceBandBatch.body 9,
      LightSmallDivide.body,LightSourceBandSetup.body 11 10]
def originalProcs : LightSourceBucketOriginal.Procs program 0 :=
  ⟨1,6,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,⟨7,8,rfl,rfl,rfl⟩,rfl⟩
def programProcs : LightSourceBandSetup.Procs program 12 :=
  ⟨11,10,rfl,⟨9,⟨0,originalProcs,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightSourceBandProgram


