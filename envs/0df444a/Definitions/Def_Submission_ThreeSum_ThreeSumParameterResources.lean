-- Prove2me | Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
-- name    : Submission_ThreeSum_ThreeSumParameterResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:52:50.16691+00:00
-- url     : https://prove2.me/theorems/dd1834ad-fed5-4763-913e-1d11944495d2
-- title:
--   Three Sum Parameter Resources
-- statement:
--   Definitions and structural lemmas for Three Sum Parameter Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumParameterResources.lean

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
set_option autoImplicit false
namespace ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
def work (dst : ℕ) : ℕ :=
  dst + 19
def cells (n : ℕ) : ℕ :=
  19 + LightParameterInit.space 0 n
def depth (n : ℕ) : ℕ :=
  512 * LightParameterInit.half n + 6
def envelope (n : ℕ) : ℕ :=
  20000 * scale n
def need (n _U : ℕ) : Light.Need :=
  ⟨LightParameterInit.word n, cells n, depth n⟩
noncomputable section
end
end ThreeSum.ThreeSumParameterResources


