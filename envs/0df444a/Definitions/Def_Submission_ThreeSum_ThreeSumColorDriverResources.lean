-- Prove2me | Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
-- name    : Submission_ThreeSum_ThreeSumColorDriverResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:57:55.089338+00:00
-- url     : https://prove2.me/theorems/1895c4d6-1a9d-473a-93c7-f152940c7d25
-- title:
--   Three Sum Color Driver Resources
-- statement:
--   Definitions and structural lemmas for Three Sum Color Driver Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean

import Definitions.Def_Submission_ThreeSum_LightThreeSumColorDriver
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
set_option autoImplicit false
namespace ThreeSum.ThreeSumColorDriverResources
open Light Scales StageBounds ArithmeticStageBounds LightColorParametersCosts ColorParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000
def overhead (n _U : ℕ) : Need :=
  ⟨LightColorScanHost.word n,6,count (width n)+4⟩
def need (colorNeed : ℕ→ℕ→Need) (n U : ℕ) : Need :=
  ⟨(colorNeed n U).word+(overhead n U).word,
    (colorNeed n U).cells+(overhead n U).cells,
    (colorNeed n U).depth+(overhead n U).depth⟩
def fullNeed (colorNeed : ℕ→ℕ→Need) (n U : ℕ) : Need :=
  ⟨(ThreeSumParameterResources.need n U).word+(need colorNeed n U).word,
    max (ThreeSumParameterResources.need n U).cells (19+(need colorNeed n U).cells),
    (ThreeSumParameterResources.need n U).depth+(need colorNeed n U).depth+2⟩
def overheadEnvelope (n : ℕ) : ℕ := 200*(n+1)^2
noncomputable section
end
end ThreeSum.ThreeSumColorDriverResources


