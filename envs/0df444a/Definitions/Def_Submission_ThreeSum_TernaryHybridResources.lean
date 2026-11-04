-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryHybridResources
-- name    : Submission_ThreeSum_TernaryHybridResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:57:33.023126+00:00
-- url     : https://prove2.me/theorems/6bbcc254-5482-4e38-85f9-289cb398af9d
-- title:
--   Ternary Hybrid Resources
-- statement:
--   Definitions and structural lemmas for Ternary Hybrid Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridResources.lean

import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_Submission_ThreeSum_LightNatPower
set_option autoImplicit false
namespace ThreeSum.TernaryHybridResources
open Light StageBounds ArithmeticStageBounds
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
def controls (κ cutoff n : ℕ) : ℕ := n+κ+cutoff+(n+1)^(κ+1)+10
variable (fastNeed : ℕ → ℕ → Light.Need)
def need (fastNeed : ℕ → ℕ → Light.Need) (κ cutoff n U : ℕ) : Light.Need :=
  ⟨(fastNeed n (n^κ)).word+(LightBruteThreeSum.need n U).word+controls κ cutoff n,
    max (fastNeed n (n^κ)).cells (LightBruteThreeSum.need n U).cells,
    max (fastNeed n (n^κ)).depth (LightBruteThreeSum.need n U).depth+3⟩
def poweredFastNeed (fastNeed : ℕ → ℕ → Light.Need) (κ n _U : ℕ) : Light.Need := fastNeed n (n^κ)
noncomputable section
end
end ThreeSum.TernaryHybridResources


