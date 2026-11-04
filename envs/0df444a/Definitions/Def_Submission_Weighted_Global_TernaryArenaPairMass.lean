-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
-- name    : Submission_Weighted_Global_TernaryArenaPairMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:50:50.725871+00:00
-- url     : https://prove2.me/theorems/028c9765-aae8-471d-b0c6-c32012f77769
-- title:
--   Ternary Arena Pair Mass
-- statement:
--   Definitions and structural lemmas for Ternary Arena Pair Mass, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairMass.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPairMass
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeMomentBounds
open WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters StageBounds
variable {p m F r : ℕ} [Fact p.Prime]
def tableWidth (maps : Fin F→Weight m p) (cap : ℕ) : ℕ :=
  max (localRecords maps cap false).length (localRecords maps cap true).length
def base (maps : Fin F→Weight m p) (cap : ℕ) : ℕ :=
  (tableWidth maps cap+1)^2*2^(fixedLength m)
def envelope (maps : Fin F→Weight m p) (cap M n : ℕ) : ℕ :=
  M^(base maps cap)*(n+1)^(2*base maps cap+2)
end ThreeSum.WeightedGlobalArenaPairMass


