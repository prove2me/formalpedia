-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
-- name    : Submission_Weighted_Global_TernaryCoverGoodMaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:16:22.261679+00:00
-- url     : https://prove2.me/theorems/159a3218-819c-49c0-a4de-d903738f11c8
-- title:
--   Ternary Cover Good Maps
-- statement:
--   Definitions and structural lemmas for Ternary Cover Good Maps, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverGoodMaps.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalLocalParameters WeightedGlobalCoverActualMoment TernaryCoverMoments
open scoped BigOperators
abbrev Weight (m p : ℕ) := Coordinate (Fin (fixedLength m)) → ZMod p
abbrev ActualEdge (m : ℕ) := LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)
variable (m p : ℕ) [Fact p.Prime]
def rawBadMaps (τ : ℕ) : Finset (Weight m p) :=
  badMaps (fun w (t : ZMod p × ZMod p) => TernaryCoverFibers.rawPairCount
    (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) t.1 t.2) τ
def prunedHit (B τ : ℕ) (w : Weight m p) (a b : ZMod p) : ℕ := by
  classical
  exact if w ∈ rawBadMaps m p τ then 0 else hitCount (fixedAlpha m) (fixedPi m) B w a b
end ThreeSum.WeightedGlobalCoverGoodMaps


