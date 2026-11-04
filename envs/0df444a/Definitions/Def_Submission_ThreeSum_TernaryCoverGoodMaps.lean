-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
-- name    : Submission_ThreeSum_TernaryCoverGoodMaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:16:07.47502+00:00
-- url     : https://prove2.me/theorems/c1b1f613-24fc-4a8a-97ff-1a7d30d4a2b5
-- title:
--   Ternary Cover Good Maps
-- statement:
--   Definitions and structural lemmas for Ternary Cover Good Maps, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryLocalParameters TernaryCoverActualMoment TernaryCoverMoments
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
end ThreeSum.TernaryCoverGoodMaps


