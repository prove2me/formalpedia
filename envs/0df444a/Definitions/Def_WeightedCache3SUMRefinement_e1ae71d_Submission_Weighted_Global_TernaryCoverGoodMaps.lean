-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverGoodMaps
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverGoodMaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:10:48.39185+00:00
-- url     : https://prove2.me/theorems/52f989bf-6706-4dfd-bc94-fe5a924f7972
-- title:
--   TernaryCoverGoodMaps
-- statement:
--   Definitions and structural lemmas for TernaryCoverGoodMaps, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverGoodMaps.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


