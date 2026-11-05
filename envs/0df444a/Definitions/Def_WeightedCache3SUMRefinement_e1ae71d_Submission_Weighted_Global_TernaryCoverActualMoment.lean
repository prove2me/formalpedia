-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverActualMoment
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverActualMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:09:54.360684+00:00
-- url     : https://prove2.me/theorems/c5973902-c938-4879-9a91-e0c3d08e05c5
-- title:
--   TernaryCoverActualMoment
-- statement:
--   Definitions and structural lemmas for TernaryCoverActualMoment, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverActualMoment.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers WeightedGlobalLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
def taggedLeft {L : ℕ} {α π : DigitType} (e : LocalEdge L α π) : Coordinate (Fin L) → Fin 3 :=
  Sum.elim (left e) (fun b => if b then 0 else 1)
def taggedRight {L : ℕ} {α π : DigitType} (e : LocalEdge L α π) : Coordinate (Fin L) → Fin 3 :=
  Sum.elim (right e) (fun b => if b then 1 else 0)
end ThreeSum.WeightedGlobalCoverActualMoment
end
end WeightedCache3SUMRefinement_e1ae71d


