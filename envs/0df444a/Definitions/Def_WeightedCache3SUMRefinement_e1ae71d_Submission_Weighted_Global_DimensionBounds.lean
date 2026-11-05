-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:01:26.059125+00:00
-- url     : https://prove2.me/theorems/e4dd4b90-6747-404b-a04c-d506698b699a
-- title:
--   DimensionBounds
-- statement:
--   Definitions and structural lemmas for DimensionBounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/DimensionBounds.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters
def bankCut (m j : ℕ) : ℕ := 8371360984307726883*j*m
def queryDeficit (m j : ℕ) : ℕ := 552323882206246677*j*m+2739
def bankSize (m j : ℕ) : ℕ := (bank (fixedLength (j*m)) (bankCut m j)).card
end ThreeSum.WeightedGlobalDimensionBounds
end
end WeightedCache3SUMRefinement_e1ae71d


