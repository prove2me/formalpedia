-- Prove2me | Definitions.Def_Submission_ThreeSum_SignedLeaf
-- name    : Submission_ThreeSum_SignedLeaf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:23.18432+00:00
-- url     : https://prove2.me/theorems/52fc3fd6-4418-4f07-a5e0-0bb776aaf0b4
-- title:
--   Signed Leaf
-- statement:
--   Definitions and structural lemmas for Signed Leaf, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
set_option autoImplicit false
namespace ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
def value {W : ℕ} (f g : Finset (Fin W) → ℤ) (stage : ℕ)
    (preL preR S : Finset (Fin W)) : ℤ :=
  (-1 : ℤ)^S.card *
    (SubsetStages.stageValue f stage (preL ∪ S)*SubsetStages.stageValue g stage (preR ∪ S))
def explicitMissing {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) : List (Finset (Fin W)) :=
  (List.range t).flatMap (QueryCoordinates.missingSets Q)
def explicitLeaves {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) : List (Finset (Fin W)) :=
  (explicitMissing Q t).map fun U => Q \ U
end ThreeSum.SignedLeaf


