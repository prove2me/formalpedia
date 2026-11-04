-- Prove2me | Definitions.Def_Submission_ThreeSum_QueryCoordinates
-- name    : Submission_ThreeSum_QueryCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:44:36.536269+00:00
-- url     : https://prove2.me/theorems/4c505a27-1a5a-402b-9f59-23122d3b0fdc
-- title:
--   Query Coordinates
-- statement:
--   Definitions and structural lemmas for Query Coordinates, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean

import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
namespace ThreeSum.QueryCoordinates
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
def positions {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) : List ℕ :=
  (List.range j).filter fun i => i ∈ natPositions Q
def selectedPowers {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) : List ℕ :=
  (positions Q j).map fun i => 2^i
def weights {W : ℕ} (Q : Finset (Fin W)) (i : ℕ) : ℕ :=
  (selectedPowers Q W)[i]?.getD 0
def setLayer (xs : List ℕ) (k : ℕ) : List (Finset ℕ) :=
  (xs.sublistsLen k).map List.toFinset
def missingSets {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) : List (Finset (Fin W)) :=
  (setLayer (positions Q W).reverse k).map fun s => MaskDecode.decode W (maskOf s)
end ThreeSum.QueryCoordinates


