-- Prove2me | Definitions.Def_Submission_ThreeSum_BoxStages
-- name    : Submission_ThreeSum_BoxStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:35.896658+00:00
-- url     : https://prove2.me/theorems/af35a8f8-f9d6-4689-8021-f58fde811021
-- title:
--   Box Stages
-- statement:
--   Definitions and structural lemmas for Box Stages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
set_option autoImplicit false
namespace ThreeSum.BoxStages
open Finset
def initialCoords (L j : ℕ) : Finset (Fin L) := univ.filter fun a => a.val < j
def nextCoord {L : ℕ} (j : ℕ) (hj : j < L) : Fin L := ⟨j,hj⟩
def stageValue {L : ℕ} (f : Finset (Fin L) → ℤ) (j : ℕ) : Finset (Fin L) → ℤ :=
  Subset.partialZeta (initialCoords L j) f
end ThreeSum.BoxStages


