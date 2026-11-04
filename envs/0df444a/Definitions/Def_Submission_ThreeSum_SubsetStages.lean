-- Prove2me | Definitions.Def_Submission_ThreeSum_SubsetStages
-- name    : Submission_ThreeSum_SubsetStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:50:47.048776+00:00
-- url     : https://prove2.me/theorems/5fc10d0a-ec43-4b73-8609-bd75b81d79c3
-- title:
--   Subset Stages
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
set_option autoImplicit false
namespace ThreeSum.SubsetStages
open Finset
def suffix (L j : ℕ) : Finset (Fin L) := univ.filter fun a => L-j ≤ a.val
def nextCoord {L : ℕ} (j : ℕ) (hj : j < L) : Fin L := ⟨L-1-j,by omega⟩
def stageValue {L : ℕ} (f : Finset (Fin L) → ℤ) (j : ℕ) : Finset (Fin L) → ℤ :=
  Subset.partialZeta (suffix L j) f
end ThreeSum.SubsetStages


