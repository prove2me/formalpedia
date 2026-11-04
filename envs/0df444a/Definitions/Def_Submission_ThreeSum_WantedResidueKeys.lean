-- Prove2me | Definitions.Def_Submission_ThreeSum_WantedResidueKeys
-- name    : Submission_ThreeSum_WantedResidueKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:59:39.019937+00:00
-- url     : https://prove2.me/theorems/054ec8dd-ec4d-465c-b257-63634ac8186e
-- title:
--   Wanted Residue Keys
-- statement:
--   Definitions and structural lemmas for Wanted Residue Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
set_option autoImplicit false
namespace ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators
def code (M : ℕ) (shift x : ℤ) : ℕ := LightSourceResidues.key M M shift x
def total (M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : ℕ :=
  WantedPairs.count (fun i => code M shift (left i)) (fun j => code M 0 (right j)) NR NL
end ThreeSum.WantedResidueKeys


