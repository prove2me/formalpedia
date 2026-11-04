-- Prove2me | Definitions.Def_Submission_ThreeSum_ExplicitLayers
-- name    : Submission_ThreeSum_ExplicitLayers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:38.381188+00:00
-- url     : https://prove2.me/theorems/5564c985-b35d-471d-a538-1d7e6a35c2bb
-- title:
--   Explicit Layers
-- statement:
--   Definitions and structural lemmas for Explicit Layers, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
set_option autoImplicit false
namespace ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
def valueSum {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) : ℤ :=
  ((SignedLeaf.explicitLeaves Q t).map weight).sum
end ThreeSum.ExplicitLayers


