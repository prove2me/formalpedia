-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
-- name    : Submission_ThreeSum_ReportingHostQueryBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:28:59.69882+00:00
-- url     : https://prove2.me/theorems/d39d1ac3-f5dc-454a-9bdb-30154044005b
-- title:
--   Reporting Host Query Bounds
-- statement:
--   Definitions and structural lemmas for Reporting Host Query Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostQueryBounds.lean

import Definitions.Def_Submission_ThreeSum_LightBlockQuery
set_option autoImplicit false
namespace ThreeSum.ReportingHostQueryBounds
open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators
def value {W : ℕ} (f g : Finset (Fin W) → ℤ) (stage : ℕ)
    (preL preR Q : Finset (Fin W)) : ℤ :=
  Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
    SubsetStages.stageValue g stage (preR ∪ S)) Q
end ThreeSum.ReportingHostQueryBounds


