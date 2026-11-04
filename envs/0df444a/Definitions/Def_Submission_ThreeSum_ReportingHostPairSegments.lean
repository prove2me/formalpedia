-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
-- name    : Submission_ThreeSum_ReportingHostPairSegments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:46:55.510122+00:00
-- url     : https://prove2.me/theorems/b6a4b160-f763-4ed2-91f9-3a4b864f8d96
-- title:
--   Reporting Host Pair Segments
-- statement:
--   Definitions and structural lemmas for Reporting Host Pair Segments, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairSegments.lean

import Definitions.Def_Submission_ThreeSum_LightReportingPairRows
set_option autoImplicit false
namespace ThreeSum.ReportingHostPairSegments
open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration
set_option linter.unusedSimpArgs false
variable {α β : Type*}
def leftMasks (L h : ℕ) : List ℤ := (pairs L h).map fun p => (subsetMask p.1 : ℤ)
def rightMasks (L h : ℕ) : List ℤ := (pairs L h).map fun p => (subsetMask p.2 : ℤ)
end ThreeSum.ReportingHostPairSegments


