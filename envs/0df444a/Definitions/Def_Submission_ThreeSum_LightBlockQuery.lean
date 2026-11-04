-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockQuery
-- name    : Submission_ThreeSum_LightBlockQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:26:21.677876+00:00
-- url     : https://prove2.me/theorems/eb53cad6-abd3-4e7c-887f-40346582c139
-- title:
--   Light Block Query
-- statement:
--   Definitions and structural lemmas for Light Block Query, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockQuery.lean

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSparseQuery
import Definitions.Def_Submission_ThreeSum_LightSignedBoxSetup
set_option autoImplicit false
namespace ThreeSum.LightBlockQuery
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
variable {lim : Limits} {P : Program}
abbrev width (h J : ℕ) : ℕ := J*(512*h)
abbrev sourceCut (h J : ℕ) : ℕ := 2*h*J
abbrev residualSize (h J k : ℕ) : ℕ := (J-k)*(2*h)
section OriginalIndices
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
end OriginalIndices
end ThreeSum.LightBlockQuery


