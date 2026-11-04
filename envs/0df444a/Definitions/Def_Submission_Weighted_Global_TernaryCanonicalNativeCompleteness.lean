-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
-- name    : Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:11:59.394908+00:00
-- url     : https://prove2.me/theorems/15ecb87c-b5ef-408f-b09a-9ad7a63c74e6
-- title:
--   Ternary Canonical Native Completeness
-- statement:
--   Definitions and structural lemmas for Ternary Canonical Native Completeness, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalNativeCompleteness.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalCanonicalNativeCompleteness
open Finset TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalCoverGoodMaps
open WeightedGlobalNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open TernaryCanonicalDictionaries LightTernarySourceHost WeightedGlobalRepeatedWords
set_option maxHeartbeats 4000000
variable {p m F r : ℕ} [Fact p.Prime]
def outputRecord (occ : Fin r→Fin F) (e : Fin r→ActualEdge m) (i : Fin r) :
    WeightedGlobalGoodOutputCatalog.Record m (Fin F) :=
  (occ i,⟨output (e i),WeightedGlobalNativeTupleWitness.output_mem_vertices (e i)⟩)
def bankId (occ : Fin r→Fin F) : ℕ :=
  Nat.ofDigits F (List.ofFn fun i => (Fintype.equivFin (Fin F) (occ i)).val)
end ThreeSum.WeightedGlobalCanonicalNativeCompleteness


