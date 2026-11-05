-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:44:08.227976+00:00
-- url     : https://prove2.me/theorems/8c881868-e34a-438c-b4b8-4caab2aae088
-- title:
--   TernaryCanonicalNativeCompleteness
-- statement:
--   Definitions and structural lemmas for TernaryCanonicalNativeCompleteness, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCanonicalNativeCompleteness.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


