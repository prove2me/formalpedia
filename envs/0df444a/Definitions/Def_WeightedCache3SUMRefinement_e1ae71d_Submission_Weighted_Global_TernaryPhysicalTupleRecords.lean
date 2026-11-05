-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalTupleRecords
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalTupleRecords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:45:33.2277+00:00
-- url     : https://prove2.me/theorems/89f5d172-0efe-4845-80f0-77d3f34074ce
-- title:
--   TernaryPhysicalTupleRecords
-- statement:
--   Definitions and structural lemmas for TernaryPhysicalTupleRecords, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_mem
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalPhysicalTupleRecords
open WeightedGlobalTupleDictionaryDecode LightTernarySourceHost
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*}
def Record (base : List A) (r M n : ℕ) (input : ℕ→ℤ) (raw : A→ℤ) :=
  {x : Fin n×{xs // xs∈RadixKeyLists.tuples base r} //
    (M : ℤ)∣input x.1.val-Radix.positionalHash (M : ℤ) raw x.2.val}
def decodeRecord (base : List A) (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    Fin n×{xs // xs∈RadixKeyLists.tuples base r} :=
  (⟨x.val.1,((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).1⟩,
    ⟨decode base r ⟨x.val.2,((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.1⟩,
      decode_mem _ _ _⟩)
end ThreeSum.WeightedGlobalPhysicalTupleRecords
end
end WeightedCache3SUMRefinement_e1ae71d


