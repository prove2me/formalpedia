-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutableParameters
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutableParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:53:58.240828+00:00
-- url     : https://prove2.me/theorems/f53930f2-1184-4072-be07-1926b1227e75
-- title:
--   TernaryExecutableParameters
-- statement:
--   Definitions and structural lemmas for TernaryExecutableParameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryExecutableParameters.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Theorems.Thm_ThreeSum_SparseBoxes_mem_records
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeCoverWitness_local_record_witness
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeCoverWitness_nativeMaps_cover
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalExecutableParameters
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverGoodMaps
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters WeightedGlobalNativeCoverWitness WeightedGlobalCoverScale
set_option maxHeartbeats 2000000
def F (K m k : ℕ) :=(nativeFamily K m k).length
def maps (K m k : ℕ) : Fin (F K m k)→Weight m (nativePrime K m) :=nativeMaps K m k
def cap (K m : ℕ) :=sourceCap m (nativePrime K m)
def threshold (K m k : ℕ) :=rawThreshold (nativePrime K m) (cap K m) k
theorem cover {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k)
    (a b : ZMod (nativePrime K m)) :
    ∃i, WeightedGlobalCoverFrequency.Covers m (nativePrime K m) (cap K m)
      (threshold K m k) (maps K m k i) (a,b) :=nativeMaps_cover hK hm hk a b
theorem exists_output {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k) :
    ∃ Q : WeightedGlobalGoodOutputCatalog.Output m,
      0<(WeightedGlobalGoodOutputCatalog.records (maps K m k) (threshold K m k)).length := by
  obtain ⟨i,e,hgood,_,_,_,_,_⟩ := local_record_witness (maps K m k) (cap K m)
    (threshold K m k) (cover hK hm hk) 0 0
  let Q : WeightedGlobalGoodOutputCatalog.Output m :=⟨TernaryCoverLocal.output e,
    WeightedGlobalNativeTupleWitness.output_mem_vertices e⟩
  refine ⟨Q,?_⟩
  have hmem : (i,Q)∈WeightedGlobalGoodOutputCatalog.records (maps K m k) (threshold K m k) :=
    (WeightedGlobalGoodOutputCatalog.mem_records _ _ _).mpr hgood
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
def output {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k) : WeightedGlobalGoodOutputCatalog.Output m :=
  Classical.choose (exists_output hK hm hk)
end ThreeSum.WeightedGlobalExecutableParameters
end
end WeightedCache3SUMRefinement_e1ae71d


