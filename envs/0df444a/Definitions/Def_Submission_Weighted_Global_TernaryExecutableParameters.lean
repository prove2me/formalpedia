-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
-- name    : Submission_Weighted_Global_TernaryExecutableParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:52:56.775194+00:00
-- url     : https://prove2.me/theorems/29354687-071b-4460-b761-c02dc0f5f944
-- title:
--   Ternary Executable Parameters
-- statement:
--   Definitions and structural lemmas for Ternary Executable Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutableParameters.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryExecutable
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Theorems.Thm_ThreeSum_SparseBoxes_mem_records
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalNativeCoverWitness_local_record_witness
import Theorems.Thm_ThreeSum_WeightedGlobalNativeCoverWitness_nativeMaps_cover
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records


set_option autoImplicit false
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


