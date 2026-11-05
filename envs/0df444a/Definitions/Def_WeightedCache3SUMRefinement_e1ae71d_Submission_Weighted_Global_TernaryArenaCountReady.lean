-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCountReady
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCountReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:17:25.317205+00:00
-- url     : https://prove2.me/theorems/a13e2b7c-9f99-4989-ae33-3c485ef60d80
-- title:
--   TernaryArenaCountReady
-- statement:
--   Definitions and structural lemmas for TernaryArenaCountReady, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCountReady.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceValues
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaCountReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalBank TernaryCodeSemantics LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
def queryTime (I : Input) (V : ℕ) : ℕ :=
  ((Finset.univ : Finset (TritWord (N m r))).filter
    (fun Q => HasType Q (fun d => r*fixedPi m d))).sup
    (fun Q => LightWeightedPreparedWanted.time
      (nearConfig (m := m) (r := r) I false V) (nearConfig (m := m) (r := r) I true V) Q)
structure Capacity {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) : Prop where
  endSpace : finish I.free I.capacity≤lim.space
  prefixBank : I.prefixFree+nb m r≤addr I.free I.capacity 48
  bankValues : F^r*nb m r≤I.capacity
  stages : F^r*((N m r+1)*nb m r)≤I.capacity
  records : 3*(entries (r := r) maps τ I).length≤I.capacity
  metadata : 4*nb m r≤I.capacity
  powers : 2*N m r+1≤I.capacity
  nearRows : 3^(N m r)≤I.capacity
  nearMetadata : 2*N m r*3^(N m r)+N m r≤I.capacity
  division : WeightedGlobalFrontendResources.eulerBound (N m r) (valueCap (r := r) maps cap I)+3≤I.capacity
  word : (WeightedGlobalFrontendResources.word (N m r) (nb m r) (F^r)
    (entries (r := r) maps τ I).length (3^(N m r)) (valueCap (r := r) maps cap I) : ℤ)≤lim.word
  depth : d+5*N m r+16≤lim.depth
  time : queryTime (m := m) (r := r) I (valueCap (r := r) maps cap I)≤I.queryTime
end ThreeSum.WeightedGlobalArenaCountReady
end
end WeightedCache3SUMRefinement_e1ae71d


