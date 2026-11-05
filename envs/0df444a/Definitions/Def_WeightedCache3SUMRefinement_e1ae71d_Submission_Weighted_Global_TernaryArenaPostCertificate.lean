-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostCertificate
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:34:10.977541+00:00
-- url     : https://prove2.me/theorems/63063922-9379-4f5c-9fb4-f1283e4f6894
-- title:
--   TernaryArenaPostCertificate
-- statement:
--   Definitions and structural lemmas for TernaryArenaPostCertificate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPostCertificate.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostResources
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_controls
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceControls_controls
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceLayout_geometry
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_controls
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPostCertificate
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps LightWeightedGlobalPostSelection
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]
structure Guards (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (lim : Limits)
    (d M n U Hdet nB nC : ℕ) : Prop where
  hM : 1<M
  hr : r≤Nat.clog M (n^2)
  hF : 1<F
  hN : 0<N m r
  hnB : nB≤n
  hnC : nC≤n
  hw : (lim.space : ℤ)≤lim.word
  hd : d+5<lim.depth
  hend : finish I.free I.capacity≤lim.space
  counts : nB+3*nC+1≤I.capacity
  Ccount : nC+1≤I.capacity
  bankLo : addr I.free I.capacity 11≤I.prefixFree
  bankHi : I.prefixFree+nb m r≤addr I.free I.capacity 16
  powersHi : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16
  records : 3*(entries (r := r) maps τ I).length≤I.capacity
  matrix : (2*Hdet+1)*(entries (r := r) maps τ I).length≤I.capacity
  terms : 2*Hdet+1≤I.capacity
  localPositive : ∀right,0<(WeightedGlobalNativeCompleteFrontend.localRecords maps cap right).length
  geometry : ∀right,WeightedGlobalArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space
  controls : ∀right,WeightedGlobalArenaSourceControls.Controls (r := r) maps cap I right lim (d+6)
  countCapacity : WeightedGlobalArenaCountReady.Capacity (lim := lim) (d := d+6) (r := r) maps τ cap I
  weight : WeightedGlobalMomentWeightBounds.leftBound U (2*Hdet)≤I.weightCap
  channel : ((WeightedGlobalArenaMomentResources.channelNeed maps cap M Hdet n U).word : ℤ)≤lim.word
  detector : ((WeightedGlobalArenaMomentResources.detectorNeed maps cap M Hdet n U).word : ℤ)≤lim.word
  args : ∀z∈LightWeightedGlobalMomentChannelFactory.args (setup (r := r) maps τ cap Q I)
    (addr I.free I.capacity 10) (addr I.free I.capacity 16+nB+1+2*nC)
    (addr I.free I.capacity 25), |z|≤lim.word
end ThreeSum.WeightedGlobalArenaPostCertificate
end
end WeightedCache3SUMRefinement_e1ae71d


