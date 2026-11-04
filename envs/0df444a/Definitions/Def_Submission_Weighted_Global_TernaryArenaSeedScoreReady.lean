-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
-- name    : Submission_Weighted_Global_TernaryArenaSeedScoreReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:10:50.603271+00:00
-- url     : https://prove2.me/theorems/9b6310e6-e78c-4f29-860b-8ad07adcdc59
-- title:
--   Ternary Arena Seed Score Ready
-- statement:
--   Definitions and structural lemmas for Ternary Arena Seed Score Ready, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedScoreReady.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorReady
import Theorems.Thm_ThreeSum_WeightedFrontendResources_controls
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceControls_controls
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceLayout_geometry
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_controls

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSeedScoreReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
structure TensorGuard {lim : Limits} {depth K U seed : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ) : Prop where
  family : 1<F
  dimension : 0<N m r
  wordSpace : (lim.space : ℤ)≤lim.word
  capacity : WeightedGlobalArenaCountReady.Capacity (lim := lim) (d := depth+4) (r := r)
    maps τ cap (sourceInput I A seed D)
  nB : I.nB≤I.capacity
  nC : I.nC≤I.capacity
  prefixEnd : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16
  headerBeforePrefix : addr I.free I.capacity 1+106≤I.prefixFree
  localNonempty : ∀right, 0<(localRecords maps cap right).length
  geometry : ∀right, WeightedGlobalArenaSourceLayout.Geometry
    (source (r := r) maps cap (sourceInput I A seed D) right) lim.space
  controls : ∀right, WeightedGlobalArenaSourceControls.Controls (r := r) maps cap
    (sourceInput I A seed D) right lim (depth+4)
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)
  header : ∀i<106, i≠104 → μ (addr I.free I.capacity 1+i)=
    (setup (r := r) maps τ cap Q (sourceInput I A seed D)).argv.getD i 0
  leftEnd : A.leftTagged+I.nB*(A.J+2)≤addr I.free I.capacity 1
  rightEnd : A.rightTagged+I.nC*(A.J+2)≤addr I.free I.capacity 1
  leftRead : ∀i<I.nB,∀j<A.J+2,
    μ (A.leftTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=L i j
  rightRead : ∀i<I.nC,∀j<A.J+2,
    μ (A.rightTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=R i j
  leftBound : ∀i<I.nB,∀j<A.J+2, |L i j|≤(U : ℤ)
  rightBound : ∀i<I.nC,∀j<A.J+2, |R i j|≤(U : ℤ)
  weightCap : U^2≤I.weightCap
  headerCells : 106≤I.capacity
  tensorCells : (entries (r := r) maps τ (sourceInput I A seed D)).length*(A.J+2)^4≤I.capacity
  quadCells : 4≤I.capacity
  powersCells : 5≤I.capacity
  columnCells : TernaryPairedColumnEnumeration.width K+1≤I.capacity
  tensorWord : (WeightedGlobalTensorWordResources.word K A.J
    (entries (r := r) maps τ (sourceInput I A seed D)).length
    (WeightedGlobalNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q (sourceInput I A seed D))) U : ℤ)≤lim.word
end ThreeSum.WeightedGlobalArenaSeedScoreReady


