-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:53:59.13217+00:00
-- url     : https://prove2.me/theorems/6b1b40e1-2190-48f4-9bf5-52bb973cf666
-- title:
--   TernaryArenaControllerCore
-- statement:
--   Definitions and structural lemmas for TernaryArenaControllerCore, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaControllerCore.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaGuardTransport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerPlan
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaGuardTransport_tensor
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_reads
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_resources

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaControllerCore
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
def family (maps : Fin F→Weight m p) (τ cap U : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs)
    (D : (seed : ℕ)→Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ) :
    Family (config p r I A 0) :=
  WeightedGlobalArenaSeedCandidate.family maps τ cap U (WeightedGlobalArenaSeedPrimitiveGuards.rawCap m p r)
    (WeightedGlobalNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q I)) Q I A D L R
def seedTime {C : Config} [Fact C.p.Prime] (D : Family C)
    (K R S n : ℕ) (raws : List ℤ) (words maps : List ℕ) : ℕ :=
  (Finset.range n).sup (fun i => (D.candidate i).runtime K R S raws words maps)
structure InputsReady {lim : Limits} {depth K U n positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : (seed : ℕ)→Data (config p r I A seed))
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ) : Prop where
  prefixAt : I.prefixFree=WeightedGlobalArenaLayout.addr I.free I.capacity 13
  threshold : 0 < τ
  nonempty : 1 ≤ (WeightedGlobalGoodOutputCatalog.raws maps τ).length
  reads : ∀i < n, WeightedGlobalArenaSeedPrimitiveGuards.Reads I A i (D i) μ positionCap
  tensor : ∀i < n, WeightedGlobalArenaSeedScoreReady.TensorGuard
    (lim := lim) (depth := depth+1) (K := K) (U := U) maps τ cap Q I A (D i) μ L R
  resources : ∀i < n, WeightedGlobalArenaCandidateGuard.Resources
    (lim := lim) (depth := depth+1) (positionCap := positionCap) maps τ I A (D i)
  pairedWord : ∀i < n,
    |((family maps τ cap U Q I A D L R).candidate i).score K| ≤ lim.word
end ThreeSum.WeightedGlobalArenaControllerCore
end
end WeightedCache3SUMRefinement_e1ae71d


