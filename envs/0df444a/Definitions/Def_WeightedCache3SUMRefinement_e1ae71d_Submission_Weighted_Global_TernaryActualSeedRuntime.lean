-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualSeedRuntime
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualSeedRuntime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:22:01.774704+00:00
-- url     : https://prove2.me/theorems/321f43b3-bba6-4250-a77c-f07584d0cf76
-- title:
--   TernaryActualSeedRuntime
-- statement:
--   Definitions and structural lemmas for TernaryActualSeedRuntime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualSeedRuntime.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSeedCoefficientBudget_seed_coefficient_polynomial

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
abbrev threshold (K k m : ℕ) := WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m)
  (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) k
abbrev outputCap (K k m F : ℕ) := F*WeightedGlobalGoodOutputCatalog.cap m (nativePrime K m) (threshold K k m)
def scoreConstant (K k c d m F D E κ : ℕ) : ℝ :=
  ((2*nativePrime K m+6+2*sourceCoefficient K m F+
    1000000*(widthCoefficient m D E κ)^3:ℕ):ℝ)*volumeConstant K k c d m
def seedPolynomialC (K p B : ℕ) : ℕ :=
  Classical.choose (WeightedGlobalSeedCoefficientBudget.seed_coefficient_polynomial K p B p)
def seedPolynomialD (K p B : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (WeightedGlobalSeedCoefficientBudget.seed_coefficient_polynomial K p B p))
def menuSize (K m J : ℕ) : ℕ :=
  (nativePrime K m)^TernaryExtensionEncoding.menuDegree (nativePrime K m) (J+2) K
def prefixSeedTime {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j I A seed)) : ℕ :=
  (Finset.range (menuSize K m A.J*menuSize K m A.J)).sup fun seed=>
    LightWeightedGlobalSeedScoreFactory.runtime (D seed)
      (nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed (D seed))) K
      (4^fixedLength m) F (outputCap K k m F) ((nativePrime K m)*(nativePrime K m+1)^j)
      (WeightedGlobalGoodOutputCatalog.raws maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.wordCodes maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.mapCodes maps (threshold K k m))
def menuCoefficient (K p : ℕ) : ℕ :=(48*p^(4*K+1)+3)^2+1
def spanCoefficient (p : ℕ) : ℕ :=(p+1)*(LightPrimeCoefficient.mulAddTime p+500)
def controllerConstant (K k c d m F D E κ B : ℕ) : ℝ :=
  (menuCoefficient K (nativePrime K m):ℝ)*
    ((seedPolynomialC K (nativePrime K m) B:ℝ)*scoreConstant K k c d m F D E κ+
      (2*spanCoefficient (nativePrime K m)+2000:ℕ)*volumeConstant K k c d m)
def prefixControllerTime {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j I A seed)) : ℕ :=
  LightWeightedGlobalSeedController.time (menuSize K m A.J*menuSize K m A.J)
    (prefixSeedTime (K:=K) (k:=k) maps Q I A D)
    (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)))
def overheadCoefficient (m : ℕ) : ℕ :=40000*(fixedLength m+fixedAlpha m 2+1)+10000
def prefixOverhead (m j J p nB nC nO : ℕ) : ℕ :=
  LightWeightedGlobalPrefixPrepare.time m (j-1) (fixedAlpha m 2)+
    LightTernaryCommitKeys.time nB nC nO+copyTime (p^j*J)+5500
def prefixStageTime {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j I A seed)) : ℕ :=
  prefixControllerTime (K:=K) (k:=k) maps Q I A D+
    prefixOverhead m j A.J (nativePrime K m) I.nB I.nC I.requesterCount
def stageConstant (K k c d m F D E κ B : ℕ) : ℝ :=
  controllerConstant K k c d m F D E κ B+(overheadCoefficient m:ℝ)*volumeConstant K k c d m
def allStageTime {K k m F : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : ℕ→Input) (A : Inputs)
    (D : (j seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j (I j) A seed))
    (n : ℕ) : ℕ :=
  (Finset.range (radixLength m n)).sup fun old=>
    prefixStageTime (K:=K) (k:=k) maps Q (I (old+1)) A (D (old+1))
def allPrefixTime {K k m F : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : ℕ→Input) (A : Inputs)
    (D : (j seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j (I j) A seed))
    (n : ℕ) : ℕ :=
  LightWeightedGlobalPrefixInit.time (config (nativePrime K m) 0 (I 0) A 0)
    (radixLength m n) (allStageTime (K:=K) (k:=k) maps Q I A D n)
def prefixConstant (K k c d m F D E κ B : ℕ) : ℝ :=
  stageConstant K k c d m F D E κ B+50000*volumeConstant K k c d m
end ThreeSum.WeightedGlobalActualSeedRuntime
end
end WeightedCache3SUMRefinement_e1ae71d


