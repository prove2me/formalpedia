-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
-- name    : Submission_Weighted_Global_TernaryActualPrefixRuntime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:58:31.739475+00:00
-- url     : https://prove2.me/theorems/d15b9bf2-0c1a-48ab-aea6-e5ca89071d13
-- title:
--   Ternary Actual Prefix Runtime
-- statement:
--   Definitions and structural lemmas for Ternary Actual Prefix Runtime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
def sourceWidth (J L U M : ℕ) :=J+L+Nat.log 2 (U+1)+Nat.log 2 (M+1)+3
def sourceVolume (xs : List ℤ) (J M NL bank groups cap : ℕ) :=
  NL+LightTernarySourceHost.size xs J+xs.length+M+NL*cap+groups*bank+1
def tensorCoefficient (K J : ℕ) : ℕ :=
  powTableTime 5+(J+2)^4*(LightWeightRow.time 4 ((J+2)^4)+3000)+
    LightTernaryPairedPotential.time K (J+2)+6000
def nativeFactor (K k b m : ℕ) : ℕ :=
  b*(nativeFamily K m k).length*
    WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m)
      (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) k
def fullCharge (K m : ℕ) : ℝ :=
  max 1 (max (WeightedGlobalOversizeRates.bankCharge K m)
    (max (WeightedGlobalOversizeRates.queryCharge K m)
      (max (WeightedGlobalOversizeRates.endpointCharge K m)
        (max (WeightedGlobalOversizeRates.histogramCharge K m) (WeightedGlobalOversizeRates.incidenceCharge K m)))))
def fullExponent (K k c d m : ℕ) : ℝ :=fullCharge K m+overheadCharge k c d m
def volumeConstant (K k c d m : ℕ) : ℝ :=
  (baseFactor K k c d m:ℝ)*
    (Real.exp (WeightedGlobalOversizeDimensions.bankSlope K m)+
      Real.exp (WeightedGlobalOversizeDimensions.tableSlope K m (endpointSize m))+
      Real.exp (WeightedGlobalOversizeDimensions.tableSlope K m (nativePrime K m))+
      Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/WeightedGlobalParameters.z^1024)
def volumeBundle (K k b m n j : ℕ) : ℝ :=
  (nativeFactor K k b m:ℝ)^j*
    ((bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(nativePrime K m:ℝ)^j+
      (n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*
        WeightedGlobalCountFrontendBudget.envelope m j)
def localFactor (m : ℕ) : ℕ :=17+2*WeightedGlobalPartitionCount.partitionLoss (2380004124000*m) (292746547000*m)
def seedCoefficient (K J p B V prefixLen : ℕ) : ℕ :=
  60*J+200+(LightSignedRowHash.time (J+2) p B+120)+
    (LightTernaryWantedCanonical.overhead p V+LightTernaryWantedCanonical.stepCost V+40)*(prefixLen+1)+
    tensorCoefficient K J+10000
def seedVolume {C : LightWeightedGlobalSeedScoreFactory.Config}
    (D : LightWeightedGlobalSeedScoreFactory.Data C) {N : ℕ}
    (host : WeightedSourceCountExecutionFactory.Setup N) (R S cap : ℕ)
    (raws : List ℤ) (words maps : List ℕ) : ℕ :=
  C.catalogRows+C.nB+C.nC+C.nO+C.nO*cap^C.prefixLength+C.power*C.p+
    D.H R S raws words maps+host.runtime+1
def potentialCoefficient (K : ℕ) : ℕ :=
  powTableTime (TernaryPairedColumnEnumeration.width K+1)+
    280*TernaryPairedColumnEnumeration.width K+LightTernaryPairedPolynomial.time K+700
def capacityBits (M D E κ : ℕ) : ℕ :=D+2*E+M*(κ+1)*E+1
def nativeHost {K k m F : ℕ} (j : ℕ) (maps : Fin F→Weight m (nativePrime K m))
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) :=
  setup (r:=j) maps (WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m)
    (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) k)
    (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) Q I
def allHostTime {K k m F : ℕ} (maps : Fin F→Weight m (nativePrime K m))
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : ℕ→Input) (n : ℕ) : ℕ :=
  ∑j∈Finset.range (radixLength m n+1), (nativeHost (K:=K) (k:=k) j maps Q (I j)).runtime
def sourceCoefficient (K m F : ℕ) : ℕ :=
  8000*(2*fixedLength m+3*nativePrime K m+6)*(F*endpointSize m+3)
def widthCoefficient (m D E κ : ℕ) : ℕ :=5*fixedLength m+2*capacityBits (outputSize m) D E κ+3
def hostConstant (K k c d m F D E κ : ℕ) : ℝ :=
  ((2*sourceCoefficient K m F+1000000*(widthCoefficient m D E κ)^3:ℕ):ℝ)*volumeConstant K k c d m
end ThreeSum.WeightedGlobalActualPrefixRuntime


