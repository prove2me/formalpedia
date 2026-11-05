-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelection
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:45:36.648909+00:00
-- url     : https://prove2.me/theorems/896bbca5-02fe-4f4b-ad07-048f9ba6b24d
-- title:
--   LightTernaryPostSelection
-- statement:
--   Definitions and structural lemmas for LightTernaryPostSelection, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPostSelection.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryCompactReporter
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_resources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCompactPairedSupport_support

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalPostSelection
open Light LightOriginalSurvivors LightOriginalSurvivorPair
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
def body (pReporter : ℕ) : Stmt :=
  .call 8 (LightWeightedSourceCountHost.callArgs 0 21) 148 ;;
  .ite (v 148 =' k 0)
    (.ite (M (v 16) =' k 0) (.set 0 (k 0))
      (.ite (M (v 20) =' k 0) (.set 0 (k 0))
        (.call pReporter (LightWeightedSourceCountHost.callArgs 21 127) 0)))
    (.set 0 (k 1))
def libraries {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  ReportingHostRelocation.program LightOriginalSurvivorPair.program
    (LightWeightedGlobalCompactReporter.program S H)
def program {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  libraries S H ++ [body (9+(LightWeightedGlobalMomentReporter.program S H).length)]
def args {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (c : Layout)
    (scratch matrix : ℕ) : List ℤ := c.args ++
  LightWeightedGlobalCompactReporter.args S c.aBase c.nA scratch
    c.valueB c.packedB c.lengthB c.valueC c.packedC c.lengthC matrix
def time {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ)
    (c : Layout) (keysB keysC : ℕ → ℕ) : ℕ :=
  LightOriginalSurvivorPair.time keysB keysC c.nA c.nB c.nC c.L+
    LightWeightedGlobalCompactReporter.time S H+600
def compact (keys : ℕ → ℕ) (values : ℕ → ℤ) (n : ℕ) : ℕ → ℤ :=
  fun j => values (index keys n j)
structure Certificate {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (c : Layout) (lim : Limits) (d H a b U W detectorU scratch matrix : ℕ)
    (μ : ℕ → ℤ) (A B C : ℕ → ℤ) (keysB keysC position : ℕ → ℕ) : Prop where
  leftCount : S.left.NL = (indices keysB c.nB).length
  rightCount : S.right.NL = (indices keysC c.nC).length
  leftSrc : S.left.src = c.packedB
  rightSrc : S.right.src = c.packedC
  beforeMatrix : c.lengthC+1 ≤ matrix
  recordsApart : S.front.records+3*S.front.count ≤ c.outB ∨ c.lengthC < S.front.records
  matrixWindow : matrix+(2*H+1)*S.front.count ≤ scratch
  scratchSpace : scratch+(2*H+1) ≤ lim.space
  positions : ∀ i < S.front.count, position i < c.nA
  positionRead : ∀ i < S.front.count, μ (S.front.records+3*i) = (position i : ℤ)
  originalAbs : ∀ i < c.nA, |A i| ≤ (detectorU : ℤ)
  detectorWord : max (detectorU : ℤ) (LightMomentDeterminant.wordBound detectorU H) ≤ lim.word
  resources : ∀ ν,
    Output ν keysB B c.nB c.outB c.valueB c.packedB c.lengthB →
    Output ν keysC C c.nC c.outC c.valueC c.packedC c.lengthC → Kept μ ν c.outB →
    LightOriginalSurvivorStage.Above μ ν c.lengthC → c.Unchanged keysB keysC μ ν → LightWeightedGlobalCertifiedMomentDriver.Resources S lim (d+3) c.valueB c.valueC matrix
      (2*H+1) a b U W ν (compact keysB B c.nB) (compact keysC C c.nC)
  support : ∀ i < S.front.count,
    (TernaryPairedSupport.physicalSupport (WeightedGlobalNativePairMoments.mode (S := S) (i := i)
      (compact keysB B c.nB) (compact keysC C c.nC))).card ≤ H
  momentAbs : ∀ i < S.front.count, ∀ k ≤ 2*H,
    |∑ p : WeightedGlobalNativePairMoments.Pair S i,
      WeightedGlobalNativePairMoments.mass S i p*WeightedGlobalNativePairMoments.mode
        (compact keysB B c.nB) (compact keysC C c.nC) p^k| ≤ (detectorU : ℤ)
  nativeComplete :
    (∃ i < S.front.count, ∃ p : WeightedGlobalNativePairMoments.Pair S i,
      WeightedGlobalNativePairMoments.mode (compact keysB B c.nB) (compact keysC C c.nC) p=A (position i)) ↔
    (∃ i < c.nA, ∃ j < (indices keysB c.nB).length, ∃ k < (indices keysC c.nC).length,
      compact keysC C c.nC k=A i+compact keysB B c.nB j)
variable {lim : Limits}
end ThreeSum.LightWeightedGlobalPostSelection
end
end WeightedCache3SUMRefinement_e1ae71d


