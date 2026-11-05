-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:53:02.24771+00:00
-- url     : https://prove2.me/theorems/b6eb08f2-4028-4b16-9b72-df6e5168e434
-- title:
--   LightTernaryPreparedPostSelection
-- statement:
--   Definitions and structural lemmas for LightTernaryPreparedPostSelection, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
structure Inputs (c : Layout) (lim : Limits) (d U W : ℕ) (μ : ℕ → ℤ)
    (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  hA : c.aBase+c.nA ≤ c.outB
  hB : c.bBase+c.nB ≤ c.outB
  hC : c.cBase+c.nC ≤ c.outB
  hkB : c.keyB+c.nB ≤ c.outB
  hkC : c.keyC+c.nC ≤ c.outB
  hhB : c.histB+c.q ≤ c.outB
  hhC : c.histC+c.q ≤ c.outB
  hp : c.powers+(W+1) ≤ c.outB
  hB1 : c.outB+2*c.nB ≤ c.valueB
  hB2 : c.valueB+c.nB ≤ c.packedB
  hB3 : c.packedB+c.nB ≤ c.lengthB
  hBC : c.lengthB+1 ≤ c.outC
  hC1 : c.outC+2*c.nC ≤ c.valueC
  hC2 : c.valueC+c.nC ≤ c.packedC
  hC3 : c.packedC+c.nC ≤ c.lengthC
  hEnd : c.lengthC+1 ≤ lim.space
  hword : ((c.nB+c.nC+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word
  hkeysB : ∀ i < c.nB, keysB i < c.q
  hkeysC : ∀ i < c.nC, keysC i < c.q
  hreadKB : ∀ i < c.nB, μ (c.keyB+i) = (keysB i : ℤ)
  hreadKC : ∀ i < c.nC, μ (c.keyC+i) = (keysC i : ℤ)
  hboundA : ∀ i < c.nA, |A i| ≤ U
  hboundB : ∀ i < c.nB, |B i| ≤ U
  hboundC : ∀ i < c.nC, |C i| ≤ U
  hreadA : ∀ i < c.nA, μ (c.aBase+i) = A i
  hreadB : ∀ i < c.nB, μ (c.bBase+i) = B i
  hreadC : ∀ i < c.nC, μ (c.cBase+i) = C i
  hvalueWord : 2*(U : ℤ)+3 ≤ lim.word
  hsortedB : ∀ i j, i < j → j < c.nB → B i < B j
  hsortedC : ∀ i j, i < j → j < c.nC → C i < C j
  hL : c.L ≤ W
  hnB : c.nB < 2^c.L
  hnC : c.nC < 2^c.L
  hd : d+c.L+5 ≤ lim.depth

  beforeA : c.aBase+c.nA ≤ c.powers
  beforeB : c.bBase+c.nB ≤ c.powers
  beforeC : c.cBase+c.nC ≤ c.powers
  beforeKeyB : c.keyB+c.nB ≤ c.powers
  beforeKeyC : c.keyC+c.nC ≤ c.powers
  powerBeforeHist : c.powers+(W+1) ≤ c.histB
  histBeforeHist : c.histB+c.q ≤ c.histC
  scoreWordB : ((c.nB*c.nB+c.nB+c.q+16 : ℕ) : ℤ) ≤ lim.word
  scoreWordC : ((c.nC*c.nC+c.nC+c.q+16 : ℕ) : ℤ) ≤ lim.word
def body (pPost : ℕ) : Stmt :=
  .call 5 [v 6,v 3,v 7,v 5,v 10,v 11,v 12,v 8,v 9] 148 ;;
  .call pPost (LightWeightedSourceCountHost.callArgs 0 148) 0
def libraries {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  ReportingHostRelocation.program LightTernaryFinalPreparation.program (LightWeightedGlobalPostSelection.program S H)
def program {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  libraries S H ++ [body (6+(LightWeightedGlobalPostSelection.libraries S H).length)]
def args {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (c : Layout) (scratch matrix : ℕ) : List ℤ :=
  LightWeightedGlobalPostSelection.args S c scratch matrix
def time {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) (c : Layout)
    (keysB keysC : ℕ → ℕ) : ℕ :=
  LightTernaryFinalPreparation.time c.nB c.nC c.q c.L + LightWeightedGlobalPostSelection.time S H c keysB keysC+200
def closedProgram (xl yl zl xr yr zr : List ℤ) (H : ℕ) : Program :=
  ReportingHostRelocation.program LightTernaryFinalPreparation.program
    (LightWeightedGlobalPostSelection.closedProgram xl yl zl xr yr zr H)++
      [body (6+(139*(TernaryMomentSchedule.channels (2*H+1)).length+17))]
end ThreeSum.LightWeightedGlobalPreparedPostSelection
end
end WeightedCache3SUMRefinement_e1ae71d


