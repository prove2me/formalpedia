-- Prove2me | Definitions.Def_OAIQ053K046
-- name    : OAIQ053K046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:06:45.803995+00:00
-- url     : https://prove2.me/theorems/5e2de070-b1c4-48ab-81c7-212ce79ecfa8
-- title:
--   Definitions bundle OAIQ053K046 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 72 declarations of OpenAI's Lean: 46 definitions and 26 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.IntegerProgram.rationalProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.basisProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.compressed`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.nextLaw`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.step`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.compressed`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.lawStep`, `OAI.MetricKMedian.IntegerLaw.ListOperation.entriesProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.positiveProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.ratioProgram`, `OAI.MetricKMedian.LPBinary.Input.encode`, `OAI.MetricKMedian.LPBinary.Program.inputRaw`, `OAI.MetricKMedian.LPBinary.Repair.raw`, `OAI.MetricKMedian.LPBinary.Scale.candidate`, `OAI.MetricKMedian.LPBinary.Scale.feasible`, `OAI.MetricKMedian.LPBinary.Scale.selected`, `OAI.MetricKMedian.LPBinary.Scale.selectedScale`, `OAI.MetricKMedian.LPBinary.result`, `OAI.MetricKMedian.LPBinary.start`, `OAI.MetricKMedian.LPBinary.states`, `OAI.MetricKMedian.PCP.ProjectionSeed.LeftLabel`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.law`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.law`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.inputs`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.law`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.ctxInputs`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.ctxLaw`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.law`, `OAI.MetricKMedian.RoundingProgram.Input.run`, `OAI.MetricKMedian.RoundingProgram.State.compress`, `OAI.MetricKMedian.RoundingProgram.State.step`, `OAI.MetricKMedian.SparseBernoulli.Program.Input.state`, `OAI.MetricKMedian.SparseBernoulli.Program.State.increment`, `OAI.MetricKMedian.SparseBernoulli.Program.State.step`, `OAI.MetricKMedian.SparseBernoulli.Program.countProgram`, `OAI.MetricKMedian.SparseBundles.law`, `OAI.MetricKMedian.SparseCounts.run`, `OAI.MetricKMedian.SparseCounts.step`, `OAI.MetricKMedian.SparseGraph.Program.Input.state`, `OAI.MetricKMedian.SparseGraph.Program.QInput.input` and 6 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_AffineListCompiler`, `KMedian_Compression_CompressionBinaryProgram`, `KMedian_Compression_CompressionBounds`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Compression_GaussianStates`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_FractionalSelectProgram`, `KMedian_Optimization_IndexedInstanceLP`, `KMedian_Optimization_IntegralFractionalComparison`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPBinaryTrajectory`, `KMedian_Optimization_ZeroCostBranch`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Projection_Seed`, `KMedian_Sparse_SparseBundleLaw`, `KMedian_Sparse_SparseCountFeatures`, `KMedian_Sparse_SparseCountRun`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseRescaledInner`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K038`, `OAIQ053K039`, `OAIQ053K040`, `OAIQ053K041` and `OAIQ053K042` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K049`, `OAIQ053K050`, `OAIQ053K051`, `OAIQ053K052` and `OAIQ053K053`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K038
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K040
import Definitions.Def_OAIQ053K041
import Definitions.Def_OAIQ053K042

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListCompiler
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def basisProgram : PolyProgram eslots er basis := by
  let tl := listTail eu ()
  let zero : PolyProgram eu Ratio.encode (fun _ : Unit => (0:ℚ)) := constant eu Ratio.encode 0
  let zeros := tl.comp (zero.listMap ())
  let nonnil := (((constant eslots Ratio.encode 1).fanout zeros).comp (listCons Ratio.encode))
  exact (ite (listIsEmpty eu) nonnil (constant eslots er [])).congr _ (fun _ => rfl)
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianStates
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian
open Finset

 theorem kernelStates_return_height (R N L : ℕ) (A : RatMatrix R N) (hRN : R<N)
    (hnum : ∀ i j, |(values A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((values A i j).den:ℤ) ≤ (2:ℤ)^L)
    (B : MatrixState) (hB : B ∈ kernelStates R N A) (j : Fin B.cols) :
    |((kernelVector B.rows B.cols B.data)[j.val]).num| ≤ (2:ℤ)^(returnHeight R N L) ∧
      (((kernelVector B.rows B.cols B.data)[j.val]).den:ℤ) ≤ (2:ℤ)^(returnHeight R N L) := by
  obtain ⟨P⟩ := kernelStates_certificate (values A) R N A (ResidualCertificate.initial _) B hB
  have hrow : B.rows ≤ R := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.row P.row_injective
  have hcol : B.cols ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.col P.col_injective
  have hentry := kernelStates_entry_height R N L A hnum hden B hB
  have hb := rational_input_kernel_bounds B.rows B.cols (residualHeight R N L) (values B.data)
    (kernelStates_underdetermined R N A hRN B hB) (fun i j => (hentry i j).1) (fun i j => (hentry i j).2) j
  have hp : 2*B.rows*(B.rows+residualHeight R N L*(B.cols+1)) ≤ returnHeight R N L := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hrow)
      (Nat.add_le_add hrow (Nat.mul_le_mul_left _ (Nat.add_le_add_right hcol 1)))
  have he := congrFun (kernelVector_eq B.rows B.cols B.data) j
  rw [he]
  exact ⟨hb.1.trans (pow_le_pow_right₀ (by norm_num) hp),hb.2.trans (pow_le_pow_right₀ (by norm_num) hp)⟩

end MetricKMedian.Gaussian
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianInputBounds
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset Polynomial

 theorem input_audit (I : Input) :
    Audit I.encode.length I.encode.length (residualHeight I.encode.length I.encode.length I.encode.length)
      (returnHeight I.encode.length I.encode.length I.encode.length) I.rows I.cols I.data := by
  let L := I.encode.length
  obtain ⟨hr,hn,hh⟩ := input_bounds I
  intro B hB
  obtain ⟨P⟩ := kernelStates_certificate (values I.data) I.rows I.cols I.data (ResidualCertificate.initial _) B hB
  have hrB : B.rows ≤ I.rows := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.row P.row_injective
  have hnB : B.cols ≤ I.cols := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.col P.col_injective
  refine ⟨hrB.trans hr,hnB.trans hn,?_,?_⟩
  · intro i j
    have hb := kernelStates_entry_height I.rows I.cols L I.data (fun i j => (hh i j).1) (fun i j => (hh i j).2) B hB i j
    exact HasHeight.mono hb (residualHeight_mono hr hn le_rfl)
  · intro j
    have hb := kernelStates_return_height I.rows I.cols L I.data I.underdetermined
      (fun i j => (hh i j).1) (fun i j => (hh i j).2) B hB j
    exact HasHeight.mono hb (returnHeight_mono hr hn le_rfl)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.IntegerProgram
open Binary Binary.PolyProgram

noncomputable def rationalProgram : PolyProgram Input.encode ListOperation.Input.encode Input.rational := by
  let cast := (ratOfInt.listMap 0).listMap []
  let raw := (cast.second ListOperation.eslots)
  exact raw.recode Input.raw (fun _ => rfl) (fun I => by
    change ListOperation.edata (List.replicate I.n (),castRows (List.ofFn (fun i => List.ofFn (I.V i)))) = _
    rw [castRows_ofFn]
    simp only [ListOperation.Input.encode,ListOperation.Input.raw,Input.rational,values_tabulate])

end MetricKMedian.Gaussian.IntegerProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def entriesProgram : PolyProgram ed ees entries := by
  let zz := encodePair Signed.encode er
  let zip := (snd es (encodePair er em)).comp (listZip Signed.encode er 0 [])
  exact (zip.comp (((listIndices zz (0,[])).fanout (identity (encodeList zz))).comp (listZip Nat.bits zz 0 (0,[])))).congr _ (fun _ => rfl)

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset

noncomputable def ratioProgram : PolyProgram ee Ratio.encode ratio :=
  ((((fst Signed.encode Signed.encode).comp ratOfInt).fanout ((snd Signed.encode Signed.encode).comp ratOfInt)).comp ratDiv).congr _ (fun _ => rfl)
noncomputable def positiveProgram : PolyProgram ee encodeBool (fun e : Entry => decide (0<e.2)) :=
  (((constant ee Signed.encode 0).fanout (snd Signed.encode Signed.encode)).comp intLT).congr _ (fun _ => rfl)

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionListStep
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
def Input.nextLaw (I : Input) : IntegerLaw (Fin I.n) :=
  if h : I.large then compressionStepAuto I.μ I.v h else I.μ

def Input.step (I : Input) : Input := {I with μ := I.nextLaw}

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionBounds
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight _root_.OAI.MetricKMedian.RationalLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset Polynomial

def lawStep {n d : ℕ} (v : Fin n → Fin d → ℤ) (μ : IntegerLaw (Fin n)) : IntegerLaw (Fin n) :=
  if h : d+1 < μ.support.card then compressionStepAuto μ v h else μ

theorem input_iterate (I : Input) (t : ℕ) :
    Input.step^[t] I=⟨I.n,I.d,(lawStep I.v)^[t] I.μ,I.v⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
      rfl

theorem lawStep_denominator {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j|≤(2:ℤ)^L) :
    (lawStep v μ).denominator ≤ μ.denominator*(2:ℤ)^((2*(d+1)*(d+1+L))*(n+1)) := by
  unfold lawStep
  split_ifs with h
  · rw [compressionStepAuto_eq μ v L hv h]
    exact (compressionStep_spec μ v L hv h).1
  · exact le_mul_of_one_le_right μ.denominator_pos.le (one_le_pow₀ (by norm_num))

theorem iterate_denominator {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j|≤(2:ℤ)^L) (hμ : μ.denominator≤(2:ℤ)^L) (t : ℕ) :
    ((lawStep v)^[t] μ).denominator ≤ (2:ℤ)^(L+((2*(d+1)*(d+1+L))*(n+1))*t) := by
  induction t with
  | zero => simpa using hμ
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      apply (lawStep_denominator _ v L hv).trans
      apply (mul_le_mul_of_nonneg_right ih (by positivity)).trans
      rw [← pow_add]
      have he : L+((2*(d+1)*(d+1+L))*(n+1))*t+((2*(d+1)*(d+1+L))*(n+1))=
          L+((2*(d+1)*(d+1+L))*(n+1))*(t+1) := by ring
      rw [he]

theorem compressSteps_eq_iterate {n d : ℕ} (v : Fin n → Fin d → ℤ) (t : ℕ) (μ : IntegerLaw (Fin n)) :
    compressStepsAuto v t μ=(lawStep v)^[t] μ := by
  induction t generalizing μ with
  | zero => rfl
  | succ t ih =>
      rw [compressStepsAuto,Function.iterate_succ_apply]
      split_ifs with h
      · rw [show lawStep v μ=compressionStepAuto μ v h from dite_eq_left h,ih]
      · have he : lawStep v μ=μ := dite_eq_right h
        rw [he,Function.iterate_fixed he]

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionBinaryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Polynomial

def Input.compressed (I : Input) : LawData :=
  let ν := compressStepsAuto I.v I.n I.μ
  (ν.denominator,List.ofFn ν.numerator)

def RationalInput.compressed (I : RationalInput) : LawData :=
  ( (I.μ.compressAuto I.v).denominator, List.ofFn (I.μ.compressAuto I.v).numerator)

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_IntegralFractionalComparison
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.TruncatedLP.instDecidableValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

theorem approximation_integral (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc0 : 1/2 ≤ ∑ j, d j (a j)) (hc1 : (∑ j, d j (a j)) ≤ 1) :
    let out := approximation d r k hr hk hd
    (∀ i : Fin n, 0 ≤ out.opening[i.val] ∧ out.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ out.assignment[j.val][i.val] ∧
      out.assignment[j.val][i.val] ≤ out.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, out.opening[i.val]) ≤ (k:ℚ)+1 ∧
    (∑ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]*d j i) ≤
      (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨z,hz,hzc⟩ := integral_comparison d k hd S hS hSk a ha hc1 (penalty r k)
  exact approximation_spec d r k hr hk hd _ hc0 hc1 z hz hzc

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateLPSelection
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {n m : ℕ} [NeZero n] [NeZero m]

theorem candidate_success (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : 0 < ∑ j, d j (a j)) :
    ∃ B ∈ feasibleScales d r k hr hk hd,
      (scaledCandidate d r k hr hk hd B).value d ≤ (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨B,hBg,hB,hc0,hc1⟩ := Normalization.matrixGoodGuess d hd a hc
  have hh := approximation_integral (fun j i => d j i/B) r k hr hk
    (fun j i => div_nonneg (hd j i) hB.le) S hS hSk a ha
    (by simpa only [sum_div] using hc0) (by simpa only [sum_div] using hc1)
  have hv : (scaledCandidate d r k hr hk hd B).Valid k := by
    simp only [scaledCandidate,dite_eq_left hB,FractionalData.Valid]
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
  have hcand : (scaledCandidate d r k hr hk hd B).value (fun j i => d j i/B) ≤
      (1+3/(r:ℚ))*(∑ j, d j (a j)/B) := by
    simpa only [scaledCandidate,dite_eq_left hB,FractionalData.value] using hh.2.2.2.2
  refine ⟨B,mem_filter.mpr ⟨hBg,hv⟩,?_⟩
  rw [value_div,← sum_div,← mul_div_assoc] at hcand
  exact (div_le_div_iff_of_pos_right hB).mp hcand

theorem selectFractional_spec (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : 0 < ∑ j, d j (a j)) :
    let out := selectFractional d r k hr hk hd
    out.Valid k ∧ out.value d ≤ (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨B,hB,hBc⟩ := candidate_success d r k hr hk hd S hS hSk a ha hc
  obtain ⟨hmem,hmin⟩ := rationalArgmin_spec (feasibleScales d r k hr hk hd)
    (fun B => (scaledCandidate d r k hr hk hd B).value d) ⟨B,hB⟩
  exact ⟨(mem_filter.mp hmem).2,(hmin B hB).trans hBc⟩

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input
abbrev encode (I : Input) := encodePair ers Nat.bits I.raw

end Input

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function
def start (r : ℕ) (I : Input) : State := (rawContext r I.raw,rawInitial I.raw)

namespace Program
noncomputable def inputRaw : PolyProgram Input.encode ei Input.raw :=
  (identity ei).recode Input.raw (fun _ => rfl) (fun _ => rfl)
end Program

theorem rawGrad_eq (r : ℕ) (I : Input) : rawGrad r I.raw=TruncatedLP.gradSize (n:=I.n) (m:=I.m) (TruncatedLP.penalty r I.k) := by
  simp only [rawGrad,Input.raw,Input.rows,head_ofFn,List.length_ofFn,rawPenalty,TruncatedLP.gradSize,TruncatedLP.penalty]
theorem rawSteps_eq (r : ℕ) (I : Input) : rawSteps r I.raw=TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k) := by
  unfold rawSteps
  rw [rawGrad_eq]
  rfl
theorem rawRate_eq (r : ℕ) (I : Input) : rawRate r I.raw=TruncatedLP.rate (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k) := by
  simp only [rawRate,rawGrad_eq,TruncatedLP.rate]

theorem start_eq (r : ℕ) (I : Input) : start r I=(rawContext r I.raw,I.iterate r 0) := by
  unfold start
  congr 1
  simp only [rawInitial,Input.raw,Input.rows,head_ofFn,List.length_ofFn,range_ofFn,List.map_ofFn,Input.iterate,Input.vector,ProjectedSubgradient.trajectory_zero]
  congr 1
  funext i
  simp only [ProjectedSubgradient.initial,ProjectedSubgradient.point_ofFn_apply]
  simp only [Fin.ext_iff,Function.comp_apply,Fin.val_zero]

theorem update_eq (r : ℕ) (I : Input) (t : ℕ) :
    update (rawContext r I.raw,I.iterate r t)=(rawContext r I.raw,I.iterate r (t+1)) := by
  unfold update
  congr 1
  change Truncated.next I.rows (I.iterate r t) (TruncatedLP.penalty r I.k) I.k (rawRate r I.raw)=I.iterate r (t+1)
  rw [rawRate_eq]
  unfold Input.rows Input.iterate
  rw [Truncated.next_ofFn]
  have he : Vector.ofFn (ProjectedSubgradient.point (I.vector r t))=I.vector r t := by ext index hindex; simp
  rw [he]
  rfl

theorem update_iterate (r : ℕ) (I : Input) (t : ℕ) :
    update^[t] (start r I)=(rawContext r I.raw,I.iterate r t) := by
  induction t with
  | zero => exact start_eq r I
  | succ t ih => rw [Function.iterate_succ_apply',ih,update_eq]
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryTrajectory
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Polynomial Function

def states (r : ℕ) (I : Input) : List State := Iteration.iterates update (start r I) (rawSteps r I.raw)

theorem states_eq (r : ℕ) (I : Input) :
    states r I=List.ofFn (fun t : Fin (rawSteps r I.raw) => (rawContext r I.raw,I.iterate r t.val)) := by
  rw [states,Iteration.iterates_eq,range_ofFn,List.map_ofFn]
  congr 1
  funext t
  exact update_iterate r I t.val
def result (r : ℕ) (I : Input) : Row := (choose (states r I)).2

 theorem value_eq (r : ℕ) (I : Input) (t : ℕ) :
    value (rawContext r I.raw,I.iterate r t)=
      TruncatedLP.objective I.distance (ProjectedSubgradient.point (I.vector r t)) (TruncatedLP.penalty r I.k) := by
  unfold value
  change Truncated.objective I.rows (I.iterate r t) (TruncatedLP.penalty r I.k)=_
  exact Truncated.objective_ofFn _ _ _

 theorem result_eq (r : ℕ) (hr : 0 < r) (I : Input) :
    result r I=List.ofFn (ProjectedSubgradient.point (TruncatedLP.optimize I.distance r I.k (TruncatedLP.penalty r I.k) hr I.kpos (TruncatedLP.penalty_pos r I.k hr))) := by
  let T := TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k)
  have hT : 0 < T := TruncatedLP.steps_pos _ _ _ hr I.kpos (TruncatedLP.penalty_pos r I.k hr)
  let : NeZero T := ⟨hT.ne'⟩
  unfold result choose
  have hs := states_eq r I
  rw [rawSteps_eq] at hs
  rw [hs,selectMinimum_ofFn]
  simp only [value_eq]
  unfold TruncatedLP.optimize
  simp only [Input.iterate,Input.vector]
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
def raw (r : ℕ) (I : Input) : Output := finish I.rows (result r I) (rawPenalty r I.raw) (TruncatedLP.loss r I.k)

end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalSelectProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

def candidate (r : ℕ) (I : Input) (B : ℚ) : Repair.Output :=
  if 0 < B then Repair.raw r (I.scale B) else I.zeroOutput

def feasible (r : ℕ) (I : Input) : Row := (guesses I.rows).filter (fun B => Repair.valid (candidate r I B) I.k)
def selectedScale (r : ℕ) (I : Input) : ℚ := argmin (feasible r I) (fun B => Repair.value (candidate r I B) I.rows)
def selected (r : ℕ) (I : Input) : Repair.Output := candidate r I (selectedScale r I)

end Scale
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_IndexedInstanceLP
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

theorem computedFractional_spec (I : Instance) (r : ℕ) (hr : 0 < r)
    (hJ : I.clients.Nonempty) (S : Finset (Fin I.n))
    (hSF : S ⊆ I.facilities) (hS : S.Nonempty) (hSk : S.card ≤ I.k)
    (hc : 0 < rationalCost I S) :
    let out := I.computedFractional r hr hJ
    out.Valid I.k ∧ out.value I.indexedDistance ≤ (1+3/(r:ℚ))*rationalCost I S := by
  let : NeZero I.facilities.card := ⟨(card_pos.mpr I.facilities_nonempty).ne'⟩
  let : NeZero I.clients.card := ⟨(card_pos.mpr hJ).ne'⟩
  obtain ⟨T,hT,hTc,a,ha,hac⟩ := I.indexed_integral S hSF hS
  have hh := TruncatedLP.selectFractional_spec I.indexedDistance r I.k hr I.k_pos
    I.indexedDistance_nonneg T hT (by rwa [hTc]) a ha (by rwa [hac])
  rwa [hac] at hh

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ZeroCostBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

theorem initialPhase_spec (I : Instance) (r : ℕ) (hr : 0 < r) :
    if h : I.zeroTest then
      I.zeroOutput ⊆ I.facilities ∧ I.zeroOutput.Nonempty ∧ I.zeroOutput.card ≤ I.k ∧
        cost I I.zeroOutput=0
    else
      let out := I.computedFractional r hr (I.nonzero_clients h)
      out.Valid I.k ∧ (out.value I.indexedDistance:ℝ) ≤
        (1+3/(r:ℝ))*optimum I := by
  split_ifs with h
  · exact I.zeroOutput_spec h
  · obtain ⟨S,hSF,hS,hSk,he⟩ := I.optimum_attained
    have hc : 0 < rationalCost I S := by
      have hh := I.nonzero_optimum h
      rw [← he,← I.cast_rationalCost S] at hh
      exact_mod_cast hh
    obtain ⟨hv,hc⟩ := I.computedFractional_spec r hr (I.nonzero_clients h) S hSF hS hSk hc
    refine ⟨hv,?_⟩
    have hh : ((I.computedFractional r hr (I.nonzero_clients h)).value I.indexedDistance:ℝ) ≤
        (1+3/(r:ℝ))*(rationalCost I S:ℝ) := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr hc
      push_cast at hh
      exact hh
    rwa [I.cast_rationalCost,he] at hh

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
def State.compress {s : Bool} (x : State s) : State s :=
  { x with μ := x.μ.compressAuto SparseWeightedPartial.features }
def State.step {s : Bool} (x : State s) : State s := x.branch.compress

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_DependentSparseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparseIntegerLaw.DependentProgram
open Binary Binary.PolyProgram Function BinarySparse
variable {C A : Type} (T : C → Type)

variable {T} (ec : C → List Bool) (ea : A → List Bool) (view : ∀ c, T c → A)

def Bundle.compress (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ) (x : Bundle T) : Bundle T :=
  ⟨x.ctx,x.law.compressAuto (v x.ctx)⟩

end MetricKMedian.SparseIntegerLaw.DependentProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram

def State.increment (x : State) : State := ⟨⟨x.ctx.input,x.ctx.t+1⟩,x.law⟩
def State.step (d : ℕ) (x : State) : State :=
  State.increment (if x.ctx.t<x.ctx.input.n then
    Bundle.compress (fun c : Context => (c.input.n+1)^d) (fun _ => features (d:=d))
      (Bundle.branch probability probability_unit endpoint x)
    else x)

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram

def Input.state (x : Input) (d t : ℕ) : State := ⟨⟨x,t⟩,run (d:=d) x.p x.feasible t⟩

 theorem state_next (x : Input) (d t : ℕ) : State.step d (x.state d t)=x.state d (t+1) := by
  have hp (ht : t<x.n) : probability ⟨x,t⟩=(fun _ => x.p ⟨t,ht⟩) := by
    funext q; simp only [probability,dite_eq_left ht]
  have he (ht : t<x.n) : endpoint ⟨x,t⟩=(fun q b => SparseBernoulli.endpoint q ⟨t,ht⟩ b) := by
    funext q b i
    simp only [endpoint,SparseBernoulli.endpoint,Fin.ext_iff]
  unfold State.step Input.state
  by_cases ht : t<x.n
  · rw [ite_eq_left ht]
    change (⟨⟨x,t+1⟩, ((run (d:=d) x.p x.feasible t).branch
      (probability ⟨x,t⟩) (probability_unit ⟨x,t⟩) (endpoint ⟨x,t⟩)).compressAuto features⟩ : State)=_
    rw [run,dite_eq_left ht]
    apply congrArg (fun μ => (⟨⟨x,t+1⟩,μ⟩ : State))
    simp only [SparseIntegerLaw.step,hp ht,he ht]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

 theorem state_iterate (x : Input) (d t : ℕ) : (State.step d)^[t] x.start=x.state d t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n :=
  (listLength Ratio.encode 0).recode (fun x => List.ofFn x.p) (fun _ => rfl) (fun x => by simp only [List.length_ofFn])

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparsePhysicalBatch.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse SparseIntegerLaw.DependentProgram
open SparseGraph.ListOperation (Row Table et)
def Input.bern (bal : Bool) (x : Input) : SparseIntegerLaw (Fin x.n → Bool) :=
  SparseBernoulli.run (d:=4) (x.bernInput bal).p (x.bernInput bal).feasible x.n
def Input.part (bal : Bool) (x : Input) : SparseIntegerLaw (Finset (Fin x.n)) :=
  (x.bern bal).map (fun ω => if bal then balanced x.Z x.C ω else unbalanced x.Z ω)
end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchProposalProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ProposalProgram
open Finset FixedBatch Binary Binary.PolyProgram
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

variable {I}

def Input.law (x : Input I) := proposal x.G x.Δ x.g x.b x.p x.φ x.hp x.hφ x.hupper x.enumActions
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

def Input.run {s : Bool} (x : Input s) (t : ℕ) : State s :=
  ⟨x.n,x.β,x.positive,if hs : s=true then SparseSignedPartial.run x.β x.p t
    else SparseWeightedPartial.run x.β (x.positive (by simpa using hs)) x.p t⟩

theorem input_iterate {s : Bool} (x : Input s) (t : ℕ) :
    State.step^[t] x.start=x.run t := by
  cases s <;> induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih]
    rfl

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)
def State.step (x : State) : State :=
  State.increment (if x.ctx.t<x.ctx.input.m then
    Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m))
      (fun _ => features) x.product else x)

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)

def Input.state (x : Input) (t : ℕ) : State := ⟨⟨x,t⟩,run x.columns t⟩

theorem state_next (x : Input) (t : ℕ) : State.step (x.state t)=x.state (t+1) := by
  have he (ht : t < x.m) : update ⟨x,t⟩=(fun G S => next G S ⟨t,ht⟩) := by
    funext G S i
    by_cases h : i=⟨t,ht⟩
    · subst i; simp only [update,next,Function.update_self,ite_true]
    · have hv : i.val≠t := fun hh => h (Fin.ext hh)
      simp only [update,next,Function.update_of_ne h,ite_eq_right hv]
  unfold State.step Input.state
  by_cases ht : t < x.m
  · rw [ite_eq_left ht]
    change (⟨⟨x,t+1⟩,((run x.columns t).prod (column ⟨x,t⟩) (update ⟨x,t⟩)).compressAuto features⟩ : State)=_
    rw [run,dite_eq_left ht]
    simp only [column,dite_eq_left ht,he ht,SparseGraph.step,SparseIntegerLaw.prodCompress]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

theorem state_iterate (x : Input) (t : ℕ) : (State.step)^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram
def QInput.input (x : QInput) : Input := ⟨x.n,x.m,SparseGraph.columns x.q⟩
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

local instance instLinearOrderCopyFin_r4a6bb0_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.instLinearOrderSubtypeCopyFinMemFinset
def Input.law (x : Input) := graphLaw x.d x.g x.P x.A

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchUpdateProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.RationalPhysicalKernel.UpdateProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

local instance instLinearOrderCopyFin_r4a6bb0_2 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
def Input.law (x : Input) := x.proposal.law.map x.update

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel.RoundProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram

local instance instLinearOrderCopyFin_r4a6bb0_3 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_r4a6bb0_1 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
def ctxInputs (x : Context) : List UpdateProgram.Input := x.toInput.law.states.toList.map (fun G => ⟨x,G⟩)

def ctxLaw (x : Context) : SparseIntegerLaw (Finset (CopyState.Copy (F:=Fin x.f) x.Δ)) := x.toInput.law.bindIndexed
  (fun i => (UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law)

 theorem law_step (x : Context) (s : State (Fin x.f) x.Δ x.g x.β) (hs : s.1=x.A) :
    (ctxLaw x)=(step x.d x.g x.β x.p x.φ x.P x.hp x.hφ x.hupper s).map Prod.fst := by
  unfold step
  erw [SparseIntegerLaw.map_map]
  unfold RationalBatchData.events
  erw [SparseIntegerLaw.map_bindIndexed]
  cases s with
  | mk A payload =>
    dsimp only at hs
    subst A
    unfold ctxLaw
    congr 1
    funext i
    erw [SparseIntegerLaw.map_map]
    rfl
end MetricKMedian.RationalPhysicalKernel.RoundProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalHistoriesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalPhysicalKernel.HistoryProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram
def law (P : ℕ → ℚ) (T : ℕ) (x : Context) := histories x.d x.g x.β x.p x.φ P x.hp x.hφ x.hupper x.A T

local instance instLinearOrderCopyFin_r4a6bb0_4 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_r4a6bb0_2 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
def inputs (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) : List Context :=
  (law P T x).states.toList.map (fun z => nextCtx x (P T) hP z.1.1)
end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Seed
attribute [-instance] _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionSeed

namespace MetricKMedian.PCP
open Finset
open scoped Classical BigOperators

namespace ProjectionSeed
open Amplifier

abbrev LeftLabel := (Label × Label) × Bool
end ProjectionSeed
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCounts
open Finset
variable {n m : ℕ}

def step (μ : SparseIntegerLaw (Table n m)) (ν : SparseIntegerLaw ((Fin n → ℕ)))
    (i : Fin m) : SparseIntegerLaw (Table n m) :=
  μ.prodCompress ν (fun G S => next G S i) features

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCounts
open Finset
variable {n m : ℕ}

def run (ν : Fin m → SparseIntegerLaw ((Fin n → ℕ))) : ℕ → SparseIntegerLaw (Table n m)
  | 0 => .dirac (fun _ _ => 0)
  | t+1 => if ht : t < m then step (run ν t) (ν ⟨t,ht⟩) ⟨t,ht⟩ else run ν t

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBundleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBundles
open Finset
variable {n m : ℕ}

abbrev law (q : Fin n → Fin m → ℚ) : SparseIntegerLaw (SparseCounts.Table n m) :=
  SparseCounts.run (fun j => SparseGridRounding.law (fun i => q i j)) m

end MetricKMedian.SparseBundles
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRescaledInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

abbrev law (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) := SparseBundles.law (piece P y p K)

end MetricKMedian.SparseRescaledInner
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

def kernel (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ) (z : State n m) :
    SparseIntegerLaw (State n m × SparseCounts.Table f n) :=
  (SparseRescaledInner.law P y p (total D q Δ z)).map (fun G => (z,G))

end MetricKMedian.SparsePrepared
end
end

end OAI
end


