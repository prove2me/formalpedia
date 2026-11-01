-- Prove2me | Definitions.Def_OAIQ053K056
-- name    : OAIQ053K056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:13:09.120001+00:00
-- url     : https://prove2.me/theorems/ab0e38be-916e-4ffc-a5bb-958c91aa999b
-- title:
--   Definitions bundle OAIQ053K056 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 57 declarations of OpenAI's Lean: 48 definitions and 9 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.IntegerProgram.kernelProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.bodyProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.kernelProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.compressProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.integerInputProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.iterateProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.nextLawProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.productiveProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.rationalCompressProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.scaledRowsProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.stepProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.affineKernelProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.extendProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.fullProgram`, `OAI.MetricKMedian.RationalBatchData.Ordinal.sets`, `OAI.MetricKMedian.RoundingProgram.Input.encode`, `OAI.MetricKMedian.RoundingProgram.Input.raw`, `OAI.MetricKMedian.RoundingProgram.State.encode`, `OAI.MetricKMedian.RoundingProgram.State.raw`, `OAI.MetricKMedian.RoundingProgram.compressProgram`, `OAI.MetricKMedian.RoundingProgram.compressionInputProgram`, `OAI.MetricKMedian.RoundingProgram.countProgram`, `OAI.MetricKMedian.RoundingProgram.endpoint`, `OAI.MetricKMedian.RoundingProgram.endpointProgram`, `OAI.MetricKMedian.RoundingProgram.probability`, `OAI.MetricKMedian.RoundingProgram.probabilityProgram`, `OAI.MetricKMedian.RoundingProgram.startProgram`, `OAI.MetricKMedian.RoundingProgram.statesProgram`, `OAI.MetricKMedian.RoundingProgram.vectorData`, `OAI.MetricKMedian.RoundingProgram.weightsProgram`, `OAI.MetricKMedian.SparseCardinalRounding.Program.inputProgram`, `OAI.MetricKMedian.SparseCardinalRounding.Program.result`, `OAI.MetricKMedian.SparseGraph.Program.Context.encode`, `OAI.MetricKMedian.SparseGraph.Program.Context.raw`, `OAI.MetricKMedian.SparseGraph.Program.Input.encode`, `OAI.MetricKMedian.SparseGraph.Program.Input.raw`, `OAI.MetricKMedian.SparseGraph.Program.InputRaw`, `OAI.MetricKMedian.SparseGraph.Program.QInput.result`, `OAI.MetricKMedian.SparseGraph.Program.State.encode`, `OAI.MetricKMedian.SparseGraph.Program.columnRaw` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_AffineListCompiler`, `KMedian_Compression_CompressionBinaryProgram`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_GaussianBinaryProgram`, `KMedian_Compression_GaussianListMachine`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Sparse_SparseIterationHeight`, `KMedian_Sparse_SparseListTrim`.
--
--   **Imports.** It imports the bundles `OAIQ053K048`, `OAIQ053K049`, `OAIQ053K050` and `OAIQ053K051` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K064`, `OAIQ053K065`, `OAIQ053K066` and `OAIQ053K067`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K048
import Definitions.Def_OAIQ053K049
import Definitions.Def_OAIQ053K050
import Definitions.Def_OAIQ053K051

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def bodyProgram : PolyProgram eState (encodeLoop eState er) body :=
  sumElim ed eUp downProgram upProgram (([],[]),[]) ([],[])
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianBinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Polynomial

noncomputable def kernelProgram : PolyProgram Input.encode er Input.result :=
  loopFrom startProgram bodyProgram Input.result (2*X+2) statePolynomial (fun I => by
    obtain ⟨t,ht,hrun⟩ := full_run I.encode.length I.encode.length
      (residualHeight I.encode.length I.encode.length I.encode.length)
      (returnHeight I.encode.length I.encode.length I.encode.length)
      I.rows I.cols I.data I.underdetermined (input_audit I)
    refine ⟨t,?_,?_⟩
    · have hr := (input_bounds I).1
      simp only [eval_add,eval_mul,eval_ofNat,eval_X]
      omega
    · simpa only [statePolynomial_eval,Input.result] using hrun)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerKernelProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.IntegerProgram
open Binary Binary.PolyProgram

noncomputable def kernelProgram : PolyProgram Input.encode er Input.result :=
  ((rationalProgram.comp ListOperation.kernelProgram).comp IntegerList.numeratorsProgram).congr _ (fun I => by
    simp only [Function.comp_apply,ListOperation.Input.result,ListOperation.kernelList,IntegerList.numerators_ofFn]
    unfold Input.result computedIntegerKernel
    simp only [Vector.getElem_ofFn]
    rfl)
end MetricKMedian.Gaussian.IntegerProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListCompiler
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def extendProgram : PolyProgram (encodePair (encodeList ez) Nat.bits) Signed.encode
    (fun x : List (ℕ × ℤ) × ℕ => extend x.1 x.2) := by
  let a := fst Nat.bits ez
  let b := (snd Nat.bits ez).comp (fst Nat.bits Signed.encode)
  let test := (b.fanout a).comp natEQ
  let filtered := (exchange (encodeList ez) Nat.bits).comp (test.listFilterWith (0,0) 0)
  exact ((filtered.comp ((snd Nat.bits Signed.encode).listMap (0,0))).comp IntegerList.sumProgram).congr _ (fun _ => rfl)

noncomputable def fullProgram : PolyProgram (encodePair ed er) er (fun x : Data × Row => full x.1 x.2) := by
  let x := fst ed er
  let z := snd ed er
  let ids := ((x.comp activeProgram).comp ((fst Nat.bits (encodePair Signed.encode er)).listMap (0,(0,[]))))
  let zs := (ids.fanout z).comp (listZip Nat.bits Signed.encode 0 0)
  let out := ((x.comp (snd es (encodePair er em))).comp (fst er em)).comp (listIndices Signed.encode 0)
  exact ((zs.fanout out).comp (extendProgram.listMapWith 0 0)).congr _ (fun _ => rfl)

noncomputable def affineKernelProgram : PolyProgram Input.encode er (fun I => List.ofFn (computedAffineKernel I.μ I.v)) := by
  let raw : PolyProgram Input.encode ed Input.raw := (identity ed).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let kern := kernelInputProgram.comp Gaussian.IntegerProgram.kernelProgram
  exact ((raw.fanout kern).comp fullProgram).congr _ (fun I => full_raw I)

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionListStep
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset

noncomputable def productiveProgram : PolyProgram (fun I : {I : Input // I.large} => I.val.encode) el
    (fun I => (I.val.step).lawData) := by
  let a := dimProgram.fanout ((lawProgram.comp (snd Signed.encode er)).fanout featuresProgram)
  let A : PolyProgram (fun I : {I : Input // I.large} => I.val.encode) ListOperation.Input.encode
      (fun I => I.val.affine I.property) :=
    a.recode (fun I : {I : Input // I.large} => I.val) (fun _ => rfl) (fun _ => rfl)
  let K := A.comp ListOperation.affineKernelProgram
  let M := lawProgram.recode (fun I : {I : Input // I.large} => I.val) (fun _ => rfl) (fun _ => rfl)
  exact ((M.fanout K).comp ListPivot.updateProgram).congr _ (fun I => by
    unfold Input.step Input.lawData Input.nextLaw
    rw [dite_eq_left I.property]
    obtain ⟨L,hL⟩ := exists_feature_bound I.val.v
    have hz := computedAffineKernel_spec I.val.μ I.val.v L hL I.property
    exact ListPivot.update_ofFn I.val.μ _ (positiveSet_nonempty _ hz.2.1 hz.1) hz.2.1)

noncomputable def nextLawProgram : PolyProgram Input.encode el (fun I => (I.step).lawData) := by
  let safe := checkedProgram Input.large largeProgram ⟨dummy,dummy_large⟩
  let work := safe.comp productiveProgram
  exact (ite largeProgram lawProgram work).congr _ (fun I => by
    by_cases h : I.large
    · simp only [Function.comp_apply, h,decide_true,ite_true,checked,dite_eq_left]
    · simp only [Function.comp_apply, h,decide_false,Bool.false_eq_true,ite_false]
      simp [Input.step,Input.lawData,Input.nextLaw,h])

noncomputable def stepProgram : PolyProgram Input.encode Input.encode Input.step :=
  ((dimProgram.fanout (nextLawProgram.fanout featuresProgram))).recode id (fun _ => rfl) (fun _ => rfl)

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalFeatureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function

noncomputable def scaledRowsProgram : PolyProgram eqd em scaledRows := by
  let dim := fst es (encodePair el eqm)
  let rest := snd es (encodePair el eqm)
  let rows := rest.comp (snd el eqm)
  let law := rest.comp (fst el eqm)
  let cols := (dim.fanout rows).comp (MatrixList.transposeProgram Ratio.encode Gaussian.ListOperation.eu 0 ())
  let icols := cols.comp (IntegerList.numeratorsProgram.listMap [])
  let nums := law.comp (snd Signed.encode er)
  exact ((nums.fanout icols).comp (MatrixList.transposeProgram Signed.encode Signed.encode 0 0)).congr _ (fun _ => rfl)

noncomputable def integerInputProgram : PolyProgram RationalInput.encode Input.encode RationalInput.integer := by
  let dim := fst es (encodePair el eqm)
  let law := (snd es (encodePair el eqm)).comp (fst el eqm)
  let p := dim.fanout (law.fanout scaledRowsProgram)
  exact p.recode RationalInput.raw (fun _ => rfl) (fun I => by
    change ed (List.replicate I.d (), (I.lawData, scaledRows I.raw))=_
    rw [scaledRows_raw]
    rfl)
end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionBinaryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Polynomial

noncomputable def iterateProgram : PolyProgram Input.encode Input.encode
    (fun I => Input.step^[I.n] I) :=
  stepProgram.repeatFrom (identity Input.encode) countProgram X statePolynomial
    (fun I => by simpa using (input_bounds I).1) (fun I i hi => state_size I i hi)

noncomputable def compressProgram : PolyProgram Input.encode el Input.compressed :=
  (iterateProgram.comp lawProgram).congr _ (fun I => by
    simp only [Function.comp_apply,input_iterate,Input.lawData,Input.compressed,compressSteps_eq_iterate])

noncomputable def rationalCompressProgram : PolyProgram RationalInput.encode el RationalInput.compressed :=
  (integerInputProgram.comp compressProgram).congr _ (fun _ => rfl)

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseListTrim
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}
abbrev encode (ea : α → List Bool) (μ : SparseIntegerLaw α) := ed ea (raw μ)

noncomputable def activeProgram (ea : α → List Bool) (a0 : α) :
    PolyProgram (ed ea) (encodeList (encodePair Signed.encode ea)) activeEntries := by
  let l := fst el (encodeList ea)
  let nums := l.comp (snd Signed.encode er)
  let s := snd el (encodeList ea)
  let test := ((((fst Signed.encode ea).fanout (constant (encodePair Signed.encode ea) Signed.encode 0)).comp intEQ).comp boolNot)
  exact (((nums.fanout s).comp (listZip Signed.encode ea 0 a0)).comp (test.listFilter (0,a0))).congr _ (fun x => by
    simp only [Function.comp_def,activeEntries,decide_not])

noncomputable def trimDataProgram (ea : α → List Bool) (a0 : α) :
    PolyProgram (ed ea) (ed ea) trimData := by
  let zs := activeProgram ea a0
  let nums := zs.comp ((fst Signed.encode ea).listMap (0,a0))
  let states := zs.comp ((snd Signed.encode ea).listMap (0,a0))
  let den := (fst el (encodeList ea)).comp (fst Signed.encode er)
  exact ((den.fanout nums).fanout states).congr _ (fun _ => rfl)

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingUniformStep
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly

theorem dimensions_list {n : ℕ} (β : Fin n → ℚ) :
    dimensions (List.ofFn β)=List.replicate (n+n*n) () := by
  simp only [dimensions,indices,square,List.length_ofFn]
  simp

theorem features_list {n : ℕ} (p : Vector ℚ n) :
    features p.toList=List.ofFn (SparseWeightedPartial.features p) := by
  have hp : p.toList=List.ofFn (RationalWeightedStep.point p) := by
    apply List.ext_getElem <;> intros <;> simp [RationalWeightedStep.point]
  simp only [features,hp,List.flatMap_def,List.map_ofFn,Function.comp_def,ofFn_product]
  rw [List.ofFn_add]
  congr 1
  · congr 1; funext i
    have hi : (Fin.castAdd (n*n) i : Fin (n+n*n))=finSumFinEquiv (Sum.inl i) := by rfl
    change _=SparseWeightedPartial.features p (Fin.castAdd (n*n) i)
    rw [hi,SparseWeightedPartial.features_single]
  · congr 1; funext i
    have hi : (Fin.natAdd n i : Fin (n+n*n))=finSumFinEquiv (Sum.inr i) := by
      apply Fin.ext; simp [finSumFinEquiv]
    rw [hi]
    simp only [SparseWeightedPartial.features,Equiv.symm_apply_apply,Sum.elim_inr]

end MetricKMedian.RoundingList

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

def State.encode {s : Bool} (x : State s) : List Bool :=
  encodePair erow (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList)) (List.ofFn x.β,x.μ)
def State.raw {s : Bool} (x : State s) : Row × Data Row :=
  (List.ofFn x.β,((x.μ.law.denominator,List.ofFn x.μ.law.numerator),x.μ.states.toList.map Vector.toList))

theorem State.encode_raw {s : Bool} (x : State s) :
    encodePair erow (ed erow) x.raw=x.encode := by
  simp only [State.raw,State.encode,SparseIntegerLaw.BinarySparse.encode,
    SparseIntegerLaw.BinarySparse.raw,ed,encodePair,encodeList_map]

def probability (s : Bool) : Row × Row → ℚ :=
  if s then fun x => RoundingList.Signed.probability x.1 x.2 else fun x => RoundingList.probability x.1 x.2
def endpoint (s b : Bool) : Row × Row → Row :=
  if s then fun x => RoundingList.Signed.endpoint x.1 x.2 b else fun x => RoundingList.endpoint x.1 x.2 b

noncomputable def probabilityProgram (s : Bool) : PolyProgram (encodePair erow erow) Ratio.encode (probability s) := by
  cases s
  · exact RoundingList.probability_poly.program
  · exact RoundingList.Signed.probability_poly.program
noncomputable def endpointProgram (s b : Bool) : PolyProgram (encodePair erow erow) erow (endpoint s b) := by
  cases s
  · exact (RoundingList.endpoint_poly b).program
  · exact (RoundingList.Signed.endpoint_poly b).program

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalCodes
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

def sets (S : Finset I) : Row := setView (S.map r.symm.toEquiv.toEmbedding)

 theorem sets_eq (S : Finset I) : sets r S=List.ofFn (fun i => decide (r i∈S)) := by
  simp only [sets,setView,mem_map_equiv]
  rfl
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseIterationHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.SparseIntegerLaw
open Binary
variable {α : Type} {d : ℕ}

theorem encode_length_bound (ea : α → List Bool) (μ : SparseIntegerLaw α) (N H A : ℕ)
    (hn : μ.length≤N) (hd : μ.law.denominator≤(2:ℤ)^H)
    (ha : ∀ i : Fin μ.length, (ea μ.states[i.val]).length≤A) :
    (BinarySparse.encode ea μ).length≤2*(2*(H+4)+1+N*(2*(H+4)+1))+1+N*(2*A+1) := by
  have hd' := Binary.Signed.length_height (by rwa [abs_of_pos μ.law.denominator_pos] : |μ.law.denominator|≤(2:ℤ)^H)
  have hn' : (Binary.encodeList Binary.Signed.encode (List.ofFn μ.law.numerator)).length≤N*(2*(H+4)+1) := by
    apply (Binary.EncodedList.length_bound _ _ (H+4) ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*(H+4)+1) hn
    · intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact Binary.Signed.length_height (by rw [abs_of_nonneg (μ.law.numerator_nonneg i)]; exact (μ.law.numerator_le i).trans hd)
  have hs : (Binary.encodeList ea μ.states.toList).length≤N*(2*A+1) := by
    rw [BinarySparse.states_list]
    apply (Binary.EncodedList.length_bound _ _ A ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*A+1) hn
    · intro a hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ha i
  simp only [BinarySparse.encode,BinarySparse.ed,BinarySparse.raw,BinarySparse.el,IntegerLaw.ListPivot.el,Binary.encodePair_length]
  change 2*(2*(Binary.Signed.encode μ.law.denominator).length+1+
    (Binary.encodeList Binary.Signed.encode (List.ofFn μ.law.numerator)).length)+1+
    (Binary.encodeList ea μ.states.toList).length≤_
  omega

end MetricKMedian.SparseIntegerLaw
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingStateCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

def vectorData {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n)) : Data Row :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)

theorem vectorData_branch {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n))
    (p : Vector ℚ n → ℚ) (hp : ∀ q, 0≤p q ∧ p q≤1) (next : Vector ℚ n → Fin 2 → Vector ℚ n)
    (P : Row → ℚ) (E0 E1 : Row → Row)
    (hP : ∀ q, P q.toList=p q) (hE0 : ∀ q, E0 q.toList=(next q 0).toList)
    (hE1 : ∀ q, E1 q.toList=(next q 1).toList) :
    (branchLawData ((vectorData μ).1,(vectorData μ).2.map P),
      (vectorData μ).2.flatMap (fun q => [E0 q,E1 q]))=vectorData (μ.branch p hp next) := by
  simp only [vectorData,states_list,List.map_ofFn,Function.comp_def,hP]
  rw [branchLaw_ofFn μ.law _ (fun i => hp μ.states[i.val])]
  congr 1
  simp only [SparseIntegerLaw.branch,Vector.getElem_ofFn,List.flatMap_def,List.map_ofFn,Function.comp_def,hE0,hE1]
  exact (two_expand (fun i b => (next μ.states[i.val] b).toList)).symm

theorem branch_raw (s : Bool) (x : State s) :
    (x.raw.1,(branchLawData (x.raw.2.1,x.raw.2.2.map (fun p => probability s (x.raw.1,p))),
      x.raw.2.2.flatMap (fun p => [endpoint s false (x.raw.1,p),endpoint s true (x.raw.1,p)])))=
       x.branch.raw := by
  cases s
  · change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData
      (x.μ.branch (RationalWeightedStep.probability x.β)
        (RationalWeightedStep.probability_unit x.β (x.positive rfl)) (RationalWeightedStep.endpoint x.β)))
    apply congrArg (fun d => (List.ofFn x.β,d))
    exact vectorData_branch x.μ _ _ _ (RoundingList.probability (List.ofFn x.β))
      (fun p => RoundingList.endpoint (List.ofFn x.β) p false)
      (fun p => RoundingList.endpoint (List.ofFn x.β) p true)
      (RoundingList.probability_list x.β)
      (fun p => RoundingList.endpoint_list x.β p 0) (fun p => RoundingList.endpoint_list x.β p 1)
  · change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData
      (x.μ.branch (RationalSignedStep.probability x.β)
        (RationalSignedStep.probability_unit x.β) (RationalSignedStep.endpoint x.β)))
    apply congrArg (fun d => (List.ofFn x.β,d))
    exact vectorData_branch x.μ _ _ _ (RoundingList.Signed.probability (List.ofFn x.β))
      (fun p => RoundingList.Signed.endpoint (List.ofFn x.β) p false)
      (fun p => RoundingList.Signed.endpoint (List.ofFn x.β) p true)
      (RoundingList.Signed.probability_list x.β)
      (fun p => RoundingList.Signed.endpoint_list x.β p 0) (fun p => RoundingList.Signed.endpoint_list x.β p 1)

noncomputable def compressionInputProgram (s : Bool) :
    PolyProgram State.encode IntegerLaw.BinaryCompression.RationalInput.encode (@State.compressionInput s) := by
  let β := fst erow (ed erow)
  let law := (snd erow (ed erow)).comp (fst el (encodeList erow))
  let states := (snd erow (ed erow)).comp (snd el (encodeList erow))
  let dims := β.comp RoundingList.dimensions_poly.program
  let feats := states.comp (RoundingList.features_poly.program.listMap [])
  let work := dims.fanout (law.fanout feats)
  exact work.recode State.raw State.encode_raw (fun x => by
    change IntegerLaw.BinaryCompression.eqd
      (RoundingList.dimensions (List.ofFn x.β),
       ((x.μ.law.denominator,List.ofFn x.μ.law.numerator),
        (x.μ.states.toList.map Vector.toList).map RoundingList.features))=_
    simp only [RoundingList.dimensions_list,states_list,List.map_ofFn,Function.comp_def,RoundingList.features_list]
    rfl)

noncomputable def statesProgram (s : Bool) :
    PolyProgram State.encode (encodeList erow) (fun x : State s => x.μ.states.toList.map Vector.toList) :=
  ((snd erow (ed erow)).comp (snd el (encodeList erow))).recode State.raw State.encode_raw (fun _ => rfl)
noncomputable def weightsProgram (s : Bool) :
    PolyProgram State.encode erow (fun x : State s => List.ofFn x.β) :=
  (fst erow (ed erow)).recode State.raw State.encode_raw (fun _ => rfl)

noncomputable def compressProgram (s : Bool) : PolyProgram State.encode State.encode (@State.compress s) := by
  let law := (compressionInputProgram s).comp IntegerLaw.BinaryCompression.rationalCompressProgram
  let trimmed := (law.fanout (statesProgram s)).comp (trimDataProgram erow [])
  let work := (weightsProgram s).fanout trimmed
  exact work.recode id (fun _ => rfl) (fun x => by
    change encodePair erow (ed erow) (List.ofFn x.β,
      trimData (((x.μ.law.compressAuto (fun i => SparseWeightedPartial.features x.μ.states[i.val])).denominator,
       List.ofFn (x.μ.law.compressAuto (fun i => SparseWeightedPartial.features x.μ.states[i.val])).numerator),
         x.μ.states.toList.map Vector.toList))=_
    rw [show trimData _= _ from trim_encode_raw
      (⟨x.μ.length,x.μ.states,x.μ.law.compressAuto (fun i => SparseWeightedPartial.features x.μ.states[i.val])⟩ : SparseIntegerLaw (Vector ℚ x.n))]
    exact State.encode_raw x.compress)

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

def Input.raw {s : Bool} (x : Input s) : Row × Row := (List.ofFn x.β,x.p.toList)
abbrev Input.encode {s : Bool} (x : Input s) := encodePair erow erow x.raw

noncomputable def startProgram (s : Bool) : PolyProgram Input.encode State.encode (@Input.start s) := by
  let β := fst erow erow
  let p := snd erow erow
  let law := constant (encodePair erow erow) el ((1:ℤ),[(1:ℤ)])
  let ps := (p.fanout (constant (encodePair erow erow) (encodeList erow) [])).comp (listCons erow)
  let work := β.fanout (law.fanout ps)
  exact work.recode Input.raw (fun _ => rfl) (fun x => by
    change encodePair erow (ed erow) (List.ofFn x.β,((1,[1]),[x.p.toList]))=_
    rw [← State.encode_raw]
    rfl)

noncomputable def countProgram (s : Bool) : PolyProgram Input.encode Nat.bits (@Input.n s) :=
  ((fst erow erow).comp (listLength Ratio.encode 0)).recode Input.raw (fun _ => rfl)
    (fun x => by simp only [Function.comp_def,Input.raw,List.length_ofFn])

theorem input_bounds {s : Bool} (x : Input s) :
    x.n ≤ x.encode.length ∧ (erow (List.ofFn x.β)).length ≤ x.encode.length ∧
      (∀ i, HasHeight (x.β i) x.encode.length) ∧
      ∀ i, HasHeight (RationalWeightedStep.point x.p i) x.encode.length := by
  have he : x.encode.length=2*(erow (List.ofFn x.β)).length+1+(erow x.p.toList).length := by
    simp only [Input.encode,Input.raw,encodePair_length]
  have hn := EncodedList.length_le Ratio.encode (List.ofFn x.β)
  change (List.ofFn x.β).length ≤ (erow (List.ofFn x.β)).length at hn
  simp only [List.length_ofFn] at hn
  refine ⟨by omega,by omega,?_,?_⟩
  · intro i
    exact (Ratio.height_length _).mono ((EncodedList.member_length Ratio.encode _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).trans (by change (erow (List.ofFn x.β)).length ≤ x.encode.length; omega))
  · intro i
    have hm : RationalWeightedStep.point x.p i∈x.p.toList := by
      exact List.mem_iff_getElem.mpr ⟨i.val,by simp,by simp [RationalWeightedStep.point]⟩
    exact (Ratio.height_length _).mono ((EncodedList.member_length Ratio.encode _ _ hm).trans (by change (erow x.p.toList).length ≤ x.encode.length; omega))

 theorem run_size {s : Bool} (x : Input s) (t : ℕ) (ht : t ≤ x.n) :
    (State.encode (x.run t)).length ≤ statePolynomial.eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hβ,hb,hp⟩ := input_bounds x
  have hH : RoundingHeight.stepHeight x.n L*t ≤ heightBound L := by
    unfold heightBound RoundingHeight.stepHeight SparseIntegerLaw.stepHeight
    gcongr
    exact ht.trans hn
  have hC : 2*x.n*L+L ≤ coordinateBound L := by unfold coordinateBound; gcongr
  have hN : x.n+x.n*x.n+1 ≤ supportBound L := by unfold supportBound; gcongr
  have hrow (p : Vector ℚ x.n) (hp : ∀ i, HasHeight (RationalWeightedStep.point p i) (2*x.n*L+L)) :
      (erow p.toList).length  ≤  L*(2*(3*coordinateBound L+10)+1) := by
    apply (EncodedList.length_bound Ratio.encode p.toList (3*coordinateBound L+10) ?_).trans
    · simpa only [Vector.length_toList] using Nat.mul_le_mul_right (2*(3*coordinateBound L+10)+1) hn
    · intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
      have hh := hp ⟨i,by simpa only [Vector.length_toList] using hi⟩
      exact Ratio.length_height (hh.mono hC)
  have hsize : (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length ≤ 
      2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
      supportBound L*(2*(L*(2*(3*coordinateBound L+10)+1))+1) := by
    cases s
    · apply SparseIntegerLaw.encode_length_bound _ _ (supportBound L) (heightBound L) _
      · exact (SparseWeightedPartial.run_length x.β (x.positive rfl) x.p t).trans hN
      · exact (RoundingHeight.weighted_denominator x.β (x.positive rfl) x.p L t hb hp x.feasible).trans
          (pow_le_pow_right₀ (by norm_num) hH)
      · intro i; exact hrow _ (RoundingHeight.weighted_run x.β (x.positive rfl) x.p L t hb hp x.feasible i)
    · apply SparseIntegerLaw.encode_length_bound _ _ (supportBound L) (heightBound L) _
      · exact (SparseSignedPartial.run_length x.β x.p t).trans hN
      · exact (RoundingHeight.signed_denominator x.β x.p L t hb hp x.feasible).trans
          (pow_le_pow_right₀ (by norm_num) hH)
      · intro i; exact hrow _ (RoundingHeight.signed_run x.β x.p L t hb hp x.feasible i)
  rw [statePolynomial_eval]
  have he : (State.encode (x.run t)).length = 2*(erow (List.ofFn x.β)).length+1+
      (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length := by
    exact encodePair_length _ _ _
  rw [he]
  change 2*(erow (List.ofFn x.β)).length+1+
    (SparseIntegerLaw.BinarySparse.encode (fun p => erow p.toList) (x.run t).μ).length ≤ stateBound L
  unfold stateBound
  omega

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

def Bundle.encode (x : Bundle T) : List Bool := encodePair ec (ed ea) (x.raw view)

end MetricKMedian.SparseIntegerLaw.DependentProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
abbrev InputRaw := List Unit × List (Data Row)
abbrev ei : InputRaw → List Bool := Binary.Automatic.enc

def columnRaw {n : ℕ} (μ : SparseIntegerLaw (Finset (Fin n))) : Data Row :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map ListOperation.setView)
def Input.raw (x : Input) : InputRaw := (List.replicate x.n (),List.ofFn fun i => columnRaw (x.columns i))
abbrev Input.encode (x : Input) := ei x.raw
def Context.raw (c : Context) : InputRaw × ℕ := (c.input.raw,c.t)
abbrev Context.encode (c : Context) := encodePair ei Nat.bits c.raw
abbrev view (c : Context) (G : T c) := ListOperation.view G
abbrev State.encode := Bundle.encode Context.encode et view

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_CardinalRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
def result (x : Input) : Data (List Bool) :=
  SparseGraph.Program.columnRaw ((round (Vector.ofFn x.p)).map selected)

noncomputable def inputProgram : PolyProgram encodeInput RoundingProgram.Input.encode weightedInput := by
  have hm : Binary.Automatic.Poly (fun q : List ℚ => q.map (fun _ => (1:ℚ))) := by
    apply Binary.Automatic.Poly.list_map <;> fun_prop
  let p : PolyProgram qr (encodePair qr qr) (fun q : List ℚ => (q.map (fun _ => (1:ℚ)),q)) :=
    Binary.Automatic.Poly.program (by fun_prop)
  exact p.recode (fun x => List.ofFn x.p) (fun _ => rfl) (fun x => by
    simp only [List.map_const',List.length_ofFn,RoundingProgram.Input.encode,
      RoundingProgram.Input.raw,weightedInput,List.ofFn_const,Vector.toList_ofFn])

end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
local notation "erB" => ListOperation.er

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  let raw : PolyProgram ei (encodePair (encodePair ei Nat.bits) (ed et))
      (fun x : InputRaw => ((x,0),(((1:ℤ),[(1:ℤ)]),[x.2.map (fun _ => x.1.map (fun _ => false))]))) := by
    apply Binary.Automatic.Poly.program
    have hs : Binary.Automatic.Poly (fun x : InputRaw => x.2.map (fun _ => x.1.map (fun _ => false))) := by
      apply Binary.Automatic.Poly.list_map
      · apply Binary.Automatic.Poly.list_map <;> fun_prop
      · fun_prop
    fun_prop
  exact raw.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.start,SparseIntegerLaw.dirac,
      List.map_const',Input.raw,List.length_ofFn,List.map_replicate,
      Vector.toList_replicate,List.ofFn_const,view,ListOperation.view,Finset.notMem_empty,decide_false]
    rfl)

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.m :=
  ((snd (encodeList (fun _ : Unit => [])) (encodeList (ed erB))).comp (listLength (ed erB) ((1,[1]),[]))).recode
    Input.raw (fun _ => rfl) (fun x => by simp only [Function.comp_def,Input.raw,List.length_ofFn])

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphLawProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram
def QInput.result (x : QInput) : Data ListOperation.Table :=
  (((SparseGraph.law x.q).law.denominator,List.ofFn (SparseGraph.law x.q).law.numerator),
    (SparseGraph.law x.q).states.toList.map ListOperation.view)

end MetricKMedian.SparseGraph.Program
end

end OAI
end


