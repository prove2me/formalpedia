-- Prove2me | Definitions.Def_OAIQ035K048
-- name    : OAIQ035K048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:08:04.872622+00:00
-- url     : https://prove2.me/theorems/9a46ab39-2f08-433e-9217-a0cb2fa029ed
-- title:
--   Definitions bundle OAIQ035K048 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 62 declarations of OpenAI's Lean: 48 definitions and 14 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.IntegerProgram.rationalProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.basisProgram`, `OAI.MetricKMedian.InstanceProgram.lpInput`, `OAI.MetricKMedian.IntegerLaw.ListOperation.entriesProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.positiveProgram`, `OAI.MetricKMedian.IntegerLaw.ListPivot.ratioProgram`, `OAI.MetricKMedian.LPBinary.Nearest.beforeProgram`, `OAI.MetricKMedian.LPBinary.Nearest.entriesProgram`, `OAI.MetricKMedian.LPBinary.Program.positivePart`, `OAI.MetricKMedian.LPBinary.Repair.finish`, `OAI.MetricKMedian.LPBinary.Repair.raw`, `OAI.MetricKMedian.LPBinary.Scale.candidate`, `OAI.MetricKMedian.LPBinary.Scale.feasible`, `OAI.MetricKMedian.LPBinary.Scale.selected`, `OAI.MetricKMedian.LPBinary.Scale.selectedScale`, `OAI.MetricKMedian.LPBinary.result`, `OAI.MetricKMedian.LPBinary.states`, `OAI.MetricKMedian.RationalSignedTerminal.terminal`, `OAI.MetricKMedian.RoundingProgram.State.compressionInput`, `OAI.MetricKMedian.SparseBernoulli.Program.State.encode`, `OAI.MetricKMedian.SparseBernoulli.Program.countProgram`, `OAI.MetricKMedian.SparseBundles.law`, `OAI.MetricKMedian.SparseCounts.run`, `OAI.MetricKMedian.SparseCounts.step`, `OAI.MetricKMedian.SparseGraph.Program.State.increment`, `OAI.MetricKMedian.SparseGraph.Program.State.product`, `OAI.MetricKMedian.SparseGraph.Program.State.step`, `OAI.MetricKMedian.SparseGraph.Program.column`, `OAI.MetricKMedian.SparseGraph.Program.columnsProgram`, `OAI.MetricKMedian.SparseGraph.Program.update`, `OAI.MetricKMedian.SparseGridRounding.law`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle.branch`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle.compress`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.Bundle.compressionInput`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.compressionInputProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.contextProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.lawProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.statesProgram`, `OAI.MetricKMedian.SparseIntegerLaw.bindCompress`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.Input.bern` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineListCompiler`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_FractionalSelectProgram`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPBinaryTrajectory`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Optimization_ZeroCostBranch`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Sparse_SparseBernoulliSupport`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseBundleLaw`, `KMedian_Sparse_SparseCountFeatures`, `KMedian_Sparse_SparseCountRun`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparseListTrim`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseRescaledInner`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseStarActivation`, `KMedian_Sparse_SparseSupport`, `KMedian_Sparse_SparseTargetSubset`, `KMedian_Sparse_SparseWeightedRounding`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K038`, `OAIQ035K039`, `OAIQ035K040`, `OAIQ035K041`, `OAIQ035K042` and `OAIQ035K043` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K052` and `OAIQ035K053`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K038
import Definitions.Def_OAIQ035K039
import Definitions.Def_OAIQ035K040
import Definitions.Def_OAIQ035K041
import Definitions.Def_OAIQ035K042
import Definitions.Def_OAIQ035K043

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListCompiler
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerKernelProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineListCompiler
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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SimplexListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

namespace Program
open Binary Binary.PolyProgram
noncomputable def positivePart : PolyProgram Ratio.encode Ratio.encode (fun q => max 0 q) :=
  (((constant Ratio.encode Ratio.encode 0).fanout (identity Ratio.encode)).comp ratMax).congr _ (fun _ => rfl)
end Program
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function

theorem start_eq (r : ℕ) (I : Input) : start r I=(rawContext r I.raw,I.iterate r 0) := by
  unfold start
  congr 1
  simp only [rawInitial,Input.raw,Input.rows,head_ofFn,List.length_ofFn,range_ofFn,List.map_ofFn,Input.iterate,Input.vector,ProjectedSubgradient.trajectory_zero]
  congr 1
  funext i
  simp only [ProjectedSubgradient.initial,ProjectedSubgradient.point_ofFn_apply]
  simp only [Fin.ext_iff,Function.comp_apply,Fin.val_zero]

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryTrajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Polynomial Function

def states (r : ℕ) (I : Input) : List State := Iteration.iterates update (start r I) (rawSteps r I.raw)
def result (r : ℕ) (I : Input) : Row := (choose (states r I)).2

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest

noncomputable def entriesProgram : PolyProgram (encodePair er er) ees (fun x : Row × Row => entries x.1 x.2) := by
  let ez := encodePair Ratio.encode Ratio.encode
  let zip := listZip Ratio.encode Ratio.encode 0 0
  let ids := listIndices ez (0,0)
  exact (zip.comp ((ids.fanout (identity (encodeList ez))).comp (listZip Nat.bits ez 0 (0,0)))).congr _ (fun _ => rfl)
noncomputable def beforeProgram : PolyProgram (encodePair ee ee) encodeBool (fun x : Entry × Entry => before x.1 x.2) := by
  let a := fst ee ee
  let b := snd ee ee
  let idx := fst Nat.bits (encodePair Ratio.encode Ratio.encode)
  let dist := (snd Nat.bits (encodePair Ratio.encode Ratio.encode)).comp (snd Ratio.encode Ratio.encode)
  let dst := (a.comp dist).fanout (b.comp dist)
  let ilt := ((a.comp idx).fanout (b.comp idx)).comp natLT
  exact (((dst.comp ratLT).fanout (((dst.comp ratEQ).fanout ilt).comp boolAnd)).comp boolOr).congr _ (fun _ => by simp only [Function.comp_apply,before,Bool.decide_or,Bool.decide_and])
end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
def finish (ds : Rows) (ys : Row) (H ρ : ℚ) : Output :=
  (opening ys ρ,assignments ds (nearestRows (Truncated.matrix ds H) ys))
def raw (r : ℕ) (I : Input) : Output := finish I.rows (result r I) (rawPenalty r I.raw) (TruncatedLP.loss r I.k)

theorem assignments_ofFn {n m : ℕ} (d x : Fin m → Fin n → ℚ) :
    assignments (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn (fun j => List.ofFn (x j)))=
      List.ofFn (fun j => List.ofFn (TruncatedLP.repairedAssignment d x j)) := by
  simp only [assignments,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,assignment,weights_ofFn,List.sum_ofFn]
  rfl

end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalSelectProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ZeroCostBranch
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
-- module Solutions.OAIQ035_KM.KMedian_Programs_PivotListProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseListTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}

theorem activeEntries_raw (μ : SparseIntegerLaw α) : activeEntries (raw μ)=
    List.ofFn (fun j : Fin μ.law.support.card => let i := μ.law.support.orderEmbOfFin rfl j;
      (μ.law.numerator i,μ.states[i.val])) := by
  rw [activeEntries,raw,states_list,Gaussian.ListOperation.zip_ofFn,List.ofFn_eq_map,List.filter_map]
  exact EncodingLists.map_filter_enum _ (fun i => μ.law.numerator i≠0)

theorem trimData_raw (μ : SparseIntegerLaw α) : trimData (raw μ)=raw μ.trim := by
  unfold trimData
  rw [activeEntries_raw]
  simp only [raw,trim,Vector.toList_ofFn,List.map_ofFn,Function.comp_def,IntegerLaw.trim_denominator]
  congr 2
  exact congrArg List.ofFn (funext (IntegerLaw.trim_numerator μ.law)).symm

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RationalFeatureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function

theorem scaledRows_raw (I : RationalInput) : scaledRows I.raw=
    List.ofFn (fun i => List.ofFn (RationalLaw.scaledFeatures I.v i)) := by
  unfold scaledRows RationalInput.raw RationalInput.features RationalInput.lawData
  rw [MatrixList.transpose_ofFn _ _ (List.length_replicate ..)]
  simp only [List.map_ofFn,Function.comp_def,IntegerList.numerators_ofFn]
  rw [MatrixList.transpose_ofFn _ _ (List.length_ofFn ..)]
  congr 1
  funext i
  congr 1
  funext j
  exact (RationalLaw.scaledFeatures_eq I.v i j).symm

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

def State.compressionInput {s : Bool} (x : State s) : IntegerLaw.BinaryCompression.RationalInput :=
  ⟨x.μ.length,x.n+x.n*x.n,x.μ.law,fun i => SparseWeightedPartial.features x.μ.states[i.val]⟩

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingStateCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

theorem trim_encode_raw {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n)) :
    trimData ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)=
      (((μ.trim).law.denominator,List.ofFn (μ.trim).law.numerator),μ.trim.states.toList.map Vector.toList) := by
  change trimData ((raw μ).1,(raw μ).2.map Vector.toList)=_
  rw [trimData_map,trimData_raw]
  rfl

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_DependentSparseProgram
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

def Bundle.branch (p : ∀ c, T c → ℚ) (hp : ∀ c a, 0 ≤ p c a ∧ p c a ≤ 1)
    (next : ∀ c, T c → Fin 2 → T c) (x : Bundle T) : Bundle T :=
  ⟨x.ctx,x.law.branch (p x.ctx) (hp x.ctx) (next x.ctx)⟩
def Bundle.compress (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ) (x : Bundle T) : Bundle T :=
  ⟨x.ctx,x.law.compressAuto (v x.ctx)⟩
def Bundle.compressionInput (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ) (x : Bundle T) :
    IntegerLaw.BinaryCompression.RationalInput :=
  ⟨x.law.length,d x.ctx,x.law.law,fun i => v x.ctx x.law.states[i.val]⟩

 theorem trim_view (c : C) (μ : SparseIntegerLaw (T c)) :
    trimData ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map (view c))=
      (((μ.trim).law.denominator,List.ofFn (μ.trim).law.numerator),μ.trim.states.toList.map (view c)) := by
  change trimData ((raw μ).1,(raw μ).2.map (view c))=_
  rw [RoundingProgram.trimData_map,trimData_raw]
  rfl

noncomputable def contextProgram : PolyProgram (Bundle.encode ec ea view) ec (fun x : Bundle T => x.ctx) :=
  (fst ec (ed ea)).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
noncomputable def statesProgram : PolyProgram (Bundle.encode ec ea view) (encodeList ea)
    (fun x : Bundle T => x.law.states.toList.map (view x.ctx)) :=
  ((snd ec (ed ea)).comp (snd el (encodeList ea))).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
noncomputable def lawProgram : PolyProgram (Bundle.encode ec ea view) el
    (fun x : Bundle T => (x.law.law.denominator,List.ofFn x.law.law.numerator)) :=
  ((snd ec (ed ea)).comp (fst el (encodeList ea))).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)

noncomputable def compressionInputProgram (a0 : A) (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ)
    (F : C × A → List ℚ) (hF : ∀ c a, F (c,view c a)=List.ofFn (v c a))
    (D : PolyProgram ec IntegerLaw.BinaryCompression.es (fun c => List.replicate (d c) ()))
    (V : PolyProgram (encodePair ec ea) IntegerLaw.BinaryCompression.eqr F) :
    PolyProgram (Bundle.encode ec ea view) IntegerLaw.BinaryCompression.RationalInput.encode
      (Bundle.compressionInput d v) := by
  let ctx := contextProgram ec ea view
  let rows := (ctx.fanout (statesProgram ec ea view)).comp (V.listMapWith a0 [])
  let work := (ctx.comp D).fanout ((lawProgram ec ea view).fanout rows)
  exact work.recode id (fun _ => rfl) (fun x => by
    change IntegerLaw.BinaryCompression.eqd (List.replicate (d x.ctx) (),
      ((x.law.law.denominator,List.ofFn x.law.law.numerator),
        (x.law.states.toList.map (view x.ctx)).map (fun a => F (x.ctx,a))))=_
    simp only [states_list,List.map_ofFn,Function.comp_def,hF]
    rfl)

 theorem raw_branch (p : ∀ c, T c → ℚ) (hp : ∀ c a, 0 ≤ p c a ∧ p c a ≤ 1)
    (next : ∀ c, T c → Fin 2 → T c)
    (P : C × A → ℚ) (E0 E1 : C × A → A)
    (hP : ∀ c a, P (c,view c a)=p c a)
    (hE0 : ∀ c a, E0 (c,view c a)=view c (next c a 0))
    (hE1 : ∀ c a, E1 (c,view c a)=view c (next c a 1)) (x : Bundle T) :
    (x.ctx,(branchLawData ((x.raw view).2.1,(x.raw view).2.2.map (fun a => P (x.ctx,a))),
      (x.raw view).2.2.flatMap (fun a => [E0 (x.ctx,a),E1 (x.ctx,a)])))=
       (x.branch p hp next).raw view := by
  simp only [Bundle.raw,Bundle.branch,states_list,List.map_ofFn,Function.comp_def,hP]
  rw [branchLaw_ofFn x.law.law _ (fun i => hp x.ctx x.law.states[i.val])]
  congr 2
  simp only [SparseIntegerLaw.branch,Vector.getElem_ofFn,List.flatMap_def,List.map_ofFn,
    Function.comp_def,hE0,hE1]
  exact (two_expand (fun i b => view x.ctx (next x.ctx x.law.states[i.val] b))).symm

end MetricKMedian.SparseIntegerLaw.DependentProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram
abbrev State.encode := Bundle.encode Context.encode er view

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram
open SparseIntegerLaw.BinarySparse (el ed)

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n :=
  (listLength Ratio.encode 0).recode (fun x => List.ofFn x.p) (fun _ => rfl) (fun x => by simp only [List.length_ofFn])

 theorem input_bounds (x : Input) : x.n ≤ x.encode.length ∧ ∀ i, HasHeight (x.p i) x.encode.length := by
  refine ⟨?_,?_⟩
  · simpa only [List.length_ofFn] using (EncodedList.length_le Ratio.encode (List.ofFn x.p))
  · intro i
    exact (Ratio.height_length _).mono (EncodedList.member_length _ _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩))

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

def bindCompress {d : ℕ} (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (v : β → Fin d → ℚ) : SparseIntegerLaw β :=
  (μ.bindIndexed κ).compressAuto v

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBindProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly Finset

variable {α β A : Type}

 theorem jointWeights_raw (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (view : β → A) :
    jointWeights ((raw μ).1,List.ofFn (fun i => ((raw (κ i)).1,(κ i).states.toList.map view)))=
      List.ofFn (fun j => let z := (finSigmaFinEquiv (n:=fun i => (κ i).length)).symm j;
        μ.law.rational.weight z.1*(κ z.1).law.rational.weight z.2) := by
  simp only [jointWeights,raw,weights_law,Gaussian.ListOperation.zip_ofFn,List.flatMap_def,
    List.map_ofFn,Function.comp_def,weights_law]
  exact ListSigma.ofFn_sigma _

 theorem bindData_raw (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (view : β → A) :
    bindData ((raw μ).1,List.ofFn (fun i => ((raw (κ i)).1,(κ i).states.toList.map view)))=
      ((raw (μ.bindIndexed κ)).1,(μ.bindIndexed κ).states.toList.map view) := by
  unfold bindData
  rw [jointWeights_raw,IntegerList.denominator_ofFn,IntegerList.numerators_ofFn]
  let w := (μ.law.rational.sigma (fun i => (κ i).law.rational)).weight
  change ((RationalScaling.denominator (fun j => w (finSigmaFinEquiv.symm j)),
    List.ofFn (RationalScaling.numerator (fun j => w (finSigmaFinEquiv.symm j)))),_) = _
  rw [scaling_denominator_equiv finSigmaFinEquiv w]
  rw [show RationalScaling.numerator (fun j => w (finSigmaFinEquiv.symm j)) =
    (fun j => RationalScaling.numerator w (finSigmaFinEquiv.symm j)) from
      funext (scaling_numerator_equiv finSigmaFinEquiv w)]
  have hs : (List.ofFn fun i => ((raw (κ i)).1,(κ i).states.toList.map view)).flatMap Prod.snd=
      (μ.bindIndexed κ).states.toList.map view := by
    simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,states_list,List.map_ofFn]
    rw [ListSigma.ofFn_sigma]
    simp only [bindIndexed,Vector.getElem_ofFn]
  rw [hs]
  rfl

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem compressAuto_positive {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ)
    (a : Fin (μ.compressAuto v).length) : 0 < (μ.compressAuto v).law.rational.weight a := by
  exact (⟨μ.length,μ.states,μ.law.compressAuto (fun i => v μ.states[i.val])⟩ :
    SparseIntegerLaw α).trim_positive a

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphStepProgram
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

def column (c : Context) : SparseIntegerLaw (Finset (Fin c.input.n)) :=
  if h : c.t < c.input.m then c.input.columns ⟨c.t,h⟩ else .dirac ∅
def update (c : Context) (G : T c) (S : Finset (Fin c.input.n)) : T c :=
  fun i => if i.val=c.t then S else G i

def State.product (x : State) : State := ⟨x.ctx,x.law.prod (column x.ctx) (update x.ctx)⟩

def State.increment (x : State) : State := ⟨⟨x.ctx.input,x.ctx.t+1⟩,x.law⟩
def State.step (x : State) : State :=
  State.increment (if x.ctx.t<x.ctx.input.m then
    Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m))
      (fun _ => features) x.product else x)

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram

noncomputable def columnsProgram : PolyProgram QInput.encode (encodeList SparseBernoulli.Program.Input.encode) QInput.columns :=
  (snd (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun x => by
    change qt (List.ofFn (fun i => List.ofFn (x.column i).p))=
      encodeList SparseBernoulli.Program.Input.encode (List.ofFn x.column)
    rw [show List.ofFn (fun i => List.ofFn (x.column i).p)=
      (List.ofFn x.column).map (fun c => List.ofFn c.p) by rw [List.map_ofFn]; rfl]
    exact RoundingProgram.encodeList_map qr (fun c : SparseBernoulli.Program.Input => List.ofFn c.p) _)

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountFeatures
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountRun
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
open RationalWeightedStep (point)
variable {n : ℕ}

def law (q : Fin n → ℚ) : SparseIntegerLaw (Fin n → ℕ) :=
  (SparseCardinalRounding.round (fraction q)).map (count q)

end MetricKMedian.SparseGridRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBundleLaw
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRescaledInner
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem run_positive (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) (a : Fin (run (d := d) p hp t).length) :
    0 < (run (d := d) p hp t).law.rational.weight a := by
  induction t with
  | zero =>
    change 0 < (SparseIntegerLaw.dirac (fun _ : Fin n => false)).law.rational.weight a
    change (0:ℚ) < 1/1
    norm_num
  | succ t ih =>
    let inv : SparseIntegerLaw (Fin n → Bool) → Prop := fun μ =>
      ∀ a : Fin μ.length, 0 < μ.law.rational.weight a
    suffices hs : inv (run (d := d) p hp (t+1)) from hs a
    rw [run]
    split_ifs with ht
    · exact ((run (d := d) p hp t).branch (fun _ => p ⟨t,ht⟩)
        (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)).compressAuto_positive _
    · exact ih

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedTerminal
open Finset RationalWeightedStep RationalSignedStep
variable {n : ℕ}

def terminal (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) : SparseIntegerLaw (Vector ℚ n) :=
  (SparseBernoulli.run (d := 2) (point p) hp n).map (state u p)

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseWeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedRounding
open Finset RationalWeightedStep SparseWeightedPartial
variable {n : ℕ}

def round (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) :
    SparseIntegerLaw (Vector ℚ n) :=
  (run β hβ p n).step features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint

end MetricKMedian.SparseWeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTargetSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

def vectors (D : Finset (Fin n)) (q : ℚ) : SparseIntegerLaw (Vector ℚ n) :=
  SparseWeightedRounding.round (fun _ => 1) (fun _ => by norm_num) (initial D q)

def law (D : Finset (Fin n)) (q : ℚ) : SparseIntegerLaw (Finset (Fin n)) :=
  (vectors D q).map SparseCardinalRounding.selected

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseStarActivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

def law (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) :
    SparseIntegerLaw (Fin m → Finset (Fin n)) :=
  SparseGraph.run (fun e => SparseTargetSubset.law (D e) (q e)) m

end MetricKMedian.SparseStarActivation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

def kernel (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) : SparseIntegerLaw (State n m) :=
  (SparseStarActivation.law D (point q)).prod
    (SparseBernoulli.run (d := 2) (point q) hq m) (fun S ω => (q,S,ω))

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePreparedLaw
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

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
def lpInput (I : Nonzero) : LPBinary.Input :=
  ⟨I.val.facilities.card,I.val.clients.card,I.val.k,card_pos.mpr I.val.facilities_nonempty,
    card_pos.mpr (I.val.nonzero_clients I.property),I.val.k_pos,I.val.k_le,I.val.indexedDistance⟩
end MetricKMedian.InstanceProgram
end

end OAI
end


