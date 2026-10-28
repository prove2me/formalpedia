-- Prove2me | Definitions.Def_OAIQ035K059
-- name    : OAIQ035K059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:16:07.802749+00:00
-- url     : https://prove2.me/theorems/c070ba56-d818-4464-80cd-89533b2d6c3d
-- title:
--   Definitions bundle OAIQ035K059 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 47 definitions, 1 inductive type or structure and 35 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.Input`, `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.Input.raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.Input.selection`, `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.Raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.prepare`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.candidates`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.encode`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.result`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.images`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.itemsProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.prepare`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input.encode`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input.result`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input.selection`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.dummy`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.finish`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.prepare`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.valid`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.encode`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.items`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.result`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.attach`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.ctxRaw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.dummy`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.metadata`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.iterateProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.nextLawProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.productiveProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.stepProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.affineKernelProgram`, `OAI.MetricKMedian.IntegerLaw.ListOperation.fullProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.encode`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.raw`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.taperProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.attach`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.nextRaw`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.result`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.view`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.attach`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.ctxEncode` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineListCompiler`, `KMedian_Compression_CompressionBinaryProgram`, `KMedian_Compression_CompressionListStep`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyListEncoding`, `KMedian_Process_CopyNearestProgram`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Process_TaperGraphProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_MaximumProgram`, `KMedian_Programs_NearestMaskProgram`, `KMedian_Rounding_GridDataProgram`.
--
--   **Imports.** It imports the bundles `OAIQ035K054`, `OAIQ035K055` and `OAIQ035K056` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K065` and `OAIQ035K066`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K054
import Definitions.Def_OAIQ035K055
import Definitions.Def_OAIQ035K056

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
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionListStep
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionBinaryProgram
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

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyListEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyList
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {f Δ : ℕ}
 theorem active_view (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    active (view A)=List.ofFn (fun i => (rank (enumeration A i).val).val) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_range _).pairwise.filter _).sortedLT
  · exact (enum_rank_strictMono A).sortedLT_ofFn
  · intro k
    simp only [active,indices,view,setView,List.length_ofFn,List.mem_filter,List.mem_range,List.mem_ofFn]
    constructor
    · rintro ⟨hk,ha⟩
      simp only [List.getElem?_ofFn,dite_eq_left hk,Option.getD_some,decide_eq_true_eq,mem_map_equiv] at ha
      let a : A := ⟨finProdFinEquiv.symm ⟨k,hk⟩,ha⟩
      refine ⟨(enumeration A).symm a,?_⟩
      rw [Equiv.apply_symm_apply]
      change ((finProdFinEquiv (finProdFinEquiv.symm ⟨k,hk⟩)).val)=k
      rw [Equiv.apply_symm_apply]
    · rintro ⟨i,rfl⟩
      refine ⟨(rank (enumeration A i).val).isLt,?_⟩
      simp only [List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq,
        mem_map_equiv,Equiv.symm_apply_apply]
      exact (enumeration A i).property

end MetricKMedian.RationalPhysicalKernel.CopyList
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

noncomputable def statesProgram (s : Bool) :
    PolyProgram State.encode (encodeList erow) (fun x : State s => x.μ.states.toList.map Vector.toList) :=
  ((snd erow (ed erow)).comp (snd el (encodeList erow))).recode State.raw State.encode_raw (fun _ => rfl)

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyGraphProgram
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

def Input.raw (x : Input) : Raw := ((((x.g,x.P),x.Δ),List.ofFn (fun i => List.ofFn (x.d i))),CopyList.view x.A)
abbrev Input.encode (x : Input) := enc x.raw

 theorem prepare_input (x : Input) : prepare x.raw=x.taper.raw := by
  dsimp only [TaperGraphProgram.Input.raw,Input.taper]
  simp only [prepare,Input.raw,active_view,List.map_ofFn,Function.comp_def,rank_owner,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,
    mem_map_equiv,Equiv.symm_symm,own,mem_filter,mem_univ,true_and]
  simp only [Fin.ext_iff]
noncomputable def taperProgram : PolyProgram Input.encode TaperGraphProgram.Input.encode Input.taper :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepare_input x))

 attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.instLinearOrderSubtypeCopyFinMemFinset
theorem reindexed_lift {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ))
    (G : Fin A.card → Finset (Fin A.card)) :
    RationalBatchData.Ordinal.graphView (ordinal A) (SparseEnumeratedGraph.lift (enumeration A) G)=
      SparseGraph.ListOperation.view G := by
  simp only [RationalBatchData.Ordinal.graphView,RationalBatchData.Ordinal.sets_eq,
    SparseGraph.ListOperation.view]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext h
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [SparseEnumeratedGraph.mem_lift]
  change (enumeration A).symm (enumeration A h)∈G ((enumeration A).symm (enumeration A i)) ↔ _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

 local instance instLinearOrderCopyFin_rf7a4cb_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
theorem result_eq (x : Input) : x.taper.qInput.result=x.result := by
  unfold Input.result Input.law graphLaw SparseEnumeratedGraph.law
  simp only [SparseIntegerLaw.map,Vector.toList_map,List.map_map,Function.comp_def,reindexed_lift]
  unfold SparseGraph.Program.QInput.result
  rw [taper_q]
  rfl

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_MaximumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
 theorem radius_view {n : ℕ} (d : Fin n → ℚ) (U : Finset (Fin n)) (hU : U.Nonempty) :
    radius (List.ofFn d,setView U)=(U.image d).max' (hU.image _) :=
  maximum_eq_finset _ _ _ (selectedValues_mem d U)
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_NearestMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Preparation.RationalNearest.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

 theorem erase_view {n : ℕ} (U : Finset (Fin n)) (a : Fin n) : erase (a.val,setView U)=setView (U.erase a) := by
  simp only [erase,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_erase,
    Bool.decide_and]
  simp only [ne_eq,Fin.val_inj]
  exact Bool.and_comm _ _
 theorem insert_view {n : ℕ} (U : Finset (Fin n)) (a : Fin n) : insert (a.val,setView U)=setView (Insert.insert a U) := by
  simp only [insert,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_insert,Fin.ext_iff,
    Bool.decide_or]
  exact Bool.or_comm _ _

 theorem raw_view {n : ℕ} (d : Fin n → ℚ) (U : Finset (Fin n)) (k : ℕ) :
    raw k (List.ofFn d,setView U)=setView (takeNearest d k U) := by
  induction k generalizing U with
  | zero => simp only [raw,takeNearest,setView,List.map_ofFn,Function.comp_def,notMem_empty,decide_false]
  | succ k ih =>
    unfold raw takeNearest
    rw [Completion.Rational.PackingProgram.any_view]
    by_cases h : U.Nonempty
    · simp only [decide_eq_true h,ite_true,dite_eq_left h]
      rw [MetricKMedian.MaskProgram.nearest_view d U h]
      have he : Preparation.firstNearest U d h=least U d h := rfl
      rw [he,erase_view,ih,insert_view]
    · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h,setView,List.map_ofFn,
        Function.comp_def,notMem_empty,decide_false]
end MetricKMedian.Preparation.RationalNearest.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyNearestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open RationalPhysicalKernel RationalPhysicalKernel.CopyList
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (q : RationalParameters τ)
 attribute [local instance] OAI.MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram.instLinearOrderCopyFin
theorem nearestRaw_view {f j : ℕ} (d : Fin j → Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) q.Δ)) (c : Fin j) :
    nearestRaw q.Δ (List.ofFn (d c),view A)=view (q.nearest d A c) := by
  unfold nearestRaw
  rw [distances_view,view,Preparation.RationalNearest.MaskProgram.raw_view]
  exact congrArg setView (Preparation.RationalNearest.takeNearest_map orderEquiv (fun a => d c a.1) q.Δ A)

 theorem radiusRaw_view {f j : ℕ} (d : Fin j → Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) q.Δ))
    (hA : q.Δ≤A.card) (c : Fin j) : radiusRaw q.Δ (List.ofFn (d c),view A)=q.radius d A hA c := by
  unfold radiusRaw
  rw [distances_view,nearestRaw_view q]
  unfold view
  rw [MetricKMedian.MaskProgram.radius_view _ _ ((q.nearest_nonempty d A hA c).map)]
  have he : ((q.nearest d A c).map finProdFinEquiv.toEmbedding).image
      (fun k => d c (finProdFinEquiv.symm k).1)=(q.nearest d A c).image (fun a => d c a.1) := by
    ext r
    simp only [mem_image,mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩; exact ⟨a,ha,by simpa using h⟩
    · rintro ⟨a,ha,rfl⟩; exact ⟨finProdFinEquiv a,⟨a,ha,rfl⟩,by simp⟩
  simp only [he,RationalParameters.radius]
end MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
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
abbrev Input.encode (x : Input) := Binary.Automatic.enc x.raw

end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchUpdateProgram
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

abbrev Raw := (ℕ × Row) × RationalBatchData.GraphData.Raw
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
def Input.raw (x : Input) : Raw := ((x.ctx.Δ,CopyList.view x.ctx.A),x.proposal.raw)

def finish (x : Raw × Data Row) : Data Row :=
  (x.2.1,x.2.2.map (fun Z => CopyNext.transition (x.1.1,((RationalBatchData.GraphData.prepare x.1.2).2,Z))))
@[fun_prop] theorem finish_poly : Poly finish := by
  unfold finish
  apply pair
  · fun_prop
  · apply list_map <;> fun_prop

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalRoundProgram
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
def ctxRaw (x : Context) : Raw := (x.toInput.raw,(x.β,(x.p,x.φ)))
abbrev ctxEncode (x : Context) := enc (ctxRaw x)

def attach (x : Raw × Data Table) : LawData × List UpdateProgram.Raw :=
  (x.2.1,x.2.2.map fun G => ((x.1.1.1.1.2,x.1.1.2),
    (((x.1.1.1.1.1.1,x.1.2.1),(x.1.1.1.1.2,x.1.2.2)),G)))
@[fun_prop] theorem attach_poly : Poly attach := by
  unfold attach
  apply pair
  · fun_prop
  · apply list_map <;> fun_prop

 local instance instLinearOrderSubtypeCopyFinMemFinset_rf7a4cb_1 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
theorem attach_input (x : Context) : attach ((ctxRaw x),x.toInput.result)=
    (x.toInput.result.1, (ctxInputs x).map UpdateProgram.Input.raw) := by
  simp only [attach,ctxRaw,CopyGraphProgram.Input.result,ctxInputs,
    List.map_map,Function.comp_def]
  rfl

def ctxResult (x : Context) : Data Row :=
  (((ctxLaw x).law.denominator,List.ofFn (ctxLaw x).law.numerator),(ctxLaw x).states.toList.map CopyList.view)

end MetricKMedian.RationalPhysicalKernel.RoundProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalHistoriesProgram
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
abbrev view (x : Context) (z : Hist x) := CopyList.view z.1.1
def result (P : ℕ → ℚ) (T : ℕ) (x : Context) : Data Row := table (law P T x) (view x)

def nextRaw (P : ℚ) (x : RoundProgram.Raw × Row) : RoundProgram.Raw :=
  (((((x.1.1.1.1.1.1,P),x.1.1.1.1.2),x.1.1.1.2),x.2),x.1.2)
@[fun_prop] theorem nextRaw_poly (P : ℚ) : Poly (nextRaw P) := by unfold nextRaw; fun_prop

def attach (P : ℚ) (x : RoundProgram.Raw × Data Row) : LawData × List RoundProgram.Raw :=
  (x.2.1,x.2.2.map (fun A => nextRaw P (x.1,A)))
@[fun_prop] theorem attach_poly (P : ℚ) : Poly (attach P) := by
  unfold attach
  apply pair
  · fun_prop
  · apply list_map <;> fun_prop

 theorem attach_result (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) :
    attach (P T) (RoundProgram.ctxRaw x,result P T x)=
      ((result P T x).1,(inputs P T hP x).map RoundProgram.ctxRaw) := by
  simp only [attach,result,table,inputs,List.map_map,Function.comp_def]
  rfl

 theorem conditional (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) (z : Hist x) :
    RoundProgram.ctxResult (nextCtx x (P T) hP z.1.1)=
      table (SparseHistories.branch (step x.d x.g x.β x.p x.φ (P T) x.hp x.hφ x.hupper) z) (view x) := by
  change table (RoundProgram.ctxLaw (nextCtx x (P T) hP z.1.1)) CopyList.view=_
  have hs := RoundProgram.law_step (nextCtx x (P T) hP z.1.1) z.1 rfl
  rw [hs,table_map]
  unfold SparseHistories.branch
  rw [table_map]
  rfl

end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_HistorySelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel
variable {τ : ℝ} (q : RationalParameters τ)
abbrev Input.encode (x : Input q) := enc x.raw

def ctxRaw (x : Raw) : RoundProgram.Raw := (((((q.g,1),q.Δ),x.1),x.2.2.2.2),(q.β,(q.probabilityQ,q.φ)))
@[fun_prop] theorem ctxRaw_poly : Poly (ctxRaw q) := by unfold ctxRaw; fun_prop

def Input.items (x : Input q) : List (Completion.Rational.Program.Input q.Δ) :=
  (q.tree x.d₀ x.A).states.toList.map (fun z => {x.toInput with A:=z.1.1})
def attach (x : Raw × Data Row) : List Completion.Rational.Program.Raw :=
  x.2.2.map (fun A => (x.1.2.1,(x.1.2.2.1,(x.1.2.2.2.1,A))))
@[fun_prop] theorem attach_poly : Poly attach := by unfold attach; apply list_map <;> fun_prop
 theorem attach_input (x : Input q) : attach (x.raw,HistoryProgram.result q.taperAt q.T x.ctx)=
    x.items.map Completion.Rational.Program.Input.raw := by
  simp only [attach,HistoryProgram.result,table,Input.items,List.map_map,Function.comp_def]
  rfl

def dummy : Completion.Rational.Program.Input q.Δ where
  f := 0
  j := 0
  d := fun c => Fin.elim0 c
  R := fun c => Fin.elim0 c
  A := ∅
  B := fun c => Fin.elim0 c
  hB := fun c => Fin.elim0 c

def metadata (x : Raw) : ℚ × List (List ℚ) :=
  (q.g*Completion.Rational.BestProgram.card x.2.2.2.2+q.allowance,x.2.2.1.1)
@[fun_prop] theorem metadata_poly : Poly (metadata q) := by unfold metadata; fun_prop

def Input.result (x : Input q) : Table :=
  ((q.selectCompleted x.d₀ x.d x.R x.A x.B x.hB).map setView).toList
end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_GridDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.FixedBatch.RationalParameters.GridDataProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel CopyList CopyNearestProgram
variable {τ : ℝ} (q : RationalParameters τ)

structure Input where
  f : ℕ
  j : ℕ
  d₀ : Fin f → Fin f → ℚ
  d : Fin j → Fin f → ℚ
  A : Finset (CopyState.Copy (F:=Fin f) q.Δ)
  enough : q.Δ≤A.card
abbrev Raw := List Unit × ((List (List ℚ) × List (List ℚ)) × Row)
def Input.raw (x : Input q) : Raw := (List.replicate x.f (),((List.ofFn (fun i => List.ofFn (x.d₀ i)),
  List.ofFn (fun c => List.ofFn (x.d c))),view x.A))

def Input.selection (x : Input q) : SelectionProgram.Input q where
  f := x.f
  j := x.j
  d := x.d
  R := q.radius x.d x.A x.enough
  A := x.A
  B := q.nearest x.d x.A
  hB := q.nearest_nonempty x.d x.A x.enough
  d₀ := x.d₀

def prepare (Δ : ℕ) (x : Raw) : SelectionProgram.Raw :=
  (x.2.1.1,(x.1,((x.2.1.2,x.2.1.2.map (fun ds => radiusRaw Δ (ds,x.2.2))),
    (x.2.1.2.map (fun ds => nearestRaw Δ (ds,x.2.2)),x.2.2))))
@[fun_prop] theorem prepare_poly (Δ : ℕ) : Poly (prepare Δ) := by
  unfold prepare
  have hr : Poly (fun x : Raw => x.2.1.2.map (fun ds => radiusRaw Δ (ds,x.2.2))) := by apply list_map <;> fun_prop
  have hn : Poly (fun x : Raw => x.2.1.2.map (fun ds => nearestRaw Δ (ds,x.2.2))) := by apply list_map <;> fun_prop
  fun_prop
 theorem prepare_input (x : Input q) : prepare q.Δ x.raw=x.selection.raw := by
  simp only [prepare,Input.raw,List.map_ofFn,Function.comp_def,nearestRaw_view q,radiusRaw_view q x.d x.A x.enough]
  rfl
end MetricKMedian.FixedBatch.RationalParameters.GridDataProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundCountsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel CopyList
variable {τ : ℝ} (q : RationalParameters τ)
abbrev Input.encode (x : Input) := enc x.raw

@[fun_prop] theorem cap_poly (Δ : ℕ) : Poly (cap Δ) := by unfold cap; apply comp bool_all; apply list_map <;> fun_prop
 theorem cap_input (x : Input) : cap q.Δ (List.ofFn x.n)=decide (∀ i, x.n i≤q.Δ) := by
  apply Bool.eq_iff_iff.mpr
  simp [cap]

def valid (Δ : ℕ) (x : Raw) : Bool := cap Δ x.2.2 && decide (Δ≤Completion.Rational.BestProgram.card (CopyState.CountsProgram.mask Δ x.2.2))
@[fun_prop] theorem valid_poly (Δ : ℕ) : Poly (valid Δ) := by unfold valid; fun_prop
 theorem valid_input (x : Input) (hn : ∀ i, x.n i≤q.Δ) : valid q.Δ x.raw=decide (q.Δ≤(CopyState.activeSlots x.n hn).card) := by
  unfold valid Input.raw
  dsimp only
  rw [cap_input q x,decide_eq_true hn,Bool.true_and,CopyState.CountsProgram.mask_view x.n hn,
    CopyList.view,Completion.Rational.BestProgram.card_view,card_map]

def dummy : SelectionProgram.Input q where
  f := 0
  j := 0
  d := fun c => Fin.elim0 c
  R := fun c => Fin.elim0 c
  A := ∅
  B := fun c => Fin.elim0 c
  hB := fun c => Fin.elim0 c
  d₀ := fun i => Fin.elim0 i

def Input.selection (x : Input) : SelectionProgram.Input q :=
  if hn : ∀ i, x.n i≤q.Δ then
    if hA : q.Δ≤(CopyState.activeSlots x.n hn).card then
      GridDataProgram.Input.selection q ⟨x.f,x.j,x.d₀,x.d,CopyState.activeSlots x.n hn,hA⟩
    else dummy q
  else dummy q

def prepare (x : Raw) : SelectionProgram.Raw :=
  if valid q.Δ x then GridDataProgram.prepare q.Δ (x.1,(x.2.1,CopyState.CountsProgram.mask q.Δ x.2.2))
  else (dummy q).raw
@[fun_prop] theorem prepare_poly : Poly (prepare q) := by unfold prepare; fun_prop
 theorem prepare_input (x : Input) : prepare q x.raw=(x.selection q).raw := by
  unfold prepare Input.selection
  by_cases hn : ∀ i, x.n i≤q.Δ
  · rw [dite_eq_left hn,valid_input q x hn]
    by_cases hA : q.Δ≤(CopyState.activeSlots x.n hn).card
    · rw [dite_eq_left hA,ite_eq_left (decide_eq_true hA)]
      rw [show (x.raw.1,(x.raw.2.1,CopyState.CountsProgram.mask q.Δ x.raw.2.2))=
        GridDataProgram.Input.raw q ⟨x.f,x.j,x.d₀,x.d,CopyState.activeSlots x.n hn,hA⟩ by
          unfold Input.raw GridDataProgram.Input.raw
          dsimp only
          rw [CopyState.CountsProgram.mask_view x.n hn]]
      exact GridDataProgram.prepare_input q _
    · simp only [dite_eq_right hA,decide_eq_false hA,Bool.false_eq_true,ite_false]
  · rw [dite_eq_right hn]
    have hv : valid q.Δ x.raw=false := by
      unfold valid Input.raw
      dsimp only
      rw [cap_input q x,decide_eq_false hn,Bool.false_and]
    simp only [hv,Bool.false_eq_true,ite_false]

def Input.result (x : Input) : Table := ((q.roundCounts x.d₀ x.d x.n).map setView).toList

def finish (x : Raw × Table) : Table := if valid q.Δ x.1 then x.2 else []
@[fun_prop] theorem finish_poly : Poly (finish q) := by unfold finish; fun_prop
 theorem finish_input (x : Input) : finish q (x.raw,SelectionProgram.Input.result q (x.selection q))=x.result q := by
  unfold finish Input.result RationalParameters.roundCounts
  by_cases hn : ∀ i, x.n i≤q.Δ
  · rw [dite_eq_left hn,valid_input q x hn]
    by_cases hA : q.Δ≤(CopyState.activeSlots x.n hn).card
    · simp only [dite_eq_left hA,decide_eq_true hA,ite_true,Input.selection,dite_eq_left hn]
      rfl
    · simp only [dite_eq_right hA,decide_eq_false hA,Bool.false_eq_true,ite_false,Option.map_none,Option.toList_none]
  · rw [dite_eq_right hn]
    have hv : valid q.Δ x.raw=false := by
      unfold valid Input.raw
      dsimp only
      rw [cap_input q x,decide_eq_false hn,Bool.false_and]
    simp only [hv,Bool.false_eq_true,ite_false,Option.map_none,Option.toList_none]

end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
variable {τ : ℝ} (q : RationalParameters τ)
abbrev Input.encode (x : Input) := enc x.raw

def prepare (x : Raw) : List RoundCountsProgram.Raw := x.2.2.1.map (fun ns =>
  (x.1.2.map (fun _ => ()),((MaskProgram.pullbackMatrix (x.2.1.1,x.1.2),
    x.2.1.2.map (fun ds => MaskProgram.pullback (ds,x.1.2))),ns)))
@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply list_map
  · have hd : Poly (fun x : Raw × List ℕ => x.1.2.1.2.map (fun ds => MaskProgram.pullback (ds,x.1.1.2))) := by
      apply list_map <;> fun_prop
    have hu : Poly (fun x : Raw × List ℕ => x.1.1.2.map (fun _ => ())) := by apply list_map <;> fun_prop
    fun_prop
  · fun_prop
 theorem prepare_input (x : Input) : prepare x.raw=x.items.map RoundCountsProgram.Input.raw := by
  simp only [prepare,Input.raw,List.map_ofFn,Function.comp_def,MaskProgram.pullbackMatrix_view,
    MaskProgram.pullback_view,List.map_map,Input.items]
  apply List.map_congr_left
  intro n _
  simp only [Input.item,RoundCountsProgram.Input.raw]
  congr 1
  simp

noncomputable def itemsProgram : PolyProgram Input.encode (encodeList RoundCountsProgram.Input.encode) Input.items :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    change encodeList enc (prepare x.raw)=_
    rw [prepare_input,encodeList_map]
    rfl)

def Input.candidates (x : Input) := q.countCandidates x.df x.dc x.orig x.ns

def images (x : Raw × List Table) : Table := x.2.flatten.map (fun O => MaskProgram.imageRaw (x.1.1,O))
@[fun_prop] theorem images_poly : Poly images := by
  unfold images
  apply list_map
  · fun_prop
  · exact comp (⟨listFlatten (enc : Row → List Bool) []⟩ : Poly (List.flatten : List Table → Table)) (by fun_prop)
 theorem images_input (x : Input) : images (x.raw,x.items.map (RoundCountsProgram.Input.result q))=
    (x.candidates q).map setView := by
  simp only [images,Input.items,List.map_map,Function.comp_def,RoundCountsProgram.Input.result,
    Input.item,Input.raw]
  rw [List.map_flatten]
  simp only [List.map_map,Function.comp_def,← Option.toList_map,Option.map_map]
  change (x.ns.map (fun n => (((q.roundCounts (fun a b => x.df (x.orig a) (x.orig b))
    (fun c a => x.dc c (x.orig a)) n).map (fun O => MaskProgram.imageRaw
      ((List.replicate x.h (),List.ofFn (fun i => (x.orig i).val)),setView O))).toList))).flatten=_
  simp only [MaskProgram.imageRaw_view]
  simp only [Input.candidates,RationalParameters.countCandidates,
    List.flatMap_def,List.map_flatten,List.map_map]
  simp only [← Option.toList_map,Option.map_map,Function.comp_def]

def Input.result (x : Input) : Table := ((q.roundList x.df x.dc x.orig x.ns x.budget).map setView).toList
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end


