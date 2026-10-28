-- Prove2me | Definitions.Def_OAIQ035K065
-- name    : OAIQ035K065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:17:12.820015+00:00
-- url     : https://prove2.me/theorems/cf83dfde-adcf-4df0-affb-d39622d41baf
-- title:
--   Definitions bundle OAIQ035K065 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 34 definitions and 11 theorems. The definitions and types are `OAI.MetricKMedian.IntegerLaw.BinaryCompression.compressProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.rationalCompressProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.Input.encode`, `OAI.MetricKMedian.RationalBatchData.ActionTransition.view`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.inputProgram`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.graphProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.inputsProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.encode`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.result`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.proposalProgram`, `OAI.MetricKMedian.RoundingProgram.compressProgram`, `OAI.MetricKMedian.RoundingProgram.runProgram`, `OAI.MetricKMedian.RoundingProgram.stepProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.branchProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.compressProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.endpointProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.probabilityProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.runStateProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.stepProgram`, `OAI.MetricKMedian.SparseCardinalRounding.Program.program`, `OAI.MetricKMedian.SparseGraph.Program.compressProgram`, `OAI.MetricKMedian.SparseGraph.Program.inputProgram`, `OAI.MetricKMedian.SparseGraph.Program.lawProgram`, `OAI.MetricKMedian.SparseGraph.Program.runStateProgram`, `OAI.MetricKMedian.SparseGraph.Program.stepProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.compressProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.bernInputProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.bernProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.partProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.program`, `OAI.MetricKMedian.TaperGraphProgram.program`, `OAI.MetricKMedian.TaperGraphProgram.qInputProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_CompressionBinaryProgram`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_ActionTransitionList`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyNextProgram`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Process_TaperGraphProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_GraphStepProgram`.
--
--   **Imports.** It imports the bundles `OAIQ035K059`, `OAIQ035K060` and `OAIQ035K061` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K069` and `OAIQ035K070`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K059
import Definitions.Def_OAIQ035K060
import Definitions.Def_OAIQ035K061

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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
abbrev Input.encode (z : Input) := enc z.raw

end MetricKMedian.Preparation.FractionalRefinement.Program
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

noncomputable def stepProgram (s : Bool) : PolyProgram State.encode State.encode (@State.step s) :=
  (branchProgram s).comp (compressProgram s)

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

noncomputable def compressProgram (a0 : A) (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ)
    (F : C × A → List ℚ) (hF : ∀ c a, F (c,view c a)=List.ofFn (v c a))
    (D : PolyProgram ec IntegerLaw.BinaryCompression.es (fun c => List.replicate (d c) ()))
    (V : PolyProgram (encodePair ec ea) IntegerLaw.BinaryCompression.eqr F) :
    PolyProgram (Bundle.encode ec ea view) (Bundle.encode ec ea view) (Bundle.compress d v) := by
  let law := (compressionInputProgram ec ea view a0 d v F hF D V).comp IntegerLaw.BinaryCompression.rationalCompressProgram
  let trimmed := (law.fanout (statesProgram ec ea view)).comp (trimDataProgram ea a0)
  let work := (contextProgram ec ea view).fanout trimmed
  exact work.recode id (fun _ => rfl) (fun x => by
    change encodePair ec (ed ea) (x.ctx,
      trimData (((x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])).denominator,
       List.ofFn (x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])).numerator),
         x.law.states.toList.map (view x.ctx)))=_
    rw [show trimData _= _ from trim_view view x.ctx
      (⟨x.law.length,x.law.states,x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])⟩ : SparseIntegerLaw (T x.ctx))]
    rfl)

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
 theorem probability_view (c : Context) (q : T c) : rowProbability (c,view c q)=probability c q := by
  simp only [rowProbability,probability,view,List.getElem?_ofFn]
  split_ifs <;> rfl
 theorem endpoint_view (c : Context) (q : T c) (b : Fin 2) :
    rowEndpoint (decide (b=0)) (c,view c q)=view c (endpoint c q b) := by
  apply List.ext_getElem
  · simp only [rowEndpoint,ListOperation.endpoint,List.length_map,List.length_range,view,List.length_ofFn]
  · intro i hi hi'
    have hin : i < c.input.n := by simpa only [view,List.length_ofFn] using hi'
    simp only [rowEndpoint,ListOperation.endpoint,view,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hin,Option.getD_some,endpoint]

noncomputable def probabilityProgram : PolyProgram (encodePair Context.encode er) Ratio.encode rowProbability := by
  let raw : PolyProgram (encodePair (encodePair qr Nat.bits) er) Ratio.encode
      (fun x : (List ℚ × ℕ) × Row => x.1.1[x.1.2]?.getD 0) := by
    exact Binary.Automatic.Poly.program (by fun_prop)
  exact raw.recode (fun x => (x.1.raw,x.2)) (fun _ => rfl) (fun _ => rfl)
noncomputable def endpointProgram (b : Bool) : PolyProgram (encodePair Context.encode er) er (rowEndpoint b) :=
  (((fst Context.encode er).comp ((snd qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))).fanout
     (snd Context.encode er)).comp (ListOperation.endpoint_poly b).program

noncomputable def branchProgram : PolyProgram State.encode State.encode (Bundle.branch probability probability_unit endpoint) :=
  SparseIntegerLaw.DependentProgram.branchProgram Context.encode er view [] probability probability_unit endpoint
    rowProbability (rowEndpoint true) (rowEndpoint false) probability_view
    (fun c q => endpoint_view c q 0) (fun c q => endpoint_view c q 1)
    probabilityProgram (endpointProgram true) (endpointProgram false)

noncomputable def compressProgram (d : ℕ) : PolyProgram State.encode State.encode
    (Bundle.compress (fun c : Context => (c.input.n+1)^d) (fun _ => features (d:=d))) :=
  SparseIntegerLaw.DependentProgram.compressProgram Context.encode er view [] (fun c => (c.input.n+1)^d) (fun _ => features (d:=d))
    (fun x => ListOperation.featureList d x.2) (fun _ q => ListOperation.featureList_ofFn q)
    (dimensionsProgram d) (featuresProgram d)

noncomputable def stepProgram (d : ℕ) : PolyProgram State.encode State.encode (State.step d) :=
  ((PolyProgram.ite activeProgram (identity State.encode) (branchProgram.comp (compressProgram d))).comp incrementProgram).congr _
    (fun x => by simp only [State.step,Function.comp_def,decide_eq_true_eq,id_eq])

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

noncomputable def runStateProgram (d : ℕ) : PolyProgram Input.encode State.encode (fun x => x.state d x.n) :=
  ((stepProgram d).repeatFrom startProgram countProgram X (sizePolynomial d)
    (fun x => by simpa using (input_bounds x).1)
    (fun x t ht => by rw [state_iterate]; exact state_size x d t ht)).congr _ (fun x => state_iterate x d _)

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActionTransitionList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ActionTransition
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)

variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I) (Z : Finset (HeavyAction D H))
def view : Raw := (Ordinal.view r D H,setView (Z.map (enumeration D H).symm.toEmbedding))
 theorem selected_mem (c : ℕ) : c∈selected (view r D H Z) ↔ ∃ e∈Z, Ordinal.code r D H e=c := by
  simp only [selected,view,Ordinal.codes_eq,setView,mem_map_equiv,Equiv.symm_symm,
    Gaussian.ListOperation.zip_ofFn,List.mem_map,List.mem_filter,List.mem_ofFn]
  constructor
  · rintro ⟨z,⟨⟨i,rfl⟩,he⟩,hc⟩
    exact ⟨enumeration D H i,of_decide_eq_true he,hc⟩
  · rintro ⟨e,he,rfl⟩
    refine ⟨_,⟨⟨(enumeration D H).symm e,rfl⟩,?_⟩,?_⟩ <;>
      simp only [Equiv.apply_symm_apply,decide_eq_true he]

 theorem selected_light (hD : ∀ i, D.source i=i) (i : Fin n) : i.val∈selected (view r D H Z) ↔
    r i∈(Z∩(heavy D H).ordinary).image (heavy D H).source := by
  rw [selected_mem]
  constructor
  · rintro ⟨e,he,hc⟩
    have hl := (Ordinal.code_light r D H e).mp (hc ▸ i.isLt)
    cases e with
    | inl h =>
      refine mem_image.mpr ⟨.inl h,mem_inter.mpr ⟨he,?_⟩,?_⟩
      · simp only [heavy,mem_filter,mem_univ,Sum.isLeft_inl,and_self]
      · change D.source h.val=r i
        rw [hD]
        have hh : r.symm h.val=i := Fin.ext hc
        exact (r.symm.injective (hh.trans (r.symm_apply_apply i).symm))
    | inr h => cases hl
  · rintro hi
    obtain ⟨e,he,hE⟩ := mem_image.mp hi
    rcases mem_inter.mp he with ⟨he,hord⟩
    cases e with
    | inl h =>
      refine ⟨.inl h,he,?_⟩
      change D.source h.val=r i at hE
      rw [hD] at hE
      simp only [Ordinal.code,hE,OrderIso.symm_apply_apply]
    | inr h => simp only [heavy,mem_filter,mem_univ,Sum.isLeft_inr,Bool.false_eq_true,and_false] at hord

 theorem dead_view : dead (view r D H Z)=Ordinal.sets r (Z.biUnion (heavy D H).erase) := by
  unfold dead
  rw [show (view r D H Z).1.2=Ordinal.sets r H from rfl]
  simp only [indices,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,Ordinal.sets_eq,List.length_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_map,Function.comp_def,id_eq,List.any_eq_true,decide_eq_true_eq,mem_biUnion]
  constructor
  · rintro ⟨c,hc,hv⟩
    obtain ⟨e,he,rfl⟩ := (selected_mem r D H Z c).mp hc
    dsimp only [view] at hv
    rw [Ordinal.erase_code,Ordinal.sets_eq] at hv
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true_eq] at hv
    exact ⟨e,he,hv⟩
  · rintro ⟨e,he,hi⟩
    refine ⟨Ordinal.code r D H e,(selected_mem r D H Z _).mpr ⟨e,he,rfl⟩,?_⟩
    dsimp only [view]
    rw [Ordinal.erase_code,Ordinal.sets_eq]
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true hi]

 theorem sources_view (hD : ∀ i, D.source i=i) : sources (view r D H Z)=Ordinal.sets r
    (H∪(Z∩(heavy D H).ordinary).image (heavy D H).source) := by
  unfold sources
  rw [show (view r D H Z).1.2=Ordinal.sets r H from rfl]
  simp only [indices,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,Ordinal.sets_eq,List.length_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,Bool.or_eq_true,
    decide_eq_true_eq,natMember_true,mem_union]
  exact or_congr Iff.rfl (selected_light r D H Z hD i)

end MetricKMedian.RationalBatchData.ActionTransition
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
local notation "br" => SparseGraph.ListOperation.er

noncomputable def bernInputProgram (bal : Bool) :
    PolyProgram Input.encode SparseBernoulli.Program.Input.encode (Input.bernInput bal) := by
  let raw : PolyProgram Binary.Automatic.enc SparseBernoulli.Program.qr
      (fun x : ListOperation.Raw => if bal then x.2.2.map (fun _ => x.2.1) else x.2.2) := by
    apply Binary.Automatic.Poly.program
    have hm : Binary.Automatic.Poly (fun x : ListOperation.Raw => x.2.2.map (fun _ => x.2.1)) := by
      apply Binary.Automatic.Poly.list_map <;> fun_prop
    fun_prop
  exact raw.recode Input.raw (fun _ => rfl) (fun x => by
    cases bal <;> simp only [Bool.false_eq_true,ite_false,ite_true,Input.raw,List.map_const',List.length_ofFn,
      Input.bernInput,SparseBernoulli.Program.Input.encode,List.ofFn_const,Fin.cast_eq_self])

noncomputable def bernProgram (bal : Bool) : PolyProgram Input.encode (ed br)
    (fun x : Input => (((x.bern bal).law.denominator,List.ofFn (x.bern bal).law.numerator),
      (x.bern bal).states.toList.map List.ofFn)) := by
  let get : PolyProgram SparseBernoulli.Program.State.encode (ed br)
      (fun x : SparseBernoulli.Program.State => (x.raw SparseBernoulli.Program.view).2) :=
    (snd SparseBernoulli.Program.Context.encode (ed br)).recode
      (Bundle.raw SparseBernoulli.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (bernInputProgram bal |>.comp (SparseBernoulli.Program.runStateProgram 4) |>.comp get).congr _ (fun _ => rfl)

noncomputable def partProgram (bal : Bool) : PolyProgram Input.encode (ed br) (Input.partData bal) := by
  let ctx : PolyProgram Input.encode Binary.Automatic.enc Input.raw := (identity Binary.Automatic.enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let post : PolyProgram (encodePair Binary.Automatic.enc (ed br)) (ed br)
      (fun x : ListOperation.Raw × Data Row => (x.2.1,x.2.2.map (fun row => ListOperation.select bal (x.1,row)))) := by
    apply Binary.Automatic.Poly.program
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact (ctx.fanout (bernProgram bal) |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,Input.partData,Input.part,SparseIntegerLaw.map,Vector.toList_map,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro ω hω
    exact ListOperation.select_view x.Z x.C x.p x.q ω bal)

noncomputable def program : PolyProgram Input.encode (ed br) Input.result :=
  ((partProgram true).fanout (partProgram false) |>.comp mixData_poly.program).congr _ (fun x => by
    change mixData (((raw (x.part true)).1,(x.part true).states.toList.map SparseGraph.ListOperation.setView),
      ((raw (x.part false)).1,(x.part false).states.toList.map SparseGraph.ListOperation.setView))=_
    rw [mixData_raw]
    rfl)
end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchProposalProgram
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

noncomputable def inputProgram : PolyProgram (Input.encode (I:=I)) SparsePhysicalBatch.Program.Input.encode Input.batch :=
  GraphData.data_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg Binary.Automatic.enc (data_input x))

 theorem result_eq (x : Input I) : x.batch.result=x.result := by
  unfold Input.result Input.law proposal SparseEnumeratedBatch.law
  simp only [SparseIntegerLaw.map,Vector.toList_map,List.map_map,Function.comp_def]
  change x.batch.result=(((SparsePhysicalBatch.law x.batch.Z x.batch.C x.batch.p x.batch.q x.batch.hp x.batch.hq).law.denominator,
    List.ofFn (SparsePhysicalBatch.law x.batch.Z x.batch.C x.batch.p x.batch.q x.batch.hp x.batch.hq).law.numerator),_)
  unfold SparsePhysicalBatch.Program.Input.result
  congr 1
  apply List.map_congr_left
  intro Z hZ
  clear hZ
  dsimp only [Input.batch] at Z ⊢
  congr 1
  ext i
  simp only [mem_map_equiv,Equiv.symm_symm,Equiv.symm_apply_apply]

noncomputable def program : PolyProgram (Input.encode (I:=I)) (ed SparseGraph.ListOperation.er) Input.result :=
  (inputProgram.comp SparsePhysicalBatch.Program.program).congr _ (fun x => result_eq x)
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

noncomputable def runProgram (s : Bool) : PolyProgram Input.encode State.encode (fun x : Input s => x.run x.n) :=
  ((stepProgram s).repeatFrom (startProgram s) (countProgram s) X statePolynomial
    (fun x => by simpa using (input_bounds x).1) (fun x i hi => by
      rw [input_iterate]; exact run_size x i hi)).congr _ (fun x => input_iterate x _)

end MetricKMedian.RoundingProgram
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

noncomputable def compressProgram : PolyProgram State.encode State.encode
    (Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m)) (fun _ => features)) :=
  SparseIntegerLaw.DependentProgram.compressProgram Context.encode et view [] _ (fun _ => features)
    (fun x => ListOperation.featureList (x.1.input.raw.1,x.2))
    (fun _ G => ListOperation.featureList_view G) dimensionsProgram featuresProgram

noncomputable def stepProgram : PolyProgram State.encode State.encode State.step :=
  ((PolyProgram.ite activeProgram (identity State.encode) (productProgram.comp compressProgram)).comp incrementProgram).congr _
    (fun x => by simp only [State.step,Function.comp_def,decide_eq_true_eq,id_eq])
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse

noncomputable def program : PolyProgram encodeInput (ed br) result := by
  let part := inputProgram.comp (RoundingProgram.runProgram false)
  let get : PolyProgram RoundingProgram.State.encode (ed RoundingProgram.erow)
      (fun x : RoundingProgram.State false => RoundingProgram.vectorData x.μ) :=
    (snd RoundingProgram.erow (ed RoundingProgram.erow)).recode RoundingProgram.State.raw
      RoundingProgram.State.encode_raw (fun _ => rfl)
  let post : PolyProgram (ed RoundingProgram.erow) (ed br)
      (fun x : Data (List ℚ) => (x.1,x.2.map selectedRow)) := by
    apply Binary.Automatic.Poly.program
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact (part.comp get |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,result,RoundingProgram.vectorData,SparseGraph.Program.columnRaw,
      SparseIntegerLaw.map,Vector.toList_map,List.map_map,selectedRow_eq]
    rfl)
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphRunProgram
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

noncomputable def runStateProgram : PolyProgram Input.encode State.encode (fun x => x.state x.m) :=
  (stepProgram.repeatFrom startProgram countProgram X sizePolynomial
    (fun x => by simpa using (input_bounds x).2.1)
    (fun x t ht => by rw [state_iterate]; exact state_size x t ht)).congr _ (fun x => state_iterate x _)
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

noncomputable def inputProgram : PolyProgram QInput.encode Input.encode QInput.input := by
  let n := (fst (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun _ => rfl)
  let cols := columnsProgram.comp (SparseCardinalRounding.Program.program.listMap emptyColumn)
  exact (n.fanout cols).recode id (fun _ => rfl) (fun x => by
    change ei (x.raw.1,x.columns.map SparseCardinalRounding.Program.result)=Input.encode x.input
    simp only [QInput.columns,List.map_ofFn,Function.comp_def]
    rfl)

noncomputable def lawProgram : PolyProgram QInput.encode (ed ListOperation.et) QInput.result := by
  let get : PolyProgram State.encode (ed ListOperation.et) (fun x : State => (x.raw view).2) :=
    (snd Context.encode (ed ListOperation.et)).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
  exact (inputProgram.comp runStateProgram |>.comp get).congr _ (fun _ => rfl)
end MetricKMedian.SparseGraph.Program
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

noncomputable def qInputProgram : PolyProgram Input.encode SparseGraph.Program.QInput.encode Input.qInput :=
  rawQ_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (rawQ_input x))
noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et)
    (fun x : Input => x.qInput.result) := qInputProgram.comp SparseGraph.Program.lawProgram
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

noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et) Input.result :=
  (taperProgram.comp TaperGraphProgram.program).congr _ result_eq

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyNextProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.RationalPhysicalKernel.CopyNext
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open CopyList
open CopyGraphProgram (rank_owner)
open SparseGraph.ListOperation (Row Table setView indices)
open RationalBatchData.Ordinal (sets)

 attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.instLinearOrderSubtypeCopyFinMemFinset
theorem pick_mem {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (S : Finset A) (k : ℕ) :
    k∈pick (active (view A),sets (ordinal A) S) ↔ ∃a∈S,(rank a.val).val=k := by
  simp only [pick,active_view,RationalBatchData.Ordinal.sets_eq,Gaussian.ListOperation.zip_ofFn,
    List.mem_map,List.mem_filter,List.mem_ofFn]
  constructor
  · rintro ⟨z,⟨⟨i,rfl⟩,hi⟩,hk⟩
    exact ⟨enumeration A i,of_decide_eq_true hi,hk⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨_,⟨⟨(enumeration A).symm a,rfl⟩,?_⟩,?_⟩
    · change decide (enumeration A ((enumeration A).symm a)∈S)=true
      rw [Equiv.apply_symm_apply]
      exact decide_eq_true ha
    · simp only [Equiv.apply_symm_apply]

 theorem next_view {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (E O : Finset A) :
    next ((Δ,view A),(sets (ordinal A) E,sets (ordinal A) O))=
    view (CopyState.next Δ A (E.image Subtype.val) (O.image (fun a => a.val.1))) := by
  unfold next
  have hl : (view A).length=f*Δ := by simp only [view,setView,List.length_ofFn]
  simp only [indices,hl,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  change List.ofFn (fun k : Fin (f*Δ) => _)=_
  conv_rhs => rw [view_eq]
  apply congrArg List.ofFn
  funext k
  let a := finProdFinEquiv.symm k
  have ha : rank a=k := finProdFinEquiv.apply_symm_apply k
  have hdiv : k.val/Δ=a.1.val := by rw [← ha,rank_owner]
  apply Bool.eq_iff_iff.mpr
  simp only [view_get,Bool.or_eq_true,
    Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,Bool.eq_false_iff,decide_eq_true_eq,natMember_true,
    CopyState.next,mem_union,mem_sdiff,CopyState.mem_resets]
  simp only [ne_eq,natMember_true]
  rw [pick_mem]
  apply or_congr
  · apply and_congr Iff.rfl
    apply not_congr
    simp only [mem_image]
    constructor
    · rintro ⟨b,hb,hk⟩
      exact ⟨b,hb,finProdFinEquiv.injective ((Fin.ext hk).trans ha.symm)⟩
    · rintro ⟨b,hb,hba⟩
      refine ⟨b,hb,?_⟩
      change b.val=a at hba
      rw [hba,ha]
  · rw [List.mem_map]
    simp only [mem_image]
    constructor
    · rintro ⟨j,hj,hjk⟩
      obtain ⟨b,hb,rfl⟩ := (pick_mem A O j).mp hj
      rw [rank_owner,hdiv] at hjk
      exact ⟨b,hb,Fin.ext hjk⟩
    · rintro ⟨b,hb,hba⟩
      refine ⟨(rank b.val).val,(pick_mem A O _).mpr ⟨b,hb,rfl⟩,?_⟩
      rw [rank_owner,hdiv]
      exact congrArg Fin.val hba

 theorem transition_view {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (RationalBatchData.graph G) H)) :
    transition ((Δ,view A),RationalBatchData.ActionTransition.view (ordinal A) (RationalBatchData.graph G) H Z)=
      view (RationalBatchData.transition A G H Z) := by
  unfold transition
  dsimp only
  have hd := RationalBatchData.ActionTransition.dead_view (ordinal A) (RationalBatchData.graph G) H Z
  have hs := RationalBatchData.ActionTransition.sources_view (ordinal A) (RationalBatchData.graph G) H Z (fun _ => rfl)
  rw [hd,hs]
  exact next_view A _ _

end MetricKMedian.RationalPhysicalKernel.CopyNext
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
abbrev Input.encode (x : Input) := enc x.raw

def Input.result (x : Input) : Data Row :=
  ((x.law.law.denominator,List.ofFn x.law.law.numerator),x.law.states.toList.map CopyList.view)

 attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
theorem result_map (x : Input) : x.result=(x.proposal.result.1,
    x.proposal.law.states.toList.map (fun Z => CopyList.view (x.update Z))) := by
  unfold Input.result Input.law
  change (x.proposal.result.1,(Vector.map x.update x.proposal.law.states).toList.map CopyList.view)=_
  erw [Vector.toList_map,List.map_map]
  rfl

noncomputable def proposalProgram : PolyProgram Input.encode
    RationalBatchData.ProposalProgram.Input.encode Input.proposal :=
  (snd enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)

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

noncomputable def graphProgram : PolyProgram ctxEncode (ed SparseGraph.ListOperation.et)
    (fun x => x.toInput.result) :=
  (show PolyProgram ctxEncode CopyGraphProgram.Input.encode (fun x : Context => x.toInput) from
    (fst enc enc).recode ctxRaw (fun _ => rfl) (fun _ => rfl)).comp CopyGraphProgram.program

noncomputable def inputsProgram : PolyProgram ctxEncode
    (encodePair enc (encodeList UpdateProgram.Input.encode)) (fun x => (x.toInput.result.1,(ctxInputs x))) := by
  let ctx : PolyProgram ctxEncode enc ctxRaw := (identity enc).recode ctxRaw (fun _ => rfl) (fun _ => rfl)
  exact (ctx.fanout graphProgram |>.comp attach_poly.program).recode id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_def,id_eq]
    rw [attach_input]
    change encodePair enc (encodeList enc) _=encodePair enc (encodeList UpdateProgram.Input.encode) _
    apply congrArg (fun w => quote (enc x.toInput.result.1)++w)
    induction ctxInputs x with
    | nil => rfl
    | cons a as ih => simpa only [List.map_cons,encodeList,UpdateProgram.Input.encode] using congrArg (fun w => quote (enc a.raw)++w) ih)

end MetricKMedian.RationalPhysicalKernel.RoundProgram
end

end OAI
end


