-- Prove2me | Definitions.Def_OAIQ053K065
-- name    : OAIQ053K065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:16:51.06851+00:00
-- url     : https://prove2.me/theorems/a75d1402-f7c2-4433-8fc7-0be01ffab11a
-- title:
--   Definitions bundle OAIQ053K065 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 15 definitions and 20 theorems. The definitions and types are `OAI.MetricKMedian.RationalBatchData.Ordinal.view`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.result`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.result`, `OAI.MetricKMedian.SparseBernoulli.Program.State.encode`, `OAI.MetricKMedian.SparseBernoulli.Program.endpointProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.rowEndpoint`, `OAI.MetricKMedian.SparseGraph.Program.dimensionsProgram`, `OAI.MetricKMedian.SparseGraph.Program.featuresProgram`, `OAI.MetricKMedian.SparseGraph.Program.incrementProgram`, `OAI.MetricKMedian.SparseGraph.Program.productProgram`, `OAI.MetricKMedian.SparseGraph.Program.rawColumn`, `OAI.MetricKMedian.SparseGraph.Program.rawProduct`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.statesProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.Input.partData`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.Input.result`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_Geometry_GraphListOperations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Geometry/GraphListOperations.lean), [`KMedian_Probability_BernoulliStepProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Probability/BernoulliStepProgram.lean), [`KMedian_Process_BatchOrdinalArrays`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/BatchOrdinalArrays.lean), [`KMedian_Process_BatchOrdinalCodes`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/BatchOrdinalCodes.lean), [`KMedian_Process_BatchProposalProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/BatchProposalProgram.lean), [`KMedian_Process_PhysicalBatchProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/PhysicalBatchProgram.lean), [`KMedian_Process_PhysicalBatchUpdateProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/PhysicalBatchUpdateProgram.lean), [`KMedian_Process_TaperGraphProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/TaperGraphProgram.lean), [`KMedian_Programs_DependentSparseProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/DependentSparseProgram.lean), [`KMedian_Programs_GraphRunProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/GraphRunProgram.lean), [`KMedian_Programs_GraphStepProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/GraphStepProgram.lean), [`KMedian_Sparse_SparseMixProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseMixProgram.lean).
--
--   **Imports.** It imports the bundles `OAIQ053K054`, `OAIQ053K055`, `OAIQ053K056` and `OAIQ053K057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K071` and `OAIQ053K072`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K054
import Definitions.Def_OAIQ053K055
import Definitions.Def_OAIQ053K056
import Definitions.Def_OAIQ053K057

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

 theorem dimensions_eq {n m : ℕ} (cs : Fin m → SparseIntegerLaw.BinarySparse.Data Row) :
    dimensions (List.replicate n (),List.ofFn cs)=List.replicate (n*m+(n*m)*(n*m)) () := by
  have h : (List.replicate n ()).flatMap (fun _ => (List.ofFn cs).map (fun _ => (0:ℚ)))=
      List.ofFn (fun _ : Fin (n*m) => (0:ℚ)) := by
    simp only [List.map_const',List.length_ofFn,List.flatMap_replicate,List.ofFn_const]
    simp [List.flatten_replicate_replicate]
  simp only [dimensions,h,RoundingList.dimensions_list]
end MetricKMedian.SparseGraph.ListOperation
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

noncomputable def statesProgram : PolyProgram (Bundle.encode ec ea view) (encodeList ea)
    (fun x : Bundle T => x.law.states.toList.map (view x.ctx)) :=
  ((snd ec (ed ea)).comp (snd el (encodeList ea))).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)

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
abbrev State.encode := Bundle.encode Context.encode er view

def rowEndpoint (b : Bool) (x : Context × Row) : Row := ListOperation.endpoint x.1.t b x.2
noncomputable def endpointProgram (b : Bool) : PolyProgram (encodePair Context.encode er) er (rowEndpoint b) :=
  (((fst Context.encode er).comp ((snd qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))).fanout
     (snd Context.encode er)).comp (ListOperation.endpoint_poly b).program

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalCodes
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

def view : ActionList.Raw := (List.ofFn fun h => sets r (D.erase (r h)),sets r H)

 theorem sets_length (S : Finset I) : (sets r S).length=n := by rw [sets_eq,List.length_ofFn]
 theorem sets_card (S : Finset I) : ((sets r S).filter id).length=S.card := by
  exact (MetricKMedian.EncodingLists.bool_card _).trans (card_map _)

 theorem valid_code (e : HeavyAction D H) : ActionList.valid (view r D H) (code r D H e)=true := by
  have hp := parent_code r D H e
  cases e with
  | inl e =>
    change ActionList.valid (view r D H) (r.symm e.val).val=true
    simp only [ActionList.valid,view,sets_eq,List.length_ofFn,ite_eq_left (r.symm e.val).isLt,
      List.getElem?_ofFn,dite_eq_left (r.symm e.val).isLt,Option.getD_some,Fin.eta,
      OrderIso.apply_symm_apply,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not]
    exact e.property
  | inr e =>
    have hc : ¬n+(r.symm e.val.1).val*n+(r.symm e.val.2).val<n := by omega
    change ActionList.valid (view r D H) (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=true
    simp only [ActionList.valid,view,sets_eq,List.length_ofFn,ite_eq_right hc]
    rw [show ActionList.parent n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.1).val from hp,
      show ActionList.child n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.2).val from child_code r D H e]
    simp only [List.getElem?_ofFn,dite_eq_left (r.symm e.val.1).isLt,dite_eq_left (r.symm e.val.2).isLt,
      Option.getD_some,Fin.eta,OrderIso.apply_symm_apply,decide_eq_true e.property.1,decide_eq_true e.property.2,Bool.and_self]
 theorem units_length : (ActionList.units (view r D H)).length=n+n*n := by
  simp [ActionList.units,view,sets_eq,List.length_flatMap,Function.comp_def]
 theorem mem_codes (c : ℕ) : c∈ActionList.codes (view r D H) ↔ ∃ e, code r D H e=c := by
  simp only [ActionList.codes,indices,units_length,List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨hc,hv⟩
    by_cases hl : c<n
    · simp only [ActionList.valid,view,sets_eq,List.length_ofFn,ite_eq_left hl,List.getElem?_ofFn,dite_eq_left hl,
        Option.getD_some,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not] at hv
      refine ⟨.inl ⟨r ⟨c,hl⟩,hv⟩,?_⟩
      simp only [code,OrderIso.symm_apply_apply]
    · have hn : 0<n := by nlinarith
      have hq : (c-n)/n<n := (Nat.div_lt_iff_lt_mul hn).mpr (by omega)
      have hr : (c-n)%n<n := Nat.mod_lt _ hn
      simp only [ActionList.valid,view,sets_eq,List.length_ofFn,ActionList.parent,ite_eq_right hl,ActionList.child,
        List.getElem?_ofFn,dite_eq_left hq,dite_eq_left hr,Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at hv
      refine ⟨.inr ⟨(r ⟨(c-n)/n,hq⟩,r ⟨(c-n)%n,hr⟩),hv⟩,?_⟩
      simp only [code,OrderIso.symm_apply_apply]
      have hh := Nat.mod_add_div (c-n) n
      rw [Nat.mul_comm] at hh
      have hs := Nat.sub_add_cancel (Nat.le_of_not_gt hl)
      omega
  · rintro ⟨e,rfl⟩; exact ⟨code_lt r D H e,valid_code r D H e⟩
 theorem codes_eq [Fintype I] : ActionList.codes (view r D H)=List.ofFn (fun i => code r D H (enumeration D H i)) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_range _).pairwise.filter _).sortedLT
  · exact (enumeration_strictMono r D H).sortedLT_ofFn
  · intro c
    rw [mem_codes,List.mem_ofFn]
    constructor
    · rintro ⟨e,rfl⟩; exact ⟨(enumeration D H).symm e,by rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨i,rfl⟩; exact ⟨enumeration D H i,rfl⟩
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalArrays
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

 theorem erase_code (e : HeavyAction D H) :
    ActionArrays.erase (view r D H) (code r D H e)=sets r ((heavy D H).erase e) := by
  cases e with
  | inl e =>
    change ActionArrays.erase (view r D H) (r.symm e.val).val=sets r (D.erase e.val)
    simp only [ActionArrays.erase,view,sets_length,ite_eq_left (r.symm e.val).isLt,
      List.getElem?_ofFn,dite_eq_left (r.symm e.val).isLt,Option.getD_some,Fin.eta,OrderIso.apply_symm_apply]
  | inr e =>
    have hc : ¬ n+(r.symm e.val.1).val*n+(r.symm e.val.2).val<n := by omega
    change ActionArrays.erase (view r D H) (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=sets r {e.val.2}
    simp only [ActionArrays.erase,view,sets_length,ite_eq_right hc,indices,
      RoundingList.range_finRange,List.map_map,Function.comp_def]
    rw [← List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext i
    rw [show ActionList.child n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.2).val from child_code r D H e]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,mem_map_equiv,mem_singleton,← Fin.ext_iff]
    change (i=r.symm e.val.2) ↔ r i=e.val.2
    exact r.eq_symm_apply
 theorem bal_code (Δ : ℕ) (e : HeavyAction D H) :
    ActionArrays.bal (view r D H,Δ) (code r D H e)=true ↔ e∈balanced (heavy D H) Δ := by
  unfold ActionArrays.bal
  rw [Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  rw [show (view r D H).2.length=n from sets_length r H,erase_code,sets_card,code_light]
  change (e.isLeft=true ∧ ((heavy D H).erase e).card=Δ) ↔
    e∈((univ.filter (fun e : HeavyAction D H => e.isLeft=true)).filter (fun e => ((heavy D H).erase e).card=Δ))
  simp only [mem_filter,mem_univ,true_and]
 omit [Fintype I] in
 theorem overlap_sets (A B : Finset I) :
    ActionArrays.overlap (sets r A) (sets r B)=true ↔ (A∩B).Nonempty := by
  rw [sets,sets,ActionArrays.overlap_view,← map_inter]
  exact Finset.map_nonempty
 theorem conflict_code (Δ : ℕ) (e f : HeavyAction D H) :
    ActionArrays.conflict (view r D H,Δ) (code r D H e) (code r D H f)=true ↔ f∈conflicts (heavy D H) Δ e := by
  simp only [ActionArrays.conflict,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not,
    bal_code,erase_code,overlap_sets]
  have he : code r D H f≠code r D H e ↔ f≠e :=
    not_congr (@StrictMono.injective _ _ (actionOrder D H) _ _ (code_strictMono r D H)).eq_iff
  simp only [he]
  unfold conflicts
  split_ifs with hb <;> simp only [mem_filter,notMem_empty,iff_false] <;> tauto

 theorem data_view (m : I → ℚ) (p φ : ℚ) (Δ : ℕ) :
    ActionArrays.data ((((p,φ),List.ofFn (fun i => m (r i))),Δ),view r D H)=
    ((setView ((balanced (heavy D H) Δ).map (enumeration D H).symm.toEmbedding),
      List.ofFn (fun i => setView ((conflicts (heavy D H) Δ (enumeration D H i)).map (enumeration D H).symm.toEmbedding))),
      (p,List.ofFn (fun i => RationalBatchData.bias m p φ (heavyParent D H (enumeration D H i))))) := by
  unfold ActionArrays.data
  dsimp only
  rw [codes_eq]
  apply Prod.ext
  · apply Prod.ext
    · dsimp only
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,mem_map_equiv,Equiv.symm_symm,Function.comp_def]
      exact bal_code r D H Δ (enumeration D H i)
    · dsimp only
      simp only [List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,mem_map_equiv,Equiv.symm_symm,Function.comp_def]
      exact conflict_code r D H Δ (enumeration D H i) (enumeration D H j)
  · apply Prod.ext
    · rfl
    · dsimp only
      rw [List.map_ofFn,show (view r D H).2.length=n from sets_length r H]
      apply congrArg List.ofFn
      funext i
      exact bias_code r D H m p φ (enumeration D H i)

end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMixProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly
variable {α A : Type}

 theorem mixData_raw (μ ν : SparseIntegerLaw α) (view : α → A) :
    mixData (((raw μ).1,μ.states.toList.map view),((raw ν).1,ν.states.toList.map view))=
      ((raw (μ.mix ν)).1,(μ.mix ν).states.toList.map view) := by
  have h := bindData_raw (fair) (fun a => if a.val=0 then μ else ν) view
  simpa [mixData,mix,raw,fair,List.ofFn_succ] using h

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
def Input.partData (bal : Bool) (x : Input) : Data Row :=
  (((x.part bal).law.denominator,List.ofFn (x.part bal).law.numerator),
    (x.part bal).states.toList.map SparseGraph.ListOperation.setView)
def Input.result (x : Input) : Data Row :=
  (((law x.Z x.C x.p x.q x.hp x.hq).law.denominator,List.ofFn (law x.Z x.C x.p x.q x.hp x.hq).law.numerator),
    (law x.Z x.C x.p x.q x.hp x.hq).states.toList.map SparseGraph.ListOperation.setView)

end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchProposalProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

def Input.result (x : Input I) : Data Row :=
  (((x.law).law.denominator,List.ofFn (x.law).law.numerator),
    x.law.states.toList.map (fun Z => setView (Z.map x.enumActions.symm.toEmbedding)))

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

end MetricKMedian.RationalBatchData.ProposalProgram
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

def rawColumn (x : InputRaw × ℕ) : Data Row :=
  if x.2 < x.1.2.length then x.1.2[x.2]?.getD ((1,[1]),[])
  else ((1,[1]),[x.1.1.map (fun _ => false)])

theorem rawColumn_eq (c : Context) : rawColumn c.raw=columnRaw (column c) := by
  simp only [rawColumn,Context.raw,Input.raw,List.length_ofFn,List.getElem?_ofFn,column]
  split_ifs with h
  · rfl
  · simp only [columnRaw,SparseIntegerLaw.dirac,Vector.toList_replicate,
      List.map_replicate,List.ofFn_const,ListOperation.setView,Finset.notMem_empty,decide_false]
    rfl

theorem update_view (c : Context) (G : T c) (S : Finset (Fin c.input.n)) :
    ListOperation.nextTable ((c.t,view c G),ListOperation.setView S)=view c (update c G S) := by
  apply List.ext_getElem
  · simp only [ListOperation.nextTable,ListOperation.indices,view,ListOperation.view,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj hj'
    have hjm : j < c.input.m := by simpa only [view,ListOperation.view,List.length_ofFn] using hj'
    simp only [ListOperation.nextTable,ListOperation.indices,view,ListOperation.view,ListOperation.setView,List.getElem_map,
      List.getElem_range,List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hjm,Option.getD_some,update]
    split_ifs <;> rfl

def rawProduct (x : (InputRaw × ℕ) × Data Table) : (InputRaw × ℕ) × Data Table :=
  let p := prodData (x.2,rawColumn x.1)
  (x.1,(p.1,p.2.map (fun z => ListOperation.nextTable ((x.1.2,z.1),z.2))))

theorem rawProduct_eq (x : State) :
    rawProduct (x.ctx.raw,(x.raw view).2)=((x.product).ctx.raw,((x.product).raw view).2) := by
  unfold rawProduct
  rw [rawColumn_eq]
  simp only [Bundle.raw,columnRaw,State.product,prodData,
    states_list,SparseIntegerLaw.prod,Vector.toList_ofFn,List.map_ofFn,List.flatMap_def,
    Function.comp_def,RoundingList.ofFn_product,Context.raw,update_view]
  rfl

noncomputable def productProgram : PolyProgram State.encode State.encode State.product := by
  have hc : Binary.Automatic.Poly rawColumn := by
    unfold rawColumn
    have hm : Binary.Automatic.Poly (fun x : InputRaw × ℕ => x.1.1.map (fun _ => false)) := by
      apply Binary.Automatic.Poly.list_map <;> fun_prop
    fun_prop
  have hp : Binary.Automatic.Poly rawProduct := by
    unfold rawProduct
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.pair
      · fun_prop
      · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact hp.program.recode (fun x => (x.ctx.raw,(x.raw view).2)) (fun _ => rfl)
    (fun x => congrArg Binary.Automatic.enc (rawProduct_eq x))

noncomputable def dimensionsProgram : PolyProgram Context.encode IntegerLaw.BinaryCompression.es
    (fun c => List.replicate (c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m)) ()) :=
  (((fst ei Nat.bits).comp ListOperation.dimensions_poly.program).recode Context.raw (fun _ => rfl)
    (fun c => congrArg _ (ListOperation.dimensions_eq (fun i => columnRaw (c.input.columns i)))))
noncomputable def featuresProgram : PolyProgram (encodePair Context.encode et) IntegerLaw.BinaryCompression.eqr
    (fun x => ListOperation.featureList (x.1.input.raw.1,x.2)) := by
  let p : PolyProgram (encodePair (encodePair ei Nat.bits) et) IntegerLaw.BinaryCompression.eqr
      (fun x : (InputRaw × ℕ) × Table => ListOperation.featureList (x.1.1.1,x.2)) := by
    apply Binary.Automatic.Poly.program
    fun_prop
  exact p.recode (fun x => (x.1.raw,x.2)) (fun _ => rfl) (fun _ => rfl)

noncomputable def incrementProgram : PolyProgram State.encode State.encode State.increment := by
  let old := fst Context.encode (ed et)
  let inp := old.comp ((fst ei Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let t := old.comp ((snd ei Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let inc := (t.fanout (constant _ Nat.bits 1)).comp natAdd
  let law := snd Context.encode (ed et)
  exact ((inp.fanout inc).fanout law).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.MaskProgram.get_view _root_.OAI.MetricKMedian.SparseEnumeratedGraph.mem_lift _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
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

theorem input_bounds (x : Input) :
    x.n≤x.encode.length ∧ x.m≤x.encode.length ∧
    (∀ i, (x.columns i).length≤x.encode.length) ∧
    (∀ i, (x.columns i).law.denominator≤(2:ℤ)^x.encode.length) := by
  let L := x.encode.length
  have he : L=2*(encodeList (fun _ : Unit => []) x.raw.1).length+1+
      (encodeList (ed erB) x.raw.2).length := encodePair_length _ _ _
  have hn := EncodedList.length_le (fun _ : Unit => []) x.raw.1
  have hm := EncodedList.length_le (ed erB) x.raw.2
  simp only [Input.raw,List.length_ofFn,List.length_replicate] at hn hm he
  have hcol (i : Fin x.m) : (ed erB (columnRaw (x.columns i))).length≤L := by
    have h := EncodedList.member_length (ed erB) x.raw.2 (columnRaw (x.columns i))
      (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simp only [Input.raw] at h
    omega
  have hc (i : Fin x.m) : (ed erB (columnRaw (x.columns i))).length=
      2*(2*(Signed.encode (x.columns i).law.denominator).length+1+
        (encodeList Signed.encode (List.ofFn (x.columns i).law.numerator)).length)+1+
      (encodeList erB ((x.columns i).states.toList.map ListOperation.setView)).length := by
    simp only [columnRaw,ed,el,IntegerLaw.ListPivot.el,encodePair_length]
  refine ⟨by change x.n≤L; omega,by change x.m≤L; omega,?_,?_⟩
  · intro i
    have h := EncodedList.length_le Signed.encode (List.ofFn (x.columns i).law.numerator)
    simp only [List.length_ofFn] at h
    have hh := hcol i
    rw [hc i] at hh
    change (x.columns i).length≤L
    omega
  · intro i
    have hh := hcol i
    rw [hc i] at hh
    have hl : (Signed.encode (x.columns i).law.denominator).length≤L := by omega
    exact (le_abs_self _).trans ((Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) hl))

theorem state_size (x : Input) (t : ℕ) (ht : t≤x.m) :
    (State.encode (x.state t)).length≤ sizePolynomial.eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hm,hN,hD⟩ := input_bounds x
  have htL : t≤L := ht.trans hm
  have hc : (Context.encode ⟨x,t⟩).length≤3*L+2 := by
    have hbits : t.bits.length≤t+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
    change (encodePair Input.encode Nat.bits (x,t)).length≤_
    rw [encodePair_length]
    change 2*L+1+t.bits.length≤_
    omega
  have hsupport : (x.state t).law.length≤ supportBound L := by
    apply (run_length x.columns t).trans
    unfold supportBound
    gcongr
  have hheight : SparseGraph.stepHeight x.n x.m L L*t≤heightBound L := by
    unfold heightBound SparseGraph.stepHeight
    dsimp only
    gcongr
  have hden : (x.state t).law.law.denominator≤(2:ℤ)^(heightBound L) :=
    (denominator_height x.columns L L hN hD t).trans (pow_le_pow_right₀ (by norm_num) hheight)
  have hr (S : Finset (Fin x.n)) : (erB (ListOperation.setView S)).length≤3*L := by
    have h := EncodedList.length_bound encodeBool (ListOperation.setView S) 1 (fun _ _ => by rfl)
    simp only [ListOperation.setView,List.length_ofFn] at h
    exact h.trans (by omega)
  have hs (G : Graph x.n x.m) : (et (ListOperation.view G)).length≤graphSize L := by
    have h := EncodedList.length_bound erB (ListOperation.view G) (3*L) (by
      intro row hrow
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
      exact hr (G i))
    simp only [ListOperation.view,List.length_ofFn] at h
    apply h.trans
    unfold graphSize
    gcongr
  have hb := SparseIntegerLaw.encode_length_bound (fun G : Graph x.n x.m => et (ListOperation.view G))
    (run x.columns t) (supportBound L) (heightBound L) (graphSize L) hsupport hden (fun _ => hs _)
  have he : State.encode (x.state t)=encodePair Context.encode
      (SparseIntegerLaw.BinarySparse.encode (fun G : Graph x.n x.m => et (ListOperation.view G)))
        (⟨x,t⟩,run x.columns t) := by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.state,view,
      SparseIntegerLaw.BinarySparse.encode,SparseIntegerLaw.BinarySparse.raw,ed,encodePair,RoundingProgram.encodeList_map]
  rw [sizePolynomial_eval,he,encodePair_length]
  unfold sizeBound
  dsimp only at ⊢
  simp only [L] at hc hb ⊢
  omega

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse

 theorem rawQ_input (x : Input) : rawQ x.raw=x.qInput.raw := by
  simp only [rawQ,Input.raw,List.map_ofFn,Function.comp_def,Taper.ListOperation.sourceRow_list,
    SparseGraph.Program.QInput.raw,Input.qInput,List.ofFn_const]

end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchUpdateProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

local instance instLinearOrderCopyFin_rb7848e_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
def Input.result (x : Input) : Data Row :=
  ((x.law.law.denominator,List.ofFn x.law.law.numerator),x.law.states.toList.map CopyList.view)

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end


