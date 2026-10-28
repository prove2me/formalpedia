-- Prove2me | Definitions.Def_OAIQ035K060
-- name    : OAIQ035K060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:15:51.311918+00:00
-- url     : https://prove2.me/theorems/7e319dfe-3133-47c8-b00c-d7668779455c
-- title:
--   Definitions bundle OAIQ035K060 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 19 definitions and 22 theorems. The definitions and types are `OAI.MetricKMedian.RationalBatchData.Ordinal.view`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.encode`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.result`, `OAI.MetricKMedian.RoundingProgram.compressionInputProgram`, `OAI.MetricKMedian.RoundingProgram.weightsProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.Row`, `OAI.MetricKMedian.SparseBernoulli.Program.rowEndpoint`, `OAI.MetricKMedian.SparseBernoulli.Program.rowProbability`, `OAI.MetricKMedian.SparseCardinalRounding.Program.inputProgram`, `OAI.MetricKMedian.SparseCardinalRounding.Program.result`, `OAI.MetricKMedian.SparseGraph.Program.activeProgram`, `OAI.MetricKMedian.SparseGraph.Program.countProgram`, `OAI.MetricKMedian.SparseGraph.Program.dimensionsProgram`, `OAI.MetricKMedian.SparseGraph.Program.featuresProgram`, `OAI.MetricKMedian.SparseGraph.Program.incrementProgram`, `OAI.MetricKMedian.SparseGraph.Program.productProgram`, `OAI.MetricKMedian.SparseGraph.Program.rawColumn`, `OAI.MetricKMedian.SparseGraph.Program.rawProduct`, `OAI.MetricKMedian.SparseGraph.Program.startProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_BatchOrdinalArrays`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Process_TaperGraphProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_GraphStepProgram`.
--
--   **Imports.** It imports the bundles `OAIQ035K054`, `OAIQ035K055` and `OAIQ035K056` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K065`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K054
import Definitions.Def_OAIQ035K055
import Definitions.Def_OAIQ035K056

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

noncomputable def weightsProgram (s : Bool) :
    PolyProgram State.encode erow (fun x : State s => List.ofFn x.β) :=
  (fst erow (ed erow)).recode State.raw State.encode_raw (fun _ => rfl)

end MetricKMedian.RoundingProgram
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
abbrev Row := ListOperation.Row

def rowProbability (x : Context × Row) : ℚ := x.1.raw.1[x.1.t]?.getD 0
def rowEndpoint (b : Bool) (x : Context × Row) : Row := ListOperation.endpoint x.1.t b x.2

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchOrdinalCodes
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
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchOrdinalArrays
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

 theorem transpose_graph (G : I → Finset I) :
    GraphData.transpose (graphView r G)=List.ofFn (fun h => sets r ((graph G).erase (r h))) := by
  simp only [GraphData.transpose,graphView,indices,List.length_ofFn,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,sets_eq,List.getElem?_ofFn,
    dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,graph,mem_filter,mem_univ,true_and]
 theorem masses_graph (G : I → Finset I) (g : ℚ) :
    GraphData.masses (g,graphView r G)=List.ofFn (fun h => graphMass G g (r h)) := by
  simp only [GraphData.masses,transpose_graph,List.map_ofFn,Function.comp_def,sets_card]
  rfl
 theorem heavy_graph (G : I → Finset I) (g b : ℚ) :
    GraphData.heavy (b,GraphData.masses (g,graphView r G))=sets r (heavySet (graphMass G g) b) := by
  rw [masses_graph]
  simp only [GraphData.heavy,GraphData.amount_view,List.map_ofFn,Function.comp_def,sets_eq,
    heavySet,mem_filter,mem_univ,true_and]
  have ha : RationalBatchData.amount (fun h => graphMass G g (r h))=RationalBatchData.amount (graphMass G g) :=
    r.toEquiv.sum_comp (fun h => max (1-graphMass G g h) 0)
  rw [ha]
 theorem prepare_graph (G : I → Finset I) (g b p φ : ℚ) (Δ : ℕ) :
    GraphData.prepare (((g,b),(Δ,(p,φ))),graphView r G)=
      ((((p,φ),List.ofFn (fun h => graphMass G g (r h))),Δ),view r (graph G) (heavySet (graphMass G g) b)) := by
  unfold GraphData.prepare
  dsimp only
  rw [heavy_graph,masses_graph,transpose_graph]
  rfl
end MetricKMedian.RationalBatchData.Ordinal
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

abbrev Input.encode (x : Input I) := Binary.Automatic.enc x.raw

def Input.result (x : Input I) : Data Row :=
  (((x.law).law.denominator,List.ofFn (x.law).law.numerator),
    x.law.states.toList.map (fun Z => setView (Z.map x.enumActions.symm.toEmbedding)))

 theorem data_input (x : Input I) : GraphData.data x.raw=x.batch.raw := by
  unfold GraphData.data Input.raw
  rw [Ordinal.prepare_graph,Ordinal.data_view]
  rfl
end MetricKMedian.RationalBatchData.ProposalProgram
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
noncomputable def activeProgram : PolyProgram State.encode encodeBool
    (fun x : State => decide (x.ctx.t<x.ctx.input.m)) := by
  let raw : PolyProgram (encodePair ei Nat.bits) encodeBool
      (fun x : InputRaw × ℕ => decide (x.2<x.1.2.length)) := Binary.Automatic.Poly.program (by fun_prop)
  let ctx : PolyProgram Context.encode encodeBool (fun c => decide (c.t < c.input.m)) := raw.recode Context.raw (fun _ => rfl)
    (fun c => by simp only [Context.raw,Input.raw,List.length_ofFn])
  exact (contextProgram Context.encode et view).comp ctx
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

 theorem selectedRow_eq {n : ℕ} (q : Vector ℚ n) :
    selectedRow q.toList=SparseGraph.ListOperation.setView (selected q) := by
  apply List.ext_getElem
  · simp only [selectedRow,List.length_map,Vector.length_toList,SparseGraph.ListOperation.setView,List.length_ofFn]
  · intro i hi hi'
    have hin : i<n := by simpa only [SparseGraph.ListOperation.setView,List.length_ofFn] using hi'
    simp only [selectedRow,List.getElem_map,Vector.getElem_toList,SparseGraph.ListOperation.setView,
      List.getElem_ofFn,selected,Finset.mem_filter,Finset.mem_univ,true_and,RationalWeightedStep.point]

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

 theorem rawQ_input (x : Input) : rawQ x.raw=x.qInput.raw := by
  simp only [rawQ,Input.raw,List.map_ofFn,Function.comp_def,Taper.ListOperation.sourceRow_list,
    SparseGraph.Program.QInput.raw,Input.qInput,List.ofFn_const]

end MetricKMedian.TaperGraphProgram
end

end OAI
end


