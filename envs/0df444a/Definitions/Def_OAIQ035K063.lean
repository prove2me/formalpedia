-- Prove2me | Definitions.Def_OAIQ035K063
-- name    : OAIQ035K063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:16:33.650907+00:00
-- url     : https://prove2.me/theorems/68a01a0c-a638-4f4f-9681-f9c4d8acd712
-- title:
--   Definitions bundle OAIQ035K063 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 19 definitions and 23 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.RationalBundles.Program.view`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Input.encode`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Input.raw`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.State.encode`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.State.raw`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.countProgram`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.program`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.startProgram`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.stepProgram`, `OAI.MetricKMedian.RoundingProgram.SignedRound.boundState`, `OAI.MetricKMedian.RoundingProgram.SignedRound.result`, `OAI.MetricKMedian.RoundingProgram.Terminal.bernoulliInputProgram`, `OAI.MetricKMedian.SparseCounts.Program.dimensionsProgram`, `OAI.MetricKMedian.SparseCounts.Program.featuresProgram`, `OAI.MetricKMedian.SparseCounts.Program.incrementProgram`, `OAI.MetricKMedian.SparseCounts.Program.productProgram`, `OAI.MetricKMedian.SparseCounts.Program.rawColumn`, `OAI.MetricKMedian.SparseCounts.Program.rawProduct`, `OAI.MetricKMedian.SparseTargetSubset.Program.Input.raw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Preparation_RepresentativeProgram`, `KMedian_Process_CountListOperations`, `KMedian_Process_CountRunHeight`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_BundleGeometryProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Rounding_SignedRoundProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Rounding_TargetSubsetProgram`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseTargetSubset`, `KMedian_Sparse_SparseWeightedPartial`, `KMedian_Sparse_SparseWeightedRounding`.
--
--   **Imports.** It imports the bundles `OAIQ035K054`, `OAIQ035K055`, `OAIQ035K056`, `OAIQ035K057` and `OAIQ035K058` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K067`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K054
import Definitions.Def_OAIQ035K055
import Definitions.Def_OAIQ035K056
import Definitions.Def_OAIQ035K057
import Definitions.Def_OAIQ035K058

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseWeightedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

 theorem step_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (μ : SparseIntegerLaw (Vector ℚ n)) (i : Fin n) :
    (step β hβ μ).moment (fun p => point p i)=μ.moment (fun p => point p i) := by
  have hh := μ.step_moment features (probability β) (probability_unit β hβ)
    (endpoint β) (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (μ.moment_congr _ _ (fun a => endpoint_mean β hβ _ i))

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

theorem run_columns (ν : Fin m → SparseIntegerLaw (Finset (Fin n)))
    (P : Fin m → Finset (Fin n) → Prop)
    (hP : ∀ i, ∀ a : Fin (ν i).length, P i (ν i).states[a.val]) (t : ℕ) (ht : t ≤ m) :
    ∀ a : Fin (run ν t).length, ∀ i, i.val<t → P i ((run ν t).states[a.val] i) := by
  induction t with
  | zero => intro a i hi; omega
  | succ t ih =>
    have htm : t < m := by omega
    have he : run ν (t+1)=step (run ν t) (ν ⟨t,htm⟩) ⟨t,htm⟩ := by
      rw [run,dite_eq_left htm]
    let inv : SparseIntegerLaw (Graph n m) → Prop := fun μ =>
      ∀ a : Fin μ.length, ∀ i, i.val<t+1 → P i (μ.states[a.val] i)
    change inv (run ν (t+1))
    rw [he]
    intro a i hi
    obtain ⟨j,k,hjk⟩ := ((run ν t).prodCompress_spec (ν ⟨t,htm⟩)
      (fun G S => next G S ⟨t,htm⟩) features).2.1 a
    change (step (run ν t) (ν ⟨t,htm⟩) ⟨t,htm⟩).states[a.val]=_ at hjk
    rw [hjk]
    by_cases hi' : i=⟨t,htm⟩
    · subst i
      simpa only [next,Function.update_self] using hP ⟨t,htm⟩ k
    · have hiv : i.val≠t := fun h => hi' (Fin.ext h)
      simpa only [next,Function.update_of_ne hi'] using ih (by omega) j i (by omega)

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

def Input.raw (x : Input) : Raw := ((List.ofFn x.R,(List.ofFn (fun i => List.ofFn (x.d i)),x.M)),setView x.U)
def Input.encode (x : Input) : List Bool := enc x.raw
def State.raw (s : State) : Raw × (Row × Row) := (s.input.raw,(setView s.cut.1,setView s.cut.2))
def State.encode (s : State) : List Bool := enc s.raw

 theorem stepRaw_state (s : State) : stepRaw s.raw=(s.step).raw := by
  unfold stepRaw State.raw State.step advance
  rw [any_view]
  by_cases h : s.cut.1.Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,Input.raw,nearest_view s.input.R s.cut.1 h]
    apply Prod.ext
    · rfl
    apply Prod.ext
    · simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,
        dite_eq_left (Preparation.firstNearest _ _ h).isLt,mem_filter,Bool.decide_and]
    · simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_insert,Bool.decide_or]
      rw [Bool.or_comm]
      congr 1
      simp only [Fin.ext_iff]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]

noncomputable def stepProgram : PolyProgram State.encode State.encode State.step :=
  stepRaw_poly.program.recode State.raw (fun _ => rfl) (fun s => congrArg enc (stepRaw_state s))

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  have hp : Poly (fun x : Raw => (x,(x.2,x.2.map (fun _ => false)))) := by
    apply pair
    · fun_prop
    · apply pair
      · fun_prop
      · apply list_map <;> fun_prop
  exact hp.program.recode Input.raw (fun _ => rfl) (fun x => by
    change enc (x.raw,(setView x.U,(setView x.U).map (fun _ => false)))=enc (x.raw,(setView x.U,setView ∅))
    simp only [setView,List.map_ofFn,notMem_empty,decide_false,Function.comp_def]
    rfl)
noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n := by
  have hp : Poly (fun x : Raw => x.2.length) := by fun_prop
  exact hp.program.recode Input.raw (fun _ => rfl) (fun x => by simp only [Input.raw,setView,List.length_ofFn]; rfl)
 theorem input_bound (x : Input) : x.n≤x.encode.length := by
  have hh := EncodedList.length_le encodeBool (setView x.U)
  simp only [setView,List.length_ofFn] at hh
  have he : x.encode.length=2*(enc (x.raw.1)).length+1+(enc x.raw.2).length := encodePair_length _ _ _
  change x.n≤(enc (setView x.U)).length at hh
  change x.encode.length=2*(enc x.raw.1).length+1+(enc (setView x.U)).length at he
  omega
 theorem mask_length {n : ℕ} (U : Finset (Fin n)) : (enc (setView U)).length≤3*n := Completion.Rational.PackingProgram.mask_length U
 theorem state_size (x : Input) (t : ℕ) : (State.encode (x.state t)).length≤11*x.encode.length+2 := by
  have h1 := mask_length ((advance x)^[t] (x.U,∅)).1
  have h2 := mask_length ((advance x)^[t] (x.U,∅)).2
  have hn := input_bound x
  change (encodePair Input.encode (encodePair (encodeList encodeBool) (encodeList encodeBool))
    (x,(setView ((advance x)^[t] (x.U,∅)).1,setView ((advance x)^[t] (x.U,∅)).2))).length≤_
  rw [encodePair_length,encodePair_length]
  dsimp only at ⊢
  change (encodeList encodeBool _).length≤3*x.n at h1 h2
  omega

noncomputable def program : PolyProgram Input.encode (encodeList encodeBool)
    (fun x => setView (select x.d x.R x.M x.n x.U)) := by
  let run := stepProgram.repeatFrom startProgram countProgram X (11*X+2)
    (fun x => by simpa using input_bound x)
    (fun x t _ => by rw [state_iterate]; simpa using state_size x t)
  let out : PolyProgram State.encode (encodeList encodeBool) (fun s => setView s.cut.2) :=
    ((snd enc (encodePair (encodeList encodeBool) (encodeList encodeBool))).comp
      (snd (encodeList encodeBool) (encodeList encodeBool))).recode State.raw (fun _ => rfl) (fun _ => rfl)
  exact (run.comp out).congr _ (fun x => by
    dsimp only [Function.comp_def]
    rw [state_iterate]
    change setView (((advance x)^[x.n] (x.U,∅)).2)=_
    rw [advance_result,empty_union])
end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseCounts.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

 theorem dimensions_eq {n m : ℕ} (cs : Fin m → SparseIntegerLaw.BinarySparse.Data Row) :
    dimensions (List.replicate n (),List.ofFn cs)=List.replicate (n*m+(n*m)*(n*m)) () := by
  have h : (List.replicate n ()).flatMap (fun _ => (List.ofFn cs).map (fun _ => (0:ℚ)))=
      List.ofFn (fun _ : Fin (n*m) => (0:ℚ)) := by
    simp only [List.map_const',List.length_ofFn,List.flatMap_replicate,List.ofFn_const]
    simp [List.flatten_replicate_replicate]
  simp only [dimensions,h,RoundingList.dimensions_list]
end MetricKMedian.SparseCounts.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseCounts
open Binary
variable {n m : ℕ}

theorem run_bound (ν : Fin m → SparseIntegerLaw (Fin n → ℕ)) (U : ℕ)
    (hν : ∀ i, ∀ a : Fin (ν i).length, ∀ h, (ν i).states[a.val] h≤U) (t : ℕ) :
    ∀ a : Fin (run ν t).length, ∀ i h,(run ν t).states[a.val] i h≤U := by
  induction t with
  | zero =>
    intro a i h
    change (Vector.replicate 1 (fun _ : Fin m => fun _ : Fin n => (0:ℕ)))[a.val] i h≤U
    simp only [Vector.getElem_replicate]
    exact Nat.zero_le _
  | succ t ih =>
    let P := fun μ : SparseIntegerLaw (Table n m) => ∀ a : Fin μ.length, ∀ i h,μ.states[a.val] i h≤U
    change P (run ν (t+1))
    rw [run]
    split_ifs with ht
    · intro a i h
      obtain ⟨j,k,hjk⟩ := ((run ν t).prodCompress_spec (ν ⟨t,ht⟩)
        (fun G S => next G S ⟨t,ht⟩) features).2.1 a
      change (step (run ν t) (ν ⟨t,ht⟩) ⟨t,ht⟩).states[a.val]=_ at hjk
      rw [hjk]
      exact next_bound _ _ _ U (ih j) (hν _ k) i h
    · exact ih

end MetricKMedian.SparseCounts
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

def rawColumn (x : InputRaw × ℕ) : Data Row :=
  if x.2 < x.1.2.length then x.1.2[x.2]?.getD ((1,[1]),[])
  else ((1,[1]),[x.1.1.map (fun _ => 0)])

theorem rawColumn_eq (c : Context) : rawColumn c.raw=columnRaw (column c) := by
  simp only [rawColumn,Context.raw,Input.raw,List.length_ofFn,List.getElem?_ofFn,column]
  split_ifs with h
  · rfl
  · simp only [columnRaw,SparseIntegerLaw.dirac,Vector.toList_replicate,
      List.map_replicate,List.ofFn_const,ListOperation.setView]
    rfl

theorem update_view (c : Context) (G : T c) (S : (Fin c.input.n → ℕ)) :
    ListOperation.nextTable ((c.t,view c G),ListOperation.setView S)=view c (update c G S) := by
  apply List.ext_getElem
  · simp only [ListOperation.nextTable,ListOperation.indices,view,ListOperation.view,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj hj'
    have hjm : j < c.input.m := by simpa only [view,ListOperation.view,List.length_ofFn] using hj'
    simp only [ListOperation.nextTable,ListOperation.indices,view,ListOperation.view,ListOperation.setView,List.getElem_map,
      List.getElem_range,List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hjm,Option.getD_some,update]
    split_ifs <;> rfl

def rawProduct (x : (InputRaw × ℕ) × Data ListOperation.Table) : (InputRaw × ℕ) × Data ListOperation.Table :=
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
    have hm : Binary.Automatic.Poly (fun x : InputRaw × ℕ => x.1.1.map (fun _ => 0)) := by
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
      (fun x : (InputRaw × ℕ) × ListOperation.Table => ListOperation.featureList (x.1.1.1,x.2)) := by
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
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BundleGeometryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalBundles.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
def view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) : Raw :=
  ((List.ofFn (fun i => List.ofFn (d i)),List.ofFn (fun i => List.ofFn (di i))),
    (List.ofFn (fun i => setView (F i)),List.ofFn y))
 theorem neighborMask_view {n : ℕ} (ds : Fin n → ℚ) (t : Fin n) :
    neighborMask (List.ofFn ds,t.val)=setView (univ.erase t) := by
  simp only [neighborMask,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,setView,mem_erase,mem_univ,and_true]
  simp only [ne_eq,Fin.val_inj]
 theorem nextData_view {n : ℕ} (d : Fin n → Fin n → ℚ) (t : Fin n) :
     nextData (List.ofFn (d t),t.val)=(next d t).val := by
  unfold nextData
  rw [neighborMask_view,Completion.Rational.PackingProgram.any_view]
  simp only [decide_eq_true_eq]
  unfold next
  split_ifs with h
  · rw [MetricKMedian.MaskProgram.nearest_view]
  · rfl

 theorem bundleData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) (t : Fin n) :
    bundleData δ (view d di F y,t.val)=setView (bundle d di F δ t) := by
  simp only [bundleData,view,List.getElem?_ofFn,dite_eq_left t.isLt,Option.getD_some,Fin.eta,nextData_view]
  by_cases h : next d t=t
  · simp only [h,ite_true,bundle]
  · have hn : (next d t).val≠t.val := fun hh => h (Fin.ext hh)
    simp only [hn,ite_false,bundle,h,indices,List.length_ofFn,RoundingList.range_finRange,
      ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,
      dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,setView,mem_filter,Bool.decide_and]

 theorem bundlesData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) :
    bundlesData δ (view d di F y)=List.ofFn (fun t => setView (bundle d di F δ t)) := by
  unfold bundlesData
  simp only [view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change List.ofFn (fun t : Fin n => bundleData δ (view d di F y,t.val))=_
  simp only [bundleData_view]

 theorem missingData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) :
    missingData δ (view d di F y)=List.ofFn (fun t => setView (missing d di F δ t)) := by
  unfold missingData
  simp only [view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change List.ofFn (fun t : Fin n => List.ofFn (fun a : Fin f => MetricKMedian.MaskProgram.get ((List.ofFn (fun t => setView (F t)))[t.val]?.getD []) a.val && !MetricKMedian.MaskProgram.get (bundleData δ (view d di F y,t.val)) a.val))=_
  simp only [bundleData_view,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,missing,mem_sdiff,Bool.decide_and,decide_not]

 theorem massData_view {f n : ℕ} (y : Fin f → ℚ) (P : Fin n → Finset (Fin f)) :
    massData (List.ofFn y,List.ofFn (fun t => setView (P t)))=List.ofFn (mass y P) := by
  simp only [massData,List.map_ofFn,Function.comp_def,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,Fin.eta,decide_eq_true_eq,List.sum_ofFn,← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rfl
end MetricKMedian.Preparation.RationalBundles.Program
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

theorem round_invariants (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    {M : ℚ} (hM : 0 ≤ M) (hβM : ∀ i, β i ≤ M) :
    ∀ a : Fin (round β hβ p).length,
      let q := (round β hβ p).states[a.val]
      (∀ i, point q i=0 ∨ point q i=1) ∧
      |(∑ i, β i*point q i)-(∑ i, β i*point p i)| ≤ M := by
  apply (run β hβ p n).step_property features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint
    (fun q => (∀ i, point q i=0 ∨ point q i=1) ∧
      |(∑ i, β i*point q i)-(∑ i, β i*point p i)| ≤ M)
  intro a b
  obtain ⟨ha,hb,hc⟩ := run_invariants β hβ p hp n a
  have hc' : (fractional (run β hβ p n).states[a.val]).card ≤ 1 := by simpa using hc
  refine ⟨RationalLastFraction.endpoint_integral _ ha hc' b,?_⟩
  have hh := RationalLastFraction.endpoint_noise (run β hβ p n).states[a.val] β
    (fun k => (hβ k).le) hβM hM b
  rwa [hb] at hh

end MetricKMedian.SparseWeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_LastFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList.Last
open Binary Binary.Automatic Binary.Automatic.Poly Finset

 theorem active_list {n : ℕ} (p : Vector ℚ n) : active p.toList=decide (RationalWeightedStep.fractional p).Nonempty := by
  simp only [active,fractional_list,List.length_map,Finset.length_sort,card_pos]
 theorem first_list {n : ℕ} (p : Vector ℚ n) (h : (RationalWeightedStep.fractional p).Nonempty) :
    first p.toList=(RationalLastFraction.pick p h).val := by
  unfold first indices
  rw [Vector.length_toList]
  apply findIdx_min _ h
  intro i
  simp [frac,RationalWeightedStep.fractional,RationalWeightedStep.point]

 theorem probability_list {n : ℕ} (p : Vector ℚ n) : probability p.toList=RationalLastFraction.probability p := by
  unfold probability RationalLastFraction.probability
  rw [active_list]
  by_cases h : (RationalWeightedStep.fractional p).Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,first_list p h,List.getElem?_eq_getElem
      (show (RationalLastFraction.pick p h).val<p.toList.length by simp),
      Option.getD_some,Vector.getElem_toList,RationalWeightedStep.point]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]

 theorem endpoint_list {n : ℕ} (p : Vector ℚ n) (b : Fin 2) : endpoint (decide (b=1)) p.toList=(RationalLastFraction.endpoint p b).toList := by
  unfold endpoint RationalLastFraction.endpoint
  rw [active_list]
  by_cases h : (RationalWeightedStep.fractional p).Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,first_list p h,indices,Vector.length_toList,range_finRange,
      ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,Vector.toList_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_inj,List.getElem?_eq_getElem (show i.val<p.toList.length by simp),Option.getD_some,Vector.getElem_toList,RationalWeightedStep.point]
    fin_cases b <;> simp
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]
end MetricKMedian.RoundingList.Last

end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

noncomputable def bernoulliInputProgram : PolyProgram Input.encode SparseBernoulli.Program.Input.encode bernoulliInput :=
  (snd erow erow).recode Input.raw (fun _ => rfl) (fun x => by
    change erow x.p.toList=erow (List.ofFn (RationalWeightedStep.point x.p))
    rw [point_toList])

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

def boundState (x : Input true) : State true :=
  ⟨x.n,x.β,x.positive,(SparseSignedPartial.run x.β x.p x.n).bindIndexed (SparseSignedRounding.kernel x.β x.p x.feasible)⟩
def result (x : Input true) : State true :=
  ⟨x.n,x.β,x.positive,SparseSignedRounding.round x.β x.p x.feasible⟩

end SignedRound
end MetricKMedian.RoundingProgram
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

theorem integral (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (vectors D q).length) : ∀ i, point (vectors D q).states[a.val] i=0 ∨
      point (vectors D q).states[a.val] i=1 :=
  (SparseWeightedRounding.round_invariants (fun _ => 1) (fun _ => by norm_num)
    (initial D q) (initial_unit D hq) (show (0:ℚ) ≤ 1 by norm_num) (fun _ => le_rfl) a).1

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_TargetSubsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
def Input.raw (x : Input) : Raw := (setView x.D,x.q)
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end


