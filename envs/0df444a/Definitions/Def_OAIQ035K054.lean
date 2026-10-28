-- Prove2me | Definitions.Def_OAIQ035K054
-- name    : OAIQ035K054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:09:45.321419+00:00
-- url     : https://prove2.me/theorems/d3fc60bd-22e7-4ec5-9be0-847e50b41812
-- title:
--   Definitions bundle OAIQ035K054 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 78 declarations of OpenAI's Lean: 39 definitions and 39 theorems. The definitions and types are `OAI.MetricKMedian.Completion.Rational.MaskOperations.firstCopy`, `OAI.MetricKMedian.Completion.Rational.MaskOperations.integralRaw`, `OAI.MetricKMedian.Completion.Rational.MaskOperations.uncoveredRaw`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.Input.encode`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.Input.raw`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.State.encode`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.State.raw`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.countProgram`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.program`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.startProgram`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.stepProgram`, `OAI.MetricKMedian.Completion.Rational.Program.Input.encode`, `OAI.MetricKMedian.Completion.Rational.Program.Input.raw`, `OAI.MetricKMedian.Completion.Rational.Program.Raw`, `OAI.MetricKMedian.Completion.Rational.Program.finish`, `OAI.MetricKMedian.Completion.Rational.Program.packInputProgram`, `OAI.MetricKMedian.Completion.Rational.Program.packRaw`, `OAI.MetricKMedian.Completion.Rational.Program.program`, `OAI.MetricKMedian.CopyState.CountsProgram.mask`, `OAI.MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram.distances`, `OAI.MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram.nearestRaw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram.radiusRaw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Raw`, `OAI.MetricKMedian.MaskProgram.radius`, `OAI.MetricKMedian.Preparation.RationalNearest.MaskProgram.erase`, `OAI.MetricKMedian.Preparation.RationalNearest.MaskProgram.insert`, `OAI.MetricKMedian.Preparation.RationalNearest.MaskProgram.raw`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.prepare`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.view`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.Raw`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.TransitionRaw`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.next`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.pick`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.transition`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.Raw`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.endpoint`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.featureList`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.value`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Probability_BernoulliListOperations`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyListEncoding`, `KMedian_Process_CopyNearestProgram`, `KMedian_Process_CopyNextProgram`, `KMedian_Process_CountsMaskProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_TaperGraphProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_FinsetMaskProgram`, `KMedian_Programs_GreedyPackingProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_MaximumProgram`, `KMedian_Programs_NearestMaskProgram`, `KMedian_Reduction_CompletionMaskProgram`, `KMedian_Reduction_CompletionProgram`.
--
--   **Imports.** It imports the bundles `OAIQ035K050` and `OAIQ035K051` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K059`, `OAIQ035K060`, `OAIQ035K061` and `OAIQ035K063`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K050
import Definitions.Def_OAIQ035K051

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
def value (d : ℕ) (q : Row) (j : ℕ) : ℚ := if (tests d q j).all id then 1 else 0
def featureList (d : ℕ) (q : Row) : List ℚ :=
  (List.range (units d q).length).map (value d q)

@[fun_prop] theorem tests_poly (d : ℕ) : Poly (fun x : Row × ℕ => tests d x.1 x.2) := by
  apply fixed_map
  intro a ha
  have hp : Poly (fun q : Row => (q.length+1)^a) := comp (nat_pow a) (by fun_prop)
  fun_prop
@[fun_prop] theorem value_poly (d : ℕ) : Poly (fun x : Row × ℕ => value d x.1 x.2) := by
  unfold value
  fun_prop
@[fun_prop] theorem featureList_poly (d : ℕ) : Poly (featureList d) := by
  apply list_map
  · exact comp (value_poly d) (by fun_prop)
  · exact comp (f:=fun xs : List Unit => List.range xs.length) (g:=units d) list_indices (units_poly d)

 def endpoint (t : ℕ) (b : Bool) (q : Row) : Row :=
   (List.range q.length).map (fun i => if i=t then b else q[i]?.getD false)
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (fun x : ℕ × Row => endpoint x.1 b x.2) := by
  apply list_map
  · fun_prop
  · exact comp (f:=fun xs : Row => List.range xs.length) (g:=Prod.snd) list_indices snd

end MetricKMedian.SparseBernoulli.ListOperation
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

def view (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : Row := setView (A.map finProdFinEquiv.toEmbedding)

end MetricKMedian.RationalPhysicalKernel.CopyList
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
@[fun_prop] theorem selectedRow_poly : Binary.Automatic.Poly selectedRow := by
  unfold selectedRow
  apply Binary.Automatic.Poly.list_map <;> fun_prop
end MetricKMedian.SparseCardinalRounding.Program
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
@[fun_prop] theorem rawQ_poly : Poly rawQ := by
  unfold rawQ
  apply Poly.pair
  · apply list_map <;> fun_prop
  · apply list_map <;> fun_prop

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

def prepare (x : Raw) : TaperGraphProgram.Raw :=
  (x.1.1,(active x.2).map (fun a =>
    ((active x.2).map (fun b => ((x.1.2[a/x.1.1.2]?.getD [])[b/x.1.1.2]?.getD 0)),
     (active x.2).map (fun b => decide (b/x.1.1.2=a/x.1.1.2)))))
@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply pair
  · fun_prop
  · apply list_map
    · apply pair <;> (apply list_map <;> fun_prop)
    · fun_prop

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_FinsetMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)

 theorem intersect_view {n : ℕ} (s t : Finset (Fin n)) : intersect (setView s,setView t)=decide (¬Disjoint s t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [intersect,setView,Gaussian.ListOperation.zip_ofFn,List.any_eq_true,List.mem_ofFn,
    Bool.and_eq_true,decide_eq_true_eq,Finset.not_disjoint_iff]
  constructor
  · rintro ⟨z,⟨i,rfl⟩,hs,ht⟩
    exact ⟨i,of_decide_eq_true hs,of_decide_eq_true ht⟩
  · rintro ⟨i,hs,ht⟩
    exact ⟨_,⟨i,rfl⟩,decide_eq_true hs,decide_eq_true ht⟩

 theorem nearest_view {n : ℕ} (R : Fin n → ℚ) (U : Finset (Fin n)) (hU : U.Nonempty) :
    nearest (List.ofFn R,setView U)=(Preparation.firstNearest U R hU).val := by
  let a := Preparation.firstNearest U R hU
  have hm : LPBinary.minimum (selectedValues (List.ofFn R,setView U))=R a :=
    (LPBinary.minimum_eq_finset _ _ (hU.image _) (selectedValues_mem R U)).trans
      (LPBinary.firstNearest_value U R hU).symm
  unfold nearest
  dsimp only
  unfold indices
  rw [show (setView U).length=n from by simp only [setView,List.length_ofFn]]
  change (List.range n).findIdx (fun i => get (setView U) i &&
    decide ((List.ofFn R)[i]?.getD 0=LPBinary.minimum (selectedValues (List.ofFn R,setView U))))=a.val
  rw [hm]
  apply (List.findIdx_eq (by simpa only [List.length_range] using a.isLt)).mpr
  refine ⟨?_,?_⟩
  · simp only [List.getElem_range,get,setView,List.getElem?_ofFn,dite_eq_left a.isLt,Option.getD_some,Fin.eta,
      decide_true,Bool.and_true,decide_eq_true_eq]
    exact (Preparation.firstNearest_spec U R hU).1
  · intro k hk
    have hkn : k<n := hk.trans a.isLt
    simp only [List.getElem_range,get,setView,List.getElem?_ofFn,dite_eq_left hkn,Option.getD_some]
    apply Bool.eq_false_iff.mpr
    intro h
    have hh : decide ((⟨k,hkn⟩ : Fin n)∈U)=true ∧ decide (R ⟨k,hkn⟩=R a)=true := by simpa only [Bool.and_eq_true] using h
    have hle := LPBinary.firstNearest_le U R hU ⟨k,hkn⟩ (of_decide_eq_true hh.1) (of_decide_eq_true hh.2)
    exact (not_le_of_gt hk) hle
end MetricKMedian.MaskProgram
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
@[fun_prop] theorem maximum_poly : Poly maximum :=
  ⟨(((identity (encodeList Ratio.encode)).fanout (listHead Ratio.encode 0)).comp maxFold).congr _ (fun _ => rfl)⟩
def radius (x : List ℚ × Row) := maximum (selectedValues x)
@[fun_prop] theorem radius_poly : Poly radius := by unfold radius; fun_prop
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GreedyPackingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Completion.Rational.PackingProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

def Input.raw (x : Input) : Raw := ((List.ofFn x.R,List.ofFn (fun i => setView (x.B i))),setView x.U)
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
      change (decide (i∈s.cut.1) && !(intersect (setView (s.input.B (Preparation.firstNearest s.cut.1 s.input.R h)),setView (s.input.B i)))) = _
      rw [intersect_view]
      simp
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
 theorem mask_length {n : ℕ} (U : Finset (Fin n)) : (enc (setView U)).length≤3*n := by
  have h := EncodedList.length_bound encodeBool (setView U) 1 (fun _ _ => by rfl)
  simpa only [setView,List.length_ofFn,enc,Coding.encode,Nat.reduceMul,Nat.reduceAdd,Nat.mul_comm] using h
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
    (fun x => setView (packing x.n x.U x.R x.B)) := by
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
end MetricKMedian.Completion.Rational.PackingProgram
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

def erase (x : ℕ × Row) : Row := (indices x.2).map (fun i => MetricKMedian.MaskProgram.get x.2 i && decide (i≠x.1))
def insert (x : ℕ × Row) : Row := (indices x.2).map (fun i => MetricKMedian.MaskProgram.get x.2 i || decide (i=x.1))
@[fun_prop] theorem erase_poly : Poly erase := by
  unfold erase
  simp only [decide_not]
  apply list_map <;> fun_prop
@[fun_prop] theorem insert_poly : Poly insert := by unfold insert; apply list_map <;> fun_prop

def raw : ℕ → List ℚ × Row → Row
  | 0,x => x.2.map (fun _ => false)
  | k+1,x => if x.2.any id then
      let a := MetricKMedian.MaskProgram.nearest x
      insert (a,raw k (x.1,erase (a,x.2)))
    else x.2.map (fun _ => false)
@[fun_prop] theorem raw_poly (k : ℕ) : Poly (raw k) := by
  induction k with
  | zero => change Poly (fun x : List ℚ × Row => x.2.map (fun _ => false)); apply list_map <;> fun_prop
  | succ k ih =>
    change Poly (fun x : List ℚ × Row => if x.2.any id then
      insert (MetricKMedian.MaskProgram.nearest x,raw k (x.1,erase (MetricKMedian.MaskProgram.nearest x,x.2)))
      else x.2.map (fun _ => false))
    fun_prop
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

def distances (Δ : ℕ) (x : List ℚ × Row) : List ℚ := (indices x.2).map (fun k => x.1[k/Δ]?.getD 0)
@[fun_prop] theorem distances_poly (Δ : ℕ) : Poly (distances Δ) := by unfold distances; apply list_map <;> fun_prop
 theorem distances_view {f Δ : ℕ} (d : Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    distances Δ (List.ofFn d,view A)=List.ofFn (fun k : Fin (f*Δ) => d (finProdFinEquiv.symm k).1) := by
  simp only [distances,indices,view,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  have hk : k.val/Δ=(finProdFinEquiv.symm k).1.val := by
    simpa only [rank,Equiv.apply_symm_apply] using CopyGraphProgram.rank_owner (finProdFinEquiv.symm k)
  simp only [Function.comp_def,hk,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

def nearestRaw (Δ : ℕ) (x : List ℚ × Row) : Row :=
  Preparation.RationalNearest.MaskProgram.raw Δ (distances Δ x,x.2)
@[fun_prop] theorem nearestRaw_poly (Δ : ℕ) : Poly (nearestRaw Δ) := by unfold nearestRaw; fun_prop

def radiusRaw (Δ : ℕ) (x : List ℚ × Row) : ℚ :=
  MetricKMedian.MaskProgram.radius (distances Δ x,nearestRaw Δ x)
@[fun_prop] theorem radiusRaw_poly (Δ : ℕ) : Poly (radiusRaw Δ) := by unfold radiusRaw; fun_prop
end MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
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

def pick (x : List ℕ × Row) : List ℕ := ((x.1.zip x.2).filter Prod.snd).map Prod.fst
@[fun_prop] theorem pick_poly : Poly pick := by
  unfold pick
  apply list_map
  · fun_prop
  · apply list_filter <;> fun_prop

abbrev Raw := (ℕ × Row) × (Row × Row)
def next (x : Raw) : Row := (indices x.1.2).map fun k =>
  (x.1.2[k]?.getD false && !natMember (pick (active x.1.2,x.2.1),k)) ||
    natMember ((pick (active x.1.2,x.2.2)).map (fun j => j/x.1.1),k/x.1.1)
@[fun_prop] theorem next_poly : Poly next := by
  unfold next
  have hp : Poly (fun x : Raw => (pick (active x.1.2,x.2.2)).map (fun j => j/x.1.1)) := by
    apply list_map <;> fun_prop
  apply list_map <;> fun_prop

 theorem view_get {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (k : Fin (f*Δ)) :
    (_root_.OAI.MetricKMedian.RationalPhysicalKernel.CopyList.view A)[k.val]?.getD false=decide (finProdFinEquiv.symm k∈A) := by
  simp only [_root_.OAI.MetricKMedian.RationalPhysicalKernel.CopyList.view,setView,List.getElem?_ofFn,dite_eq_left k.isLt,Option.getD_some,Fin.eta,mem_map_equiv]

 theorem view_eq {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    _root_.OAI.MetricKMedian.RationalPhysicalKernel.CopyList.view A=List.ofFn (fun k : Fin (f*Δ) => decide (finProdFinEquiv.symm k∈A)) := by
  simp only [_root_.OAI.MetricKMedian.RationalPhysicalKernel.CopyList.view,setView,mem_map_equiv]

abbrev TransitionRaw := (ℕ × Row) × RationalBatchData.ActionTransition.Raw
def transition (x : TransitionRaw) : Row :=
  next (x.1,(RationalBatchData.ActionTransition.dead x.2,RationalBatchData.ActionTransition.sources x.2))
@[fun_prop] theorem transition_poly : Poly transition := by unfold transition; fun_prop

end MetricKMedian.RationalPhysicalKernel.CopyNext
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountsMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.CopyState.CountsProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open RationalPhysicalKernel.CopyList

def mask (Δ : ℕ) (ns : List ℕ) : Row :=
  (indices ns).flatMap (fun i => (List.range Δ).map (fun s => decide (s<ns[i]?.getD 0)))
@[fun_prop] theorem mask_poly (Δ : ℕ) : Poly (mask Δ) := by
  unfold mask
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop
 theorem mask_view {f Δ : ℕ} (n : Fin f → ℕ) (hn : ∀ i, n i≤Δ) :
    mask Δ (List.ofFn n)=view (activeSlots n hn) := by
  simp only [mask,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,
    Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,
    List.flatMap_def]
  unfold view setView
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext s
  have he : (⟨i.val*Δ+s.val,by have hi := Nat.mul_le_mul_right Δ (Nat.succ_le_of_lt i.isLt); have hs := s.isLt; nlinarith⟩ : Fin (f*Δ))=rank (i,s) := by
    apply Fin.ext
    change i.val*Δ+s.val=s.val+Δ*i.val
    ac_rfl
  simp only [he,rank,mem_map_equiv,Equiv.symm_apply_apply]
  congr 1
  apply propext
  constructor
  · intro hs
    exact mem_image.mpr ⟨⟨i,⟨s.val,hs⟩⟩,mem_univ _,by rfl⟩
  · intro hs
    obtain ⟨⟨a,t⟩,_,ht⟩ := mem_image.mp hs
    have hi : a=i := congrArg Prod.fst ht
    subst a
    have ht' : t.val=s.val := congrArg (fun x : Copy (F:=Fin f) Δ => x.2.val) ht
    exact ht' ▸ t.isLt
end MetricKMedian.CopyState.CountsProgram
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

abbrev Raw := CopyGraphProgram.Raw × (ℚ × (ℚ × ℚ))
end MetricKMedian.RationalPhysicalKernel.RoundProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Completion.Rational.MaskOperations
open Finset CopyState Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram RationalPhysicalKernel.CopyList

def integralRaw (Δ : ℕ) (x : List Unit × Row) : Row :=
  (indices x.1).map (fun i => !((List.range Δ).map (fun k => !MaskProgram.get x.2 (k+Δ*i))).any id)
@[fun_prop] theorem integralRaw_poly (Δ : ℕ) : Poly (integralRaw Δ) := by
  unfold integralRaw
  apply list_map
  · apply comp bool_not
    apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
 theorem integralRaw_view {f Δ : ℕ} (A : Finset (Copy (F:=Fin f) Δ)) :
    integralRaw Δ (List.replicate f (),view A)=setView (integral Δ A) := by
  unfold integralRaw
  simp only [indices,List.length_replicate,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  unfold setView
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true_eq_eq_false,List.any_eq_false,decide_eq_true_eq,mem_integral]
  constructor
  · intro h a ha
    have haf : a.1=i := (mem_slots Δ i a).mp ha
    have hk : ¬(!MaskProgram.get (view A) (a.2.val+Δ*i.val))=true := by
      intro hh
      exact h _ (List.mem_ofFn.mpr ⟨a.2,rfl⟩) hh
    have hb : MaskProgram.get (view A) (rank a).val=true := by
      change MaskProgram.get (view A) (a.2.val+Δ*a.1.val)=true
      rw [haf]
      cases he : MaskProgram.get (view A) (a.2.val+Δ*i.val) <;> simp_all
    unfold MaskProgram.get at hb
    rw [RationalPhysicalKernel.CopyNext.view_get] at hb
    simpa only [rank,Equiv.symm_apply_apply,decide_eq_true_eq] using hb
  · intro h b hb hbad
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
    let a : Copy (F:=Fin f) Δ := (i,k)
    have ha : a∈A := h ((mem_slots Δ i a).mpr rfl)
    have hv : MaskProgram.get (view A) (k.val+Δ*i.val)=true := by
      change MaskProgram.get (view A) (rank a).val=true
      unfold MaskProgram.get
      rw [RationalPhysicalKernel.CopyNext.view_get]
      simpa only [Fin.eta,rank,Equiv.symm_apply_apply,decide_eq_true_eq] using ha
    rw [hv] at hbad
    cases hbad

def uncoveredRaw (x : (List (List ℚ) × List ℚ) × Row) : Row :=
  (indices x.1.2).map (fun c => !((indices x.2).map (fun i =>
    MaskProgram.get x.2 i && decide ((x.1.1[c]?.getD [])[i]?.getD 0≤5*(x.1.2[c]?.getD 0)))).any id)
@[fun_prop] theorem uncoveredRaw_poly : Poly uncoveredRaw := by
  unfold uncoveredRaw
  apply list_map
  · apply comp bool_not
    apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
 theorem uncoveredRaw_view {f j Δ : ℕ} (d : Fin j → Fin f → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F:=Fin f) Δ)) :
    uncoveredRaw ((List.ofFn (fun c => List.ofFn (d c)),List.ofFn R),setView (integral Δ A))=
      setView (uncovered d R A) := by
  unfold uncoveredRaw
  simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext c
  apply Bool.eq_iff_iff.mpr
  simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left c.isLt,Option.getD_some,Fin.eta,
    Bool.not_eq_true_eq_eq_false,List.any_eq_false,decide_eq_true_eq,
    uncovered,mem_filter,mem_univ,true_and]
  constructor
  · intro h hh
    obtain ⟨i,hi,hd⟩ := hh
    apply h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,id_eq,Bool.and_eq_true,decide_eq_true_eq] using And.intro hi hd
  · intro h b hb hh
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    apply h
    simp only [dite_eq_left i.isLt,Option.getD_some,id_eq,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact ⟨i,hh⟩

def firstCopy (b : Row) : ℕ := b.findIdx id
@[fun_prop] theorem firstCopy_poly : Poly firstCopy := ⟨Binary.PolyProgram.listFindIdx (Binary.PolyProgram.identity _) false⟩
 attribute [local instance] OAI.MetricKMedian.Completion.Rational.MaskOperations.instLinearOrderCopyFin
theorem firstCopy_view {f Δ : ℕ} (B : Finset (Copy (F:=Fin f) Δ)) (hB : B.Nonempty) :
    firstCopy (view B)=(rank (B.min' hB)).val := by
  have ha := min'_mem B hB
  unfold firstCopy
  rw [RationalPhysicalKernel.CopyNext.view_eq]
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using (rank (B.min' hB)).isLt)).mpr
  constructor
  · simp only [List.getElem_ofFn,id_eq]
    simpa only [Fin.eta,rank,Equiv.symm_apply_apply,decide_eq_true_eq] using ha
  · intro k hk
    have hkn : k<f*Δ := hk.trans (rank (B.min' hB)).isLt
    simp only [List.getElem_ofFn,id_eq]
    change decide (finProdFinEquiv.symm ⟨k,hkn⟩∈B)=false
    rw [decide_eq_false_iff_not]
    intro hb
    have hr :=
      @StrictMono.monotone _ _ (RationalPhysicalKernel.copyOrder (F:=Fin f) (Δ:=Δ)).toPartialOrder _ _
        RationalPhysicalKernel.CopyList.rank_strictMono
    have hm := hr (B.min'_le _ hb)
    have hm' : (rank (B.min' hB)).val≤k := by
      simpa only [rank,Equiv.apply_symm_apply,Fin.le_def] using hm
    omega

end MetricKMedian.Completion.Rational.MaskOperations
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Completion.Rational.Program
open Finset CopyState Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram MaskOperations RationalPhysicalKernel.CopyList
abbrev Raw := List Unit × ((List (List ℚ) × List ℚ) × (Table × Row))
def Input.raw {Δ : ℕ} (x : Input Δ) : Raw :=
  (List.replicate x.f (),((List.ofFn (fun c => List.ofFn (x.d c)),List.ofFn x.R),
    (List.ofFn (fun c => view (x.B c)),view x.A)))
def Input.encode {Δ : ℕ} (x : Input Δ) : List Bool := enc x.raw
def packRaw (Δ : ℕ) (x : Raw) : PackingProgram.Raw :=
  ((x.2.1.2,x.2.2.1),uncoveredRaw (x.2.1,integralRaw Δ (x.1,x.2.2.2)))
@[fun_prop] theorem packRaw_poly (Δ : ℕ) : Poly (packRaw Δ) := by unfold packRaw; fun_prop
 theorem packRaw_input {Δ : ℕ} (x : Input Δ) : packRaw Δ x.raw=x.packing.raw := by
  unfold packRaw Input.raw
  dsimp only
  rw [integralRaw_view,uncoveredRaw_view]
  rfl
noncomputable def packInputProgram (Δ : ℕ) : PolyProgram (Input.encode (Δ:=Δ)) PackingProgram.Input.encode Input.packing :=
  (packRaw_poly Δ).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (packRaw_input x))

def finish (Δ : ℕ) (x : Raw × Row) : Row := (indices x.1.1).map (fun i =>
  MaskProgram.get (integralRaw Δ (x.1.1,x.1.2.2.2)) i ||
    ((indices x.2).map (fun c => MaskProgram.get x.2 c && decide (firstCopy (x.1.2.2.1[c]?.getD []) / Δ=i))).any id)
@[fun_prop] theorem finish_poly (Δ : ℕ) : Poly (finish Δ) := by
  unfold finish
  apply list_map
  · have ha : Poly (fun x : (Raw × Row) × ℕ =>
        ((indices x.1.2).map (fun c => MaskProgram.get x.1.2 c &&
          decide (firstCopy (x.1.1.2.2.1[c]?.getD []) / Δ=x.2))).any id) := by
      apply comp bool_any
      apply list_map <;> fun_prop
    exact comp bool_or (pair (list_getD_comp false (by fun_prop) (by fun_prop)) ha)
  · fun_prop
 local instance instLinearOrderCopyFin_r498b10_1 {f Δ : ℕ} : LinearOrder (Copy (F:=Fin f) Δ) := RationalPhysicalKernel.copyOrder
theorem finish_input {Δ : ℕ} (x : Input Δ) :
    finish Δ (x.raw,setView (packing x.j x.packing.U x.packing.R x.packing.B))=
      setView (output x.d x.R x.A x.B x.hB) := by
  have hp := packing_map finProdFinEquiv.toEmbedding x.j (uncovered x.d x.R x.A) x.R x.B
  change finish Δ (x.raw,setView (packing x.j (uncovered x.d x.R x.A) x.R
    (fun c => (x.B c).map finProdFinEquiv.toEmbedding)))=_
  rw [hp]
  let C := packing x.j (uncovered x.d x.R x.A) x.R x.B
  change finish Δ (x.raw,setView C)=_
  unfold finish Input.raw
  dsimp only
  rw [integralRaw_view]
  simp only [List.length_replicate,indices,setView,List.length_ofFn,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,
    Bool.or_eq_true,List.any_eq_true,List.mem_ofFn,id_eq,decide_eq_true_eq,output,mem_union,mem_image]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨b,⟨c,rfl⟩,hc⟩
    simp only [dite_eq_left c.isLt,Option.getD_some,firstCopy_view (x.B c) (x.hB c),
      RationalPhysicalKernel.CopyGraphProgram.rank_owner,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact ⟨c,hc.1,Fin.ext hc.2⟩
  · rintro ⟨c,hc,he⟩
    refine ⟨_,⟨c,rfl⟩,?_⟩
    simp only [dite_eq_left c.isLt,Option.getD_some,firstCopy_view (x.B c) (x.hB c),
      RationalPhysicalKernel.CopyGraphProgram.rank_owner,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hc,congrArg Fin.val he⟩

noncomputable def program (Δ : ℕ) : PolyProgram (Input.encode (Δ:=Δ)) (encodeList encodeBool)
    (fun x => setView (output x.d x.R x.A x.B x.hB)) := by
  let raw : PolyProgram (Input.encode (Δ:=Δ)) enc Input.raw :=
    (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (raw.fanout ((packInputProgram Δ).comp PackingProgram.program) |>.comp (finish_poly Δ).program).congr _ (finish_input)
end MetricKMedian.Completion.Rational.Program
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
abbrev Raw := List (List ℚ) × Completion.Rational.Program.Raw
def Input.raw (x : Input q) : Raw := (List.ofFn (fun i => List.ofFn (x.d₀ i)),x.toInput.raw)
end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end


