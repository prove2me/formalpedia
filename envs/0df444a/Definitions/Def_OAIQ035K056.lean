-- Prove2me | Definitions.Def_OAIQ035K056
-- name    : OAIQ035K056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:13:11.252335+00:00
-- url     : https://prove2.me/theorems/735c802d-3293-4f1d-a4e8-a609594700e0
-- title:
--   Definitions bundle OAIQ035K056 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 9 definitions and 35 theorems. The definitions and types are `OAI.MetricKMedian.IntegerLaw.BinaryCompression.integerInputProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.scaledRowsProgram`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Raw`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.stepRaw`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.flagsData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.outsideData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.targetsData`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.Input.raw`, `OAI.MetricKMedian.SparseTargetSubset.Program.Raw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_GraphListOperations`, `KMedian_Geometry_GraphRunHeight`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Process_BatchActionArrays`, `KMedian_Process_BatchGraphData`, `KMedian_Process_BatchOrdinalArrays`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_PhysicalBatchList`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_RoundingUniformStep`, `KMedian_Process_TaperAllProgram`, `KMedian_Process_TaperListProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Rounding_TargetSubsetProgram`, `KMedian_Sparse_SparseBernoulliRun`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseProduct`.
--
--   **Imports.** It imports the bundles `OAIQ035K050`, `OAIQ035K051` and `OAIQ035K052` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K059`, `OAIQ035K060`, `OAIQ035K061`, `OAIQ035K062`, `OAIQ035K063` and `OAIQ035K064`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K050
import Definitions.Def_OAIQ035K051
import Definitions.Def_OAIQ035K052

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
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingUniformStep
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

end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

theorem prodCompress_spec {d : ℕ} (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (v : γ → Fin d → ℚ) :
    let ρ := μ.prodCompress ν f v
    ρ.length ≤ d+1 ∧
    (∀ a : Fin ρ.length, ∃ b : Fin μ.length, ∃ c : Fin ν.length,
      ρ.states[a.val]=f μ.states[b.val] ν.states[c.val]) ∧
    ∀ j, ρ.moment (fun t => v t j)=μ.moment (fun a => ν.moment (fun b => v (f a b) j)) := by
  have h := (μ.prod ν f).compressAuto_correct v
  refine ⟨h.1,?_,fun j => (h.2.2 j).trans (prod_moment μ ν f _)⟩
  intro a
  obtain ⟨b,hb⟩ := h.2.1 a
  refine ⟨((finProdFinEquiv (m := μ.length) (n := ν.length)).symm b).1,((finProdFinEquiv (m := μ.length) (n := ν.length)).symm b).2,?_⟩
  exact hb.trans (by
    simp only [prod,Vector.getElem_ofFn]
    congr 3)

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

 theorem edges_view {n m : ℕ} (G : Graph n m) :
    edges (List.replicate n (),view G)=List.ofFn (edgeCode G) := by
  simp only [edges,indices,List.length_replicate,RoundingList.range_finRange,view,
    List.flatMap_def,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map]
  simp only [List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    decide_eq_true_eq]
  rw [RoundingList.ofFn_product]
  rfl

 theorem featureList_view {n m : ℕ} (G : Graph n m) :
    featureList (List.replicate n (),view G)=List.ofFn (features G) := by
  simp only [featureList,edges_view,RoundingList.features,List.flatMap_def,List.map_ofFn,
    Function.comp_def,RoundingList.ofFn_product]
  rw [List.ofFn_add]
  congr 1
  · congr 1; funext i
    have hi : (Fin.castAdd ((n*m)*(n*m)) i : Fin (n*m+(n*m)*(n*m)))=finSumFinEquiv (Sum.inl i) := rfl
    change edgeCode G i = features G (Fin.castAdd ((n*m)*(n*m)) i)
    rw [hi]
    simp only [features,Equiv.symm_apply_apply,Sum.elim_inl]
  · congr 1; funext i
    have hi : (Fin.natAdd (n*m) i : Fin (n*m+(n*m)*(n*m)))=finSumFinEquiv (Sum.inr i) := by apply Fin.ext; simp [finSumFinEquiv]
    rw [hi]
    simp only [features,Equiv.symm_apply_apply,Sum.elim_inr]

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

theorem run_length (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) (t : ℕ) :
    (run ν t).length ≤ n*m+(n*m)*(n*m)+1 := by
  induction t with
  | zero => change 1 ≤ _; omega
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · exact ((run ν t).prodCompress_spec (ν ⟨t,ht⟩)
        (fun G S => next G S ⟨t,ht⟩) features).1
    · exact ih

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseGraph
open Binary
variable {n m : ℕ}

theorem denominator_height (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) (N L : ℕ)
    (hN : ∀ i, (ν i).length≤N) (hL : ∀ i, (ν i).law.denominator≤(2:ℤ)^L) (t : ℕ) :
    (run ν t).law.denominator≤(2:ℤ)^(stepHeight n m N L*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      let μ := run ν t
      let ρ := μ.prod (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩)
      have hc := ρ.compressAuto_denominator features 0
        (fun i a => (features_height ρ.states[i.val] a).1)
        (fun i a => (features_height ρ.states[i.val] a).2)
      simp only [zero_mul,add_zero] at hc
      have hrD : ρ.law.denominator=μ.law.denominator*(ν ⟨t,ht⟩).law.denominator := rfl
      have hrN : ρ.length ≤ (n*m+(n*m)*(n*m)+1)*N :=
        Nat.mul_le_mul (run_length ν t) (hN _)
      change (ρ.compressAuto features).law.denominator≤_
      apply hc.trans
      rw [hrD]
      calc
        _ ≤ ((2:ℤ)^(stepHeight n m N L*t)*(2:ℤ)^L)*
            (2:ℤ)^((2*(n*m+(n*m)*(n*m)+1)*(n*m+(n*m)*(n*m)+1))*
              ((n*m+(n*m)*(n*m)+1)*N+1)*((n*m+(n*m)*(n*m)+1)*N)) := by
          gcongr
          · exact (ν ⟨t,ht⟩).law.denominator_pos.le
          · exact hL _
          · norm_num
        _ = _ := by rw [← pow_add,← pow_add]; congr 1; simp only [stepHeight]; ring
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))
end MetricKMedian.SparseGraph
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem run_length (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) : (run (d := d) p hp t).length ≤ (n+1)^d+1 := by
  induction t with
  | zero => change 1 ≤ _; omega
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · exact ((run (d := d) p hp t).branch (fun _ => p ⟨t,ht⟩)
        (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)).compressAuto_correct
          (features (d := d)) |>.1
    · exact ih

end MetricKMedian.SparseBernoulli

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

abbrev Raw := (List ℚ × (List (List ℚ) × ℚ)) × Row

def stepRaw (x : Raw × (Row × Row)) : Raw × (Row × Row) :=
  if x.2.1.any id then
    let c := MaskProgram.nearest (x.1.1.1,x.2.1)
    (x.1,((indices x.2.1).map (fun i => MaskProgram.get x.2.1 i &&
      decide (x.1.1.2.2*(x.1.1.1[i]?.getD 0) < (x.1.1.2.1[i]?.getD [])[c]?.getD 0)),
      (indices x.2.2).map (fun i => MaskProgram.get x.2.2 i || decide (i=c))))
  else x
@[fun_prop] theorem stepRaw_poly : Poly stepRaw := by
  unfold stepRaw
  apply Poly.ite
  · fun_prop
  · apply pair
    · fun_prop
    · apply pair <;> apply list_map <;> fun_prop
  · fun_prop
end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)

theorem append_poly {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x++g x) :=
  comp list_append (pair hf hg)

def targetsData (x : SupplierRaw) : BTable :=
  ((indices x.1).map (fun i => (indices x.2.2.2.1).map (fun t => (x.2.2.1[t]?.getD [])[i]?.getD false))) ++
  (((indices x.2.2.2.1).flatMap (fun s => (indices x.2.2.2.1).map (fun _ =>
    (indices x.2.2.2.1).map (fun j => decide (j=s))))) ++
    (indices x.2.2.2.1).map (fun t => (indices x.2.2.2.1).map (fun j => decide (j=t))))
@[fun_prop] theorem targetsData_poly : Poly targetsData := by
  unfold targetsData
  apply append_poly
  · apply list_map <;> (first | (apply list_map <;> fun_prop) | fun_prop)
  · apply append_poly
    · apply list_flatMap
      · apply list_map
        · apply list_map <;> fun_prop
        · fun_prop
      · fun_prop
    · apply list_map
      · apply list_map <;> fun_prop
      · fun_prop

def flagsData (x : SupplierRaw) : QRow := x.1.map (fun _ => 1) ++
  (x.2.2.2.1.flatMap (fun _ => x.2.2.2.1.map (fun _ => 0)) ++ x.2.2.2.1.map (fun _ => 0))
@[fun_prop] theorem flagsData_poly : Poly flagsData := by
  unfold flagsData
  apply append_poly
  · apply list_map <;> fun_prop
  · apply append_poly
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
    · apply list_map <;> fun_prop

def outsideData (x : SupplierRaw) (i : ℕ) : Bool := (x.2.1.map (fun P => !(P[i]?.getD false))).all id
@[fun_prop] theorem outsideData_poly : Poly (fun x : SupplierRaw × ℕ => outsideData x.1 x.2) := by
  unfold outsideData; apply comp bool_all; apply list_map <;> fun_prop
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

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

theorem units_eq (d : ℕ) (q : Row) : units d q=List.replicate ((q.length+1)^d) () := by
  rw [← units_length d q]
  exact List.eq_replicate_length.mpr (fun b hb => Subsingleton.elim _ _)

end MetricKMedian.SparseBernoulli.ListOperation
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

 theorem state_iterate (x : Input) (d t : ℕ) : (State.step d)^[t] x.start=x.state d t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparsePhysicalBatch.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table er et indices)

 theorem conflictFree_view {n : ℕ} (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) (e : Fin n) :
    conflictFree (List.ofFn (fun a => SparseGraph.ListOperation.setView (C a)),List.ofFn ω) e.val=true ↔
      ∀ f∈C e, ω f=false := by
  simp only [conflictFree,indices,List.length_ofFn,RoundingList.range_finRange,List.map_map,
    Function.comp_def,List.all_map,List.all_eq_true,List.mem_finRange,forall_const,
    SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,id_eq,Bool.or_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not]
  constructor
  · intro h f hf
    exact (h f).resolve_left (not_not.mpr hf)
  · intro h f
    by_cases hf : f∈C e
    · exact Or.inr (h f hf)
    · exact Or.inl hf

 theorem select_view {n : ℕ} (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (ω : Fin n → Bool) (bal : Bool) :
    select bal (((SparseGraph.ListOperation.setView Z,List.ofFn (fun a => SparseGraph.ListOperation.setView (C a))),
      (p,List.ofFn q)),List.ofFn ω)=SparseGraph.ListOperation.setView
      (if bal then balanced Z C ω else unbalanced Z ω) := by
  apply List.ext_getElem
  · simp only [select,indices,List.length_ofFn,List.length_map,List.length_range,
      SparseGraph.ListOperation.setView]
  · intro i hi hi'
    have hin : i<n := by simpa only [SparseGraph.ListOperation.setView,List.length_ofFn] using hi'
    simp only [select,indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left hin,Option.getD_some]
    apply Bool.eq_iff_iff.mpr
    cases bal
    · simp only [Bool.false_eq_true,ite_false,unbalanced,Finset.mem_filter,Finset.mem_univ,true_and,
        Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not,decide_eq_true_eq]
    · simp only [ite_true,balanced,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,
        Bool.and_eq_true,decide_eq_true_eq]
      rw [show conflictFree (List.ofFn (fun a => List.ofFn (fun h => decide (h∈C a))),List.ofFn ω) i=true ↔
        ∀ f∈C ⟨i,hin⟩, ω f=false from conflictFree_view C ω ⟨i,hin⟩]
end MetricKMedian.SparsePhysicalBatch.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchActionArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.ActionArrays
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch Finset
open SparseGraph.ListOperation (Row Table setView indices)

 theorem overlap_view {n : ℕ} (A B : Finset (Fin n)) :
    overlap (setView A) (setView B)=true ↔ (A∩B).Nonempty := by
  simp only [overlap,indices,setView,List.length_ofFn,RoundingList.range_finRange,List.map_map,
    Function.comp_def,List.any_map,List.any_eq_true,List.mem_finRange,true_and,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,id_eq,Bool.and_eq_true,
    decide_eq_true_eq,Finset.Nonempty,mem_inter]

end MetricKMedian.RationalBatchData.ActionArrays

end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchGraphData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.RationalBatchData.GraphData
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch Finset
open SparseGraph.ListOperation (Row Table setView indices view)

 theorem amount_view {n : ℕ} (m : Fin n → ℚ) : amount (List.ofFn m)=RationalBatchData.amount m := by
  simp only [amount,List.map_ofFn,List.sum_ofFn,Function.comp_def,RationalBatchData.amount]
end MetricKMedian.RationalBatchData.GraphData
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

 theorem parent_code (e : HeavyAction D H) :
    ActionList.parent n (code r D H e)=(r.symm (heavyParent D H e)).val := by
  cases e with
  | inl e => simp only [ActionList.parent,code,Fin.isLt,ite_true,heavyParent]
  | inr e =>
    have hn : 0<n := Nat.zero_lt_of_lt (r.symm e.val.1).isLt
    have hi := (r.symm e.val.2).isLt
    have hc : ¬n+(r.symm e.val.1).val*n+(r.symm e.val.2).val<n := by omega
    change ActionList.parent n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.1).val
    rw [ActionList.parent,ite_eq_right hc,Nat.add_assoc,Nat.add_sub_cancel_left,Nat.mul_comm _ n,
      Nat.mul_add_div hn,Nat.div_eq_of_lt hi,Nat.add_zero]
 theorem child_code (e : {p : I × I // p.1∈H ∧ p.2∈D.erase p.1}) :
    ActionList.child n (code r D H (.inr e))=(r.symm e.val.2).val := by
  simp only [ActionList.child,code]
  rw [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (r.symm e.val.2).isLt]
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

 omit [Fintype I] in
 theorem bias_code (m : I → ℚ) (p φ : ℚ) (e : HeavyAction D H) :
    ActionArrays.bias (((p,φ),List.ofFn (fun i => m (r i))),n) (code r D H e)=
      RationalBatchData.bias m p φ (heavyParent D H e) := by
  simp only [ActionArrays.bias,parent_code,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,OrderIso.apply_symm_apply,RationalBatchData.bias]

end MetricKMedian.RationalBatchData.Ordinal
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

def Input.raw (x : Input) : ListOperation.Raw :=
  ((SparseGraph.ListOperation.setView x.Z,List.ofFn fun e => SparseGraph.ListOperation.setView (x.C e)),
    (x.p,List.ofFn x.q))
end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset

 theorem upper_list {n : ℕ} (d : Fin n → ℚ) : upper (List.ofFn d)=Taper.upper d := by
  simp only [upper,Taper.upper,List.map_ofFn,List.sum_ofFn,one_div,Function.comp_def]
 theorem mem_breaks {n : ℕ} (P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈breaks (P,List.ofFn d) ↔ q∈Taper.breakpoints P d := by
  simp only [breaks,upper_list,List.mem_cons,List.mem_append,List.mem_map,List.mem_ofFn,
    Taper.breakpoints,mem_insert,mem_union,mem_image,mem_univ,true_and]
  aesop
 theorem aSum_list {n : ℕ} (P t : ℚ) (d : Fin n → ℚ) :
    aSum ((P,List.ofFn d),t)=Taper.A P d t := by
  simp only [aSum,List.map_ofFn,List.sum_ofFn,Taper.A,Function.comp_def]
 theorem bSum_list {n : ℕ} (P t : ℚ) (d : Fin n → ℚ) :
    bSum ((P,List.ofFn d),t)=Taper.B P d t := by
  simp only [bSum,List.map_ofFn,List.sum_ofFn,Taper.B,Function.comp_def]
 theorem mem_candidates {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈candidateList ((g,P),List.ofFn d) ↔ q∈Taper.candidates g P d := by
  simp only [candidateList,List.mem_append,List.mem_flatMap,List.mem_map,mem_breaks,
    aSum_list,bSum_list,Taper.candidates,mem_union,mem_image,mem_product,Prod.exists]
  aesop
 theorem mass_list {n : ℕ} (g P r : ℚ) (d : Fin n → ℚ) :
    mass (((g,P),List.ofFn d),r)=rationalMass g P d r := by
  simp only [mass,List.map_ofFn,List.sum_ofFn,rationalMass,Function.comp_def]
 theorem mem_roots {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈roots ((g,P),List.ofFn d) ↔ q∈rootCandidates g P d := by
  simp only [roots,List.mem_filter,mem_candidates,Bool.and_eq_true,decide_eq_true_eq,mass_list,
    rootCandidates,mem_filter]
 theorem radius_list {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) :
    radius ((g,P),List.ofFn d)=inverseRadius g P d := by
  unfold inverseRadius
  split_ifs with h
  · apply LPBinary.foldl_max_eq
    · exact (mem_filter.mp (max'_mem (rootCandidates g P d) h)).2.1.le
    · exact (mem_roots _ _ _ _).mpr (max'_mem _ h)
    · intro q hq
      exact le_max' _ _ ((mem_roots _ _ _ _).mp hq)
  · have he : roots ((g,P),List.ofFn d)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      exact h ⟨q,(mem_roots _ _ _ _).mp hq⟩
    simp only [radius,he,List.foldl_nil]
end MetricKMedian.Taper.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperAllProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset

 theorem colocated_list {n : ℕ} (g : ℚ) (d : Fin n → ℚ) :
    colocated (g,List.ofFn d)=rationalColocatedMass g d := by
  simp only [colocated,List.map_ofFn,List.sum_ofFn,rationalColocatedMass,Function.comp_def]
 theorem extras_list {n : ℕ} (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    extras ((List.ofFn d,List.ofFn fun i => decide (i∈own)),Δ)=
      (((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val := by
  have hf : (RoundingList.indices (List.ofFn d)).filter
      (fun i => decide ((List.ofFn d)[i]?.getD 0=0) && !((List.ofFn fun k => decide (k∈own))[i]?.getD false))=
      ((zeroSources d\own).sort).map Fin.val := by
    simp only [RoundingList.indices,List.length_ofFn,RoundingList.range_finRange,List.filter_map,Function.comp_def,
      List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
    rw [show (fun i : Fin n => decide (d i=0) && !decide (i∈own))=
      (fun i : Fin n => decide (i∈zeroSources d\own)) by
      funext i; simp only [zeroSources,mem_sdiff,mem_filter,mem_univ,true_and,Bool.decide_and,decide_not]]
    rw [EncodingLists.filter_range]
    simp only [filter_univ_mem]
  simp only [extras,hf,EncodingLists.bool_card,List.map_take]
 theorem zeroRow_list {n : ℕ} (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    zeroRow ((List.ofFn d,List.ofFn fun i => decide (i∈own)),Δ)=List.ofFn (zeroMarginal d own Δ) := by
  apply List.ext_getElem
  · simp only [zeroRow,RoundingList.indices,List.length_map,List.length_range,List.length_ofFn]
  · intro k hk hk'
    have hkn : k<n := by simpa only [List.length_ofFn] using hk'
    let i : Fin n := ⟨k,hkn⟩
    simp only [zeroRow,RoundingList.indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hkn,Option.getD_some,extras_list]
    have he : natMember ((((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val,i.val)=true ↔
        i∈(((zeroSources d\own).sort).take (Δ-own.card)).toFinset := by
      rw [natMember_true,List.mem_toFinset]
      simp only [List.mem_map,Fin.val_inj]
      simp only [exists_eq_right]
    change (if decide (i∈own) || natMember ((((zeroSources d\own).sort).take (Δ-own.card)).map Fin.val,i.val) then (1:ℚ) else 0)=zeroMarginal d own Δ i
    simp only [Bool.or_eq_true,decide_eq_true_eq,he,zeroMarginal,zeroSelection,extend,mem_union]
 theorem sourceRow_list {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) :
    sourceRow ((((g,P),List.ofFn d),List.ofFn fun i => decide (i∈own)),Δ)=List.ofFn (sourceMarginals g P d own Δ) := by
  simp only [sourceRow,colocated_list,sourceMarginals]
  split_ifs
  · exact zeroRow_list d own Δ
  · simp only [List.map_ofFn,radius_list,Function.comp_def]
end MetricKMedian.Taper.ListOperation
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
abbrev Raw := Row × ℚ
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end


