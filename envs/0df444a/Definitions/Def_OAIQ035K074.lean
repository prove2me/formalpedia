-- Prove2me | Definitions.Def_OAIQ035K074
-- name    : OAIQ035K074
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:24:38.09788+00:00
-- url     : https://prove2.me/theorems/fd8f96df-a536-47b6-beb3-5c0d10b60187
-- title:
--   Definitions bundle OAIQ035K074 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 3 definitions and 19 theorems. The definitions and types are `OAI.MetricKMedian.Reduction.Program.algorithm`, `OAI.MetricKMedian.Reduction.Program.allList`, `OAI.MetricKMedian.Reduction.Program.ordinarySet`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Programs_BranchProgram`, `KMedian_Programs_FinalSelectionProgram`, `KMedian_Reduction_DeletionProgram`, `KMedian_Reduction_LocalCompletionProgram`, `KMedian_Reduction_OrdinaryListProgram`, `KMedian_Sparse_SparseBundleLaw`, `KMedian_Sparse_SparseGridRounding`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K070`, `OAIQ035K071` and `OAIQ035K072` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K075`; the statement `OAI.MetricKMedian.Reduction.Program.ordinarySet_spec`; the proof of `OAI.MetricKMedian.Reduction.Program.ordinarySet_spec`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K070
import Definitions.Def_OAIQ035K071
import Definitions.Def_OAIQ035K072

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

theorem law_mean (q : Fin n → ℚ) (K : ℕ) (hq : ∀ i, 0 ≤ q i)
    (hs : (∑ i,q i)=(K:ℚ)) (i : Fin n) :
    (law q).moment (fun c => (c i:ℚ))=q i := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (SparseCardinalRounding.round (fraction q)).moment
        (fun p => (base q i:ℚ)+point p i) := by
      apply SparseIntegerLaw.moment_congr
      intro a
      exact count_cast _ _ (SparseCardinalRounding.round_invariants (fraction q)
        (fraction_unit q hq) (K-∑ i,base q i) (fraction_sum q hq K hs) a).1 i
    _ = q i := by
      rw [SparseIntegerLaw.moment_add,SparseIntegerLaw.moment_const,SparseCardinalRounding.round_mean]
      simp only [fraction,point,Vector.getElem_ofFn,add_sub_cancel]

theorem law_pair (q : Fin n → ℚ) (K : ℕ) (hq : ∀ i, 0 ≤ q i)
    (hs : (∑ i,q i)=(K:ℚ)) (i j : Fin n) (hij : i≠j) :
    (law q).moment (fun c => (c i:ℚ)*(c j:ℚ)) ≤ q i*q j := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (SparseCardinalRounding.round (fraction q)).moment
        (fun p => ((base q i:ℚ)+point p i)*((base q j:ℚ)+point p j)) := by
      apply SparseIntegerLaw.moment_congr
      intro a
      have hh := SparseCardinalRounding.round_invariants (fraction q)
        (fraction_unit q hq) (K-∑ i,base q i) (fraction_sum q hq K hs) a
      rw [count_cast _ _ hh.1,count_cast _ _ hh.1]
    _ ≤ ((base q i:ℚ)+point (fraction q) i)*((base q j:ℚ)+point (fraction q) j) :=
      SparseIntegerLaw.moment_affine_pair_le _ _ _ _ _ _ _
        (SparseCardinalRounding.round_mean _ i) (SparseCardinalRounding.round_mean _ j)
        (SparseCardinalRounding.round_pair _ i j hij)
    _ = q i*q j := by simp only [fraction,point,Vector.getElem_ofFn,add_sub_cancel]

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

theorem single (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ)) (i : Fin n) (j : Fin m) :
    (law q).moment (fun G => (G j i:ℚ))=q i j := by
  have hh := SparseCounts.run_single (fun j => SparseGridRounding.law (fun i => q i j)) q
    (fun i j => SparseGridRounding.law_mean (fun i => q i j) (K j) (fun i => hq i j) (hs j) i)
    m le_rfl i j
  simpa only [SparseCounts.target,SparseCounts.edge,ite_eq_left j.isLt] using hh

theorem cross_pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i h : Fin n) (j k : Fin m) (hjk : j≠k) :
    (law q).moment (fun G => (G j i:ℚ)*(G k h:ℚ))=q i j*q h k := by
  have hh := SparseCounts.run_pair (fun j => SparseGridRounding.law (fun i => q i j)) q
    (fun i j => SparseGridRounding.law_mean (fun i => q i j) (K j) (fun i => hq i j) (hs j) i)
    m le_rfl i h j k hjk
  simpa only [SparseCounts.target,SparseCounts.edge,ite_eq_left j.isLt,ite_eq_left k.isLt] using hh

theorem same_pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i h : Fin n) (j : Fin m) (hih : i≠h) :
    (law q).moment (fun G => (G j i:ℚ)*(G j h:ℚ)) ≤ q i j*q h j := by
  have hh := SparseCounts.run_same (fun j => SparseGridRounding.law (fun i => q i j)) m le_rfl i h j
  simp only [SparseCounts.edge,ite_eq_left j.isLt] at hh
  exact hh.trans_le (SparseGridRounding.law_pair (fun i => q i j) (K j)
    (fun i => hq i j) (hs j) i h hih)

end MetricKMedian.SparseBundles
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration

 theorem eligibleData_view (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    eligibleData ((view I,B),setView U)=setView (rationalEligible I B U) := by
  simp only [eligibleData,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change (get (setView U) i.val && decide (costData (view I,erase (i.val,setView U))-costData (view I,setView U)≤B))=decide _
  rw [get_view,erase_view,costData_view,costData_view]
  simp only [rationalEligible,mem_filter,Bool.decide_and]
 theorem deleteData_view (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    deleteData ((view I,B),setView U)=setView (rationalDeleteStep I B U) := by
  unfold deleteData rationalDeleteStep
  change (if I.k < card (setView U) then _ else _)=_
  rw [card_view]
  by_cases hk : I.k < U.card
  · simp only [ite_eq_left hk]
    rw [eligibleData_view,Completion.Rational.PackingProgram.any_view]
    by_cases he : (rationalEligible I B U).Nonempty
    · simp only [decide_eq_true he,ite_true,dite_eq_left he,InstanceProgram.first_view _ he,erase_view]
    · simp only [decide_eq_false he,Bool.false_eq_true,ite_false,dite_eq_right he]
  · simp only [ite_eq_right hk]

 theorem historyData_view (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) (c : ℕ) :
    historyData c ((view I,B),setView U)=setView (rationalHistory I B U c) := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [historyData,rationalHistory,ih,deleteData_view]

end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_LocalCompletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view insert insert_view)
open Enumeration

 theorem getDist_view (I : Instance) (i j : Fin I.n) : getDist (view I,(i.val,j.val))=I.distance i j := by
  simp only [getDist,view,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

 theorem radiiData_view (I : Instance) (U : Finset (Fin I.n)) : radiiData (view I,setView U)=List.ofFn (rationalRadii I U) := by
  simp only [radiiData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  change List.ofFn (fun t : Fin I.n => nearestData (List.ofFn (I.distance t),erase (t.val,setView U)))=_
  simp only [erase_view,nearestData_view]
  rfl

 theorem candidatesData_view (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) (t : Fin I.n) :
    candidatesData (((view I,(setView F,setView B)),(List.ofFn r,δ)),t.val)=setView (rationalCandidates I F r δ t) := by
  simp only [candidatesData,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext a
  change (get (setView F) a.val && decide (getDist (view I,(t.val,a.val))≤δ*((List.ofFn r)[t.val]?.getD 0)))=decide _
  rw [get_view,getDist_view]
  simp only [List.getElem?_ofFn,dite_eq_left t.isLt,Option.getD_some,Fin.eta,rationalCandidates,mem_filter,Bool.decide_and]

 theorem weightData_view (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) (t a : Fin I.n) :
    weightData (((view I,(setView F,setView B)),(List.ofFn r,δ)),(t.val,a.val))=localWeight I r B t a := by
  unfold weightData
  change ((indices (setView I.clients)).map (fun j => _)).sum=_
  simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  change (List.ofFn (fun j : Fin I.n => if get (setView I.clients) j.val && decide (3*getDist (view I,(j.val,t.val))≤(List.ofFn r)[t.val]?.getD 0) then
    nearestData ((List.ofFn (fun i => List.ofFn (I.distance i)))[j.val]?.getD [],insert (a.val,setView B)) else 0)).sum=_
  simp only [get_view,getDist_view,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,insert_view,nearestData_view,Bool.and_eq_true,decide_eq_true_eq,List.sum_ofFn]
  rw [← Finset.sum_filter]
  change (∑j∈univ.filter (fun j => j∈I.clients ∧ 3*I.distance j t ≤ r t),rationalNearest I j (Insert.insert a B))=_
  have he : univ.filter (fun j => j∈I.clients ∧ 3*I.distance j t ≤ r t)=rationalRegion I r t := by ext j; simp [rationalRegion]
  rw [he]; rfl

 theorem pickData_view {n : ℕ} (w : Fin n → ℚ) (K : Finset (Fin n)) :
    pickData (List.ofFn w,setView K)=setView (pickSingleton K w) := by
  unfold pickData pickSingleton
  rw [Completion.Rational.PackingProgram.any_view]
  by_cases h : K.Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,nearest_view w K h,InstanceProgram.singletonRaw_view]
    rfl
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h,setView,List.map_ofFn,Function.comp_def,notMem_empty,decide_false]

 theorem localData_view (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) (t : Fin I.n) :
    localData (((view I,(setView F,setView B)),(List.ofFn r,δ)),t.val)=setView (localChoice I F B r δ t) := by
  unfold localData
  rw [candidatesData_view]
  simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change pickData (List.ofFn (fun a : Fin I.n => weightData (((view I,(setView F,setView B)),(List.ofFn r,δ)),(t.val,a.val))),
    setView (rationalCandidates I F r δ t))=setView (localChoice I F B r δ t)
  simp only [weightData_view]
  exact pickData_view _ _

 theorem unionData_view {n : ℕ} (S : Finset (Fin n)) (L : List (Finset (Fin n))) :
    unionData (setView S,L.map setView)=setView (L.toFinset.biUnion id) := by
  simp only [unionData,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,List.map_map,List.any_map,List.any_eq_true,id_eq,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true_eq,
    mem_biUnion,List.mem_toFinset]

 theorem completionData_view (I : Instance) (F B G : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) :
    completionData (((view I,(setView F,setView B)),(List.ofFn r,δ)),setView G)=setView (completionSet I F B G r δ) := by
  unfold completionData
  rw [Preparation.RationalUnitInput.Program.ranks_view]
  simp only [List.map_ofFn,Function.comp_def,localData_view]
  have he : List.ofFn (fun t => setView (localChoice I F B r δ (G.orderEmbOfFin rfl t)))=
      (List.ofFn (fun t => localChoice I F B r δ (G.orderEmbOfFin rfl t))).map setView := by simp only [List.map_ofFn,Function.comp_def]
  rw [he,unionData_view,union_view]
  apply congrArg setView
  unfold completionSet
  congr 1
  ext i
  simp only [mem_biUnion,id_eq,List.mem_toFinset,List.mem_ofFn]
  constructor
  · rintro ⟨_,⟨t,rfl⟩,hi⟩; exact ⟨_,G.orderEmbOfFin_mem rfl t,hi⟩
  · rintro ⟨t,ht,hi⟩
    obtain ⟨a,ha⟩ := (List.mem_ofFn.mp ((mem_orderList G t).mpr ht))
    subst t
    exact ⟨_,⟨a,rfl⟩,hi⟩
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def allList (I : Instance) : List (Finset (Fin I.n)) :=
  (branches I I.facilities a).flatMap (fun F => branchOut r hr p c b δ ⟨I,F⟩)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_FinalSelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
 theorem feasibleData_view (I : Instance) (S : Finset (Fin I.n)) : feasibleData (view I,setView S)=feasible I S := by
  simp only [feasibleData,view,InstanceProgram.subsetRaw_view,Completion.Rational.PackingProgram.any_view,card_view,feasible,Bool.decide_and,Bool.and_assoc]
 theorem selectRaw_view (I : Instance) (L : List (Finset (Fin I.n))) :
    selectRaw (view I,L.map setView)=((SparseSelect.best (feasible I) (rationalCost I) L).map setView).toList := by
  let ann := fun S : Finset (Fin I.n) => (feasible I S,(rationalCost I S,setView S))
  have ha : annotateData (view I,L.map setView)=L.map ann := by
    simp only [annotateData,List.map_map,Function.comp_def,feasibleData_view,costData_view]; rfl
  unfold selectRaw
  rw [ha,SparseSelect.TaggedProgram.raw_best]
  rw [← SparseSelect.best_map (feasible I) (rationalCost I) Prod.fst (fun a => a.2.1) ann (fun _ => rfl) (fun _ => rfl)]
  simp only [Option.map_map]; rfl
 theorem selectData_view (I : Instance) (L : List (Finset (Fin I.n))) :
    selectData (view I,L.map setView)=setView (selectList I L) := by
  unfold selectData
  rw [selectRaw_view]
  simp only [InstanceProgram.fallbackData,InstanceProgram.singletonData_view,selectList]
  cases SparseSelect.best (feasible I) (rationalCost I) L <;> rfl
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_OrdinaryListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def ordinarySet (I : Instance) : Finset (Fin I.n) :=
  if I.zeroTest then I.zeroOutput else selectList I (allList r hr p c a b δ I)
def algorithm (I : Instance) : List Bool := setView (ordinarySet r hr p c a b δ I)
end MetricKMedian.Reduction.Program
end

end OAI
end


