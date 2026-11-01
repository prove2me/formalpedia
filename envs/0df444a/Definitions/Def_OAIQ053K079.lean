-- Prove2me | Definitions.Def_OAIQ053K079
-- name    : OAIQ053K079
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:25:59.131992+00:00
-- url     : https://prove2.me/theorems/e93707e1-d02f-4bb3-99b1-5c74e9940c17
-- title:
--   Definitions bundle OAIQ053K079 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 11 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_Programs_FinalSelectionProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/FinalSelectionProgram.lean), [`KMedian_Reduction_DeletionProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/DeletionProgram.lean), [`KMedian_Reduction_LocalCompletionProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/LocalCompletionProgram.lean), [`KMedian_Reduction_ReductionCostProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/ReductionCostProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K070`, `OAIQ053K072` and `OAIQ053K073` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K081`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K070
import Definitions.Def_OAIQ053K072
import Definitions.Def_OAIQ053K073

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_ReductionCostProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
open MaskProgram

 theorem nearestData_view (I : Instance) (j : Fin I.n) (U : Finset (Fin I.n)) :
    nearestData (List.ofFn (I.distance j),setView U)=rationalNearest I j U := by
  unfold nearestData rationalNearest
  split_ifs with h
  · exact LPBinary.minimum_eq_finset _ _ (h.image _) (selectedValues_mem (I.distance j) U)
  · have he : selectedValues (List.ofFn (I.distance j),setView U)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      obtain ⟨i,hi,_⟩ := mem_image.mp ((selectedValues_mem (I.distance j) U q).mp hq)
      exact h ⟨i,hi⟩
    rw [he]; rfl

 theorem costData_view (I : Instance) (U : Finset (Fin I.n)) : costData (view I,setView U)=rationalCost I U := by
  simp only [costData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,
    MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq]
  change (List.ofFn (fun j : Fin I.n => if j∈I.clients then nearestData (List.ofFn (I.distance j),setView U) else 0)).sum=_
  simp only [nearestData_view,List.sum_ofFn,rationalCost]
  rw [← Finset.sum_filter]
  simp only [filter_mem_eq_inter,univ_inter]

 theorem diff_view {n : ℕ} (S T : Finset (Fin n)) : diff (setView S,setView T)=setView (S\T) := by
  simp only [diff,setView,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,mem_sdiff,Bool.decide_and,decide_not]
 theorem union_view {n : ℕ} (S T : Finset (Fin n)) : union (setView S,setView T)=setView (S∪T) := by
  simp only [union,setView,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,mem_union,Bool.decide_or]
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_FinalSelectionProgram
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
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Reduction_LocalCompletionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

 theorem radiiData_view (I : Instance) (U : Finset (Fin I.n)) : radiiData (view I,setView U)=List.ofFn (rationalRadii I U) := by
  simp only [radiiData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  change List.ofFn (fun t : Fin I.n => nearestData (List.ofFn (I.distance t),erase (t.val,setView U)))=_
  simp only [erase_view,nearestData_view]
  rfl

 theorem unionData_view {n : ℕ} (S : Finset (Fin n)) (L : List (Finset (Fin n))) :
    unionData (setView S,L.map setView)=setView (L.toFinset.biUnion id) := by
  simp only [unionData,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,List.map_map,List.any_map,List.any_eq_true,id_eq,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true_eq,
    mem_biUnion,List.mem_toFinset]

end MetricKMedian.Reduction.Program
end

end OAI
end


