-- Prove2me | Definitions.Def_OAIQ053K081
-- name    : OAIQ053K081
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:28:29.547724+00:00
-- url     : https://prove2.me/theorems/0f457534-8f44-4c79-81fe-d6e8f061063f
-- title:
--   Definitions bundle OAIQ053K081 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_CookLevin_CookClockProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookClockProgram.lean), [`KMedian_Programs_BranchProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/BranchProgram.lean), [`KMedian_Programs_FinalSelectionProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/FinalSelectionProgram.lean), [`KMedian_Projection_SeedSound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/SeedSound.lean), [`KMedian_Reduction_DeletionProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/DeletionProgram.lean), [`KMedian_Reduction_LocalCompletionProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/LocalCompletionProgram.lean), [`KMedian_Reduction_ReductionOutcomesProgram`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Reduction/ReductionOutcomesProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K076`, `OAIQ053K077`, `OAIQ053K078` and `OAIQ053K079` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K082` and `OAIQ053K083`; the statement `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K076
import Definitions.Def_OAIQ053K077
import Definitions.Def_OAIQ053K078
import Definitions.Def_OAIQ053K079

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionProgram
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

 theorem valuesData_view (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    valuesData c (view I,setView T)=values I T c := by
  simp only [valuesData,choicesRaw_choices,List.flatMap_map,Preparation.RationalUnitInput.Program.ranks_view,List.map_ofFn,
    Function.comp_def,diff_view,erase_view,costData_view,values]

 theorem endpointsData_view (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    endpointsData c (view I,setView T)=(endpoints I T c).map setView := by
  simp only [endpointsData,valuesData_view,endpoints,List.map_map,Function.comp_def,historyData_view]
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_LocalCompletionProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.distance_client_facility _root_.OAI.MetricKMedian.Instance.restrict_cost
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

 theorem localData_view (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ) (δ : ℚ) (t : Fin I.n) :
    localData (((view I,(setView F,setView B)),(List.ofFn r,δ)),t.val)=setView (localChoice I F B r δ t) := by
  unfold localData
  rw [candidatesData_view]
  simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change pickData (List.ofFn (fun a : Fin I.n => weightData (((view I,(setView F,setView B)),(List.ofFn r,δ)),(t.val,a.val))),
    setView (rationalCandidates I F r δ t))=setView (localChoice I F B r δ t)
  simp only [weightData_view]
  exact pickData_view _ _

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
-- module Solutions.OAIQ053_KM.KMedian_Reduction_ReductionOutcomesProgram
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
open Enumeration
 theorem completionsData_view (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    completionsData δ b (view I,(setView F,setView U))=(completions I F U δ b).map setView := by
  simp only [completionsData,choicesRaw_choices,List.flatMap_map,List.map_map,Function.comp_def,diff_view,radiiData_view,
    completionData_view,completions,List.map_flatMap]

 theorem outcomesData_view (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) :
    outcomesData δ c b (view I,(setView F,setView T))=(outcomes I F T δ c b).map setView := by
  simp only [outcomesData,endpointsData_view,List.flatMap_map,completionsData_view,outcomes,List.map_cons,List.map_flatMap]
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BranchProgram
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
namespace Branch
 theorem restrictedData_view (B : Branch) (h : B.allowed) : restrictedData B.view=InstanceProgram.view (B.restricted h) := rfl
end Branch
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
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookClockProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookClockProgram
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau
open scoped Classical

lemma poly_firstWord : Poly CookLevin.firstWord := by
  exact Poly.list_append.comp (Poly.pair (poly_encodeNat.comp Poly.list_length) Poly.identity)
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookClockProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedSound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedSound
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Amplifier ProjectionSeed CloudOrder
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable def good := (projection t h).prod (BiProjection.neutral Bool Bool Bool Bool)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedSound

end OAI
end


