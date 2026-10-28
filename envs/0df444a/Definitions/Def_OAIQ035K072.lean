-- Prove2me | Definitions.Def_OAIQ035K072
-- name    : OAIQ035K072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:22:40.109877+00:00
-- url     : https://prove2.me/theorems/f87f8865-1e40-4434-901d-edd1d65de207
-- title:
--   Definitions bundle OAIQ035K072 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 4 definitions and 6 theorems. The definitions and types are `OAI.MetricKMedian.Reduction.Program.annotateData`, `OAI.MetricKMedian.Reduction.Program.feasibleData`, `OAI.MetricKMedian.Reduction.Program.selectData`, `OAI.MetricKMedian.Reduction.Program.selectRaw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Programs_FinalSelectionProgram`, `KMedian_Reduction_ReductionCostProgram`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K066` and `OAIQ035K068` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K074`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K066
import Definitions.Def_OAIQ035K068

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_ReductionCostProgram
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

 theorem costData_view (I : Instance) (U : Finset (Fin I.n)) : costData (view I,setView U)=rationalCost I U := by
  simp only [costData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,
    MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq]
  change (List.ofFn (fun j : Fin I.n => if j∈I.clients then nearestData (List.ofFn (I.distance j),setView U) else 0)).sum=_
  simp only [nearestData_view,List.sum_ofFn,rationalCost]
  rw [← Finset.sum_filter]
  simp only [filter_mem_eq_inter,univ_inter]

 theorem diff_view {n : ℕ} (S T : Finset (Fin n)) : diff (setView S,setView T)=setView (S\T) := by
  simp only [diff,setView,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,mem_sdiff,Bool.decide_and,decide_not]
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
def feasibleData (x : Raw × Row) : Bool := InstanceProgram.subsetRaw (x.2,x.1.1.2) && x.2.any id && decide (card x.2≤x.1.2.1)
@[fun_prop] theorem feasibleData_poly : Poly feasibleData := by unfold feasibleData; fun_prop
def annotateData (x : Raw × Table) : List SparseSelect.TaggedProgram.Tag :=
  x.2.map (fun S => (feasibleData (x.1,S),(costData (x.1,S),S)))
@[fun_prop] theorem annotateData_poly : Poly annotateData := by unfold annotateData; apply list_map <;> fun_prop
def selectRaw (x : Raw × Table) : Table := SparseSelect.TaggedProgram.raw (annotateData x)
@[fun_prop] theorem selectRaw_poly : Poly selectRaw := by unfold selectRaw; fun_prop
def selectData (x : Raw × Table) : Row := InstanceProgram.fallbackData (x.1,selectRaw x)
@[fun_prop] theorem selectData_poly : Poly selectData := by unfold selectData; fun_prop
end MetricKMedian.Reduction.Program
end

end OAI
end


