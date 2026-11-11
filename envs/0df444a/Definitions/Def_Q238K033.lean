-- Prove2me | Definitions.Def_Q238K033
-- name    : Q238K033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:58.366813+00:00
-- url     : https://prove2.me/theorems/15d34394-ce4f-41e7-bc79-6d57b724e703
-- title:
--   Definitions bundle Q238K033 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 101 declarations of OpenAI's Lean: 101 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.logWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.predWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.contents_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.scores_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionPad.need`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.bounds_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.allRows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.box_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.shape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.cf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.doubled_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.gf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.summed_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.upLeft_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.upRight_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.rawRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.distanceWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.bid_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.chooseColTag`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.chooseEq`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.chooseTag`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.col_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.dual_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.paymentQuery_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.row_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.slack_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.chooseTag`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.distanceWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.field_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.query_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.tag_eq_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.caps_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.columns_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.doubles_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.duals_computes` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CompletionFillMath`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_NatWords`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Encoding_WordSubsets`, `KMedianRecovery_Encoding_WordTake`, `KMedianRecovery_Encoding_Words`, `KMedianRecovery_Machines_BisectionMachine`, `KMedianRecovery_Machines_CappedFold`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Machines_LoopInput2`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_DecisionOps`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_Fuel`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_SortMath`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_SeedTensor`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K028`, `Q238K029` and `Q238K030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K036`, `Q238K037` and `Q238K038`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryCross_transition_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOrientedSearch_run_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryResolve_view_pack_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryCross_transition_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOrientedSearch_run_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryResolve_view_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K028
import Definitions.Def_Q238K029
import Definitions.Def_Q238K030

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

noncomputable def columnMap_computes : PolyComputes (WordList.mapWith Lookup.run) :=
  mapWith_computes Lookup.run_computes
noncomputable def columnOp_computes : PolyComputes columnOp :=
  PolyComputes.comp (f:=swapWords) (g:=WordList.mapWith Lookup.run) swapWords_computes columnMap_computes
noncomputable def matrixIndices_computes : PolyComputes matrixIndices := id_computes.pair Indices.run_computes
noncomputable def transposeMap_computes : PolyComputes (mapWith columnOp) := mapWith_computes columnOp_computes
noncomputable def transposeWords_computes : PolyComputes transposeWords :=
  PolyComputes.comp (f:=matrixIndices) (g:=mapWith columnOp) matrixIndices_computes transposeMap_computes
noncomputable def mulInput_computes : PolyComputes mulInput := by
  unfold mulInput
  simpa only [Function.comp_def] using
    (PolyComputes.pair (f:=transposeWords ∘ discardPrefix) (g:=extractPrefix)
    (PolyComputes.comp (f:=discardPrefix) (g:=transposeWords)
      discardPrefix_computes transposeWords_computes) extractPrefix_computes)
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GetRow2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

noncomputable def tailDiagMapInput_computes : PolyComputes tailDiagMapInput :=
  id_computes.pair (extractPrefix_computes.comp Indices.run_computes)

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Words
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
open BinaryRational
noncomputable def neg {f : List Bool → ℚ} (hf : PolyComputes (fun x=>encode (f x))) :
    PolyComputes (fun x=>encode (-f x)) := by
  have hh := hf.comp negWords_computes
  simpa only [Function.comp_def,negWords_encode] using hh
end RatOps
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList
noncomputable def signOp_computes : PolyComputes signOp :=
  (discardPrefix_computes.comp discardPrefix_computes).comp BinaryRational.negWords_computes
noncomputable def signRun_computes : PolyComputes signRun := Fold.run_computes signOp_computes (4*Polynomial.X+4)
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

noncomputable def second_computes : PolyComputes second := rest₁_computes.comp extractPrefix_computes
end BinaryRationalDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.CappedFold
open WordOperations
noncomputable def run_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (run f) :=
  ((((discardPrefix_computes.comp Fold.items_computes).comp Count.run_computes).pair
    ((RepeatedAppend.fixed_computes 4).pair discardPrefix_computes)).comp
      (BoundedIteration.run_computes (Fold.step_computes hf))).comp Fold.accum_computes
end MetricKMedianRecovery.BitMachine.WordList.CappedFold

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FaceSelection
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryFinalFace
open WordList BinaryRationalDecision
noncomputable def shape_computes (s : Bool) : PolyComputes (shape s) := by
  unfold shape
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (first input,BinaryRational.encode (if s then 1 else -1)))
      (g:=BinaryEllipsoidInitial.run)
      (first_computes.pair (const_computes (BinaryRational.encode (if s then 1 else -1))))
      BinaryEllipsoidInitial.run_computes)
noncomputable def box_computes (s : Bool) : PolyComputes (box s) := by
  unfold box
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (BinaryRational.encode (value (bound input):ℚ),shape s input))
      (g:=mapWith BinaryDecision.boundOp)
      ((RatOps.nat bound_computes).pair (shape_computes s))
      (mapWith_computes BinaryDecision.boundOp_computes))
noncomputable def allRows_computes : PolyComputes allRows := rows_computes.append ((box_computes true).append (box_computes false))
noncomputable def context_computes : PolyComputes context :=
  first_computes.pair ((allRows_computes.comp Count.run_computes).pair (bound_computes.pair allRows_computes))
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack4
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList.Set

noncomputable def oldValue_computes : PolyComputes oldValue := oldInput_computes.comp Lookup.run_computes

noncomputable def op_computes : PolyComputes op := by
  have hl := NatOps.le discardPrefix_computes target_computes
  have hr := NatOps.le target_computes discardPrefix_computes
  have hh := hl.cond (hr.cond replacement_computes oldValue_computes) oldValue_computes
  unfold op
  simpa only [decide_eq_true_eq] using hh
noncomputable def input_computes : PolyComputes input :=
  id_computes.pair (extractPrefix_computes.comp Indices.run_computes)
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=input) (g:=mapWith op) input_computes (mapWith_computes op_computes))
end WordList.Set
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

noncomputable def updateInput_computes : PolyComputes updateInput := by
  unfold updateInput Set.pack
  simpa only [Function.comp_def] using
    ((PolyComputes.comp (f:=extractPrefix) (g:=transposeWords)
      extractPrefix_computes transposeWords_computes).pair
    ((discardPrefix_computes.comp extractPrefix_computes).pair
      (discardPrefix_computes.comp discardPrefix_computes)))
noncomputable def updateColWords_computes : PolyComputes updateColWords := by
  unfold updateColWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=Set.run ∘ updateInput) (g:=transposeWords)
      (PolyComputes.comp (f:=updateInput) (g:=Set.run) updateInput_computes Set.run_computes)
      transposeWords_computes)
noncomputable def cramerInput_computes : PolyComputes cramerInput :=
  id_computes.pair (extractPrefix_computes.comp Indices.run_computes)
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic Matrix
namespace Rectangular
open WordList RationalMatrix

noncomputable def transpose_computes : PolyComputes transpose := by
  unfold transpose
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (discardPrefix input,BinaryEllipsoidInitial.indices (extractPrefix input)))
      (g:=mapWith columnOp)
      (discardPrefix_computes.pair (extractPrefix_computes.comp BinaryEllipsoidInitial.indices_computes))
      transposeMap_computes)
end Rectangular
end

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
noncomputable def bounds_computes : PolyComputes bounds := by
  unfold bounds
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith BinaryRow.bound)
      ((const_computes []).pair id_computes) (mapWith_computes BinaryRow.bound_computes))
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace MetricTable
open WordList

noncomputable def getRow_computes : PolyComputes getRow := (row_computes.pair context_computes).comp Lookup.run_computes
noncomputable def get_computes : PolyComputes get := (col_computes.pair getRow_computes).comp Lookup.run_computes
end MetricTable
namespace BinaryOpeningActivity
open WordList

noncomputable def distanceWord_computes : PolyComputes distanceWord := by
  unfold distanceWord
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (pairBits (table input,discardPrefix input),client input))
      (g:=MetricTable.get)
      ((table_computes.pair discardPrefix_computes).pair client_computes)
      MetricTable.get_computes)
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
open WordOperations BinaryArithmetic WordList BinaryOpeningActivity
noncomputable def values_computes : PolyComputes values := mapWith_computes distanceWord_computes
end MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

noncomputable def activityInput_computes : PolyComputes activityInput :=
  (((itemField_computes 0).pair discardPrefix_computes).pair
    ((itemField_computes 2).pair (itemField_computes 3))).pair (itemField_computes 1)
noncomputable def distanceWords_computes : PolyComputes distanceWords := by
  unfold distanceWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (pairBits (itemField 0 input,itemField 6 input),discardPrefix input))
      (g:=MetricTable.get)
      (((itemField_computes 0).pair (itemField_computes 6)).pair discardPrefix_computes)
      MetricTable.get_computes)
noncomputable def input_computes : PolyComputes input :=
  id_computes.pair ((field_computes 7).comp BinaryEllipsoidInitial.indices_computes)
end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NatOps
noncomputable def eq {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (value (f x)=value (g x))]) := by
  have hh := (le hf hg).cond (le hg hf) (const_computes [false])
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases h : value (f x)≤value (g x)
  · simp only [decide_eq_true_eq,h,ite_true, if_true]
    congr 1
    apply decide_eq_decide.mpr
    omega
  · simp only [decide_eq_true_eq,h,ite_false, if_false]
    simp only [List.cons.injEq,and_true,decide_eq_false_iff_not]
    omega
end NatOps
namespace BinaryOpeningConstant
open WordList RationalLinearFeasibility RationalOpenability

noncomputable def field_computes (k : ℕ) : PolyComputes (field k) :=
  discardPrefix_computes.comp (BinaryOpeningPayment.field_computes k)
noncomputable def query_computes (k : ℕ) : PolyComputes (query k) := extractPrefix_computes.pair (field_computes k)
noncomputable def distanceWords_computes (f j : ℕ) : PolyComputes (distanceWords f j) := by
  unfold distanceWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (pairBits (BinaryOpeningPayment.itemField 0 input,field f input),field j input))
      (g:=MetricTable.get)
      (((BinaryOpeningPayment.itemField_computes 0).pair (field_computes f)).pair (field_computes j))
      MetricTable.get_computes)
noncomputable def tag_eq_computes (k : ℕ) : PolyComputes (fun x=>[decide (tag x=k)]) := by
  have hh := NatOps.eq (field_computes 0) (const_computes k.bits)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  congr 1
  apply decide_eq_decide.mpr
  simp only [tag,value_bits]
noncomputable def chooseTag {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if tag x=k then f x else g x)) := by
  have hh := (tag_eq_computes k).cond hf hg
  simpa only [decide_eq_true_eq,apply_ite] using hh

end BinaryOpeningConstant
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IfNat
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
noncomputable def ifNatEq {f g : List Bool → List Bool} {p q : List Bool → ℚ}
    (hf : PolyComputes f) (hg : PolyComputes g)
    (hp : PolyComputes (fun x=>BinaryRational.encode (p x)))
    (hq : PolyComputes (fun x=>BinaryRational.encode (q x))) :
    PolyComputes (fun x=>BinaryRational.encode (if value (f x)=value (g x) then p x else q x)) := by
  have hh := (NatOps.eq hf hg).cond hp hq
  simpa only [decide_eq_true_eq,apply_ite] using hh
end RatOps
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility RationalOpenability

noncomputable def col_computes (k : ℕ) : PolyComputes (col k) :=
  discardPrefix_computes.comp (BinaryOpeningPayment.field_computes k)
noncomputable def row_computes (k : ℕ) : PolyComputes (row k) :=
  extractPrefix_computes.comp (BinaryOpeningConstant.field_computes k)
noncomputable def chooseEq {f g : List Bool → ℚ} (k l : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if value (col k x)=value (row l x) then f x else g x)) :=
  RatOps.ifNatEq (col_computes k) (row_computes l) hf hg
noncomputable def chooseColTag {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if value (col 0 x)=k then f x else g x)) := by
  have hh := RatOps.ifNatEq (col_computes 0) (const_computes k.bits) hf hg
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [value_bits]
noncomputable def chooseTag {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningConstant.tag (extractPrefix x)=k then f x else g x)) := by
  have hh := (extractPrefix_computes.comp (BinaryOpeningConstant.tag_eq_computes k)).cond hf hg
  simpa only [Function.comp_def,decide_eq_true_eq,apply_ite] using hh
noncomputable def bid_computes (j : ℕ) : PolyComputes (fun x=>BinaryRational.encode (bid j x)) :=
  chooseColTag 0 (chooseEq 1 j (RatOps.const 1) (RatOps.const 0)) (RatOps.const 0)
noncomputable def slack_computes : PolyComputes (fun x=>BinaryRational.encode (slack x)) :=
  chooseColTag 1
    (chooseEq 1 2 (chooseEq 2 3 (chooseEq 3 1 (RatOps.const 1) (RatOps.const 0)) (RatOps.const 0)) (RatOps.const 0))
    (RatOps.const 0)
noncomputable def dual_computes : PolyComputes (fun x=>BinaryRational.encode (dual x)) :=
  chooseColTag 1 (chooseEq 1 2 (chooseEq 2 1 (RatOps.const 1) (RatOps.const 0)) (RatOps.const 0)) (RatOps.const 0)

noncomputable def paymentQuery_computes : PolyComputes paymentQuery :=
  (extractPrefix_computes.comp extractPrefix_computes).pair (col_computes 1)
end BinaryOpeningCoefficient
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
namespace Flatten

noncomputable def op_computes : PolyComputes op := Fold.accum_computes.append Find.item_computes
noncomputable def run_computes : PolyComputes run :=
  (Fold.pack_computes id_computes (const_computes []) (const_computes [])).comp
    (Fold.run_computes op_computes (3*Polynomial.X+3))
end Flatten
noncomputable def flatMapWith_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (flatMapWith f) := (mapWith_computes hf).comp Flatten.run_computes
end WordList
end MetricKMedianRecovery.BitMachine
namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
noncomputable def crossWith_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (crossWith f) := by
  have mapComputes : PolyComputes
      (fun input=>mapWith f (pairBits (discardPrefix input,extractPrefix input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=fun input=>pairBits (discardPrefix input,extractPrefix input))
        (g:=mapWith f) (discardPrefix_computes.pair extractPrefix_computes) (mapWith_computes hf))
  unfold crossWith
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (discardPrefix input,extractPrefix input))
      (g:=flatMapWith (fun input=>mapWith f (pairBits (discardPrefix input,extractPrefix input))))
      (discardPrefix_computes.pair extractPrefix_computes) (flatMapWith_computes mapComputes))
noncomputable def cross_computes : PolyComputes cross := crossWith_computes id_computes
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def map_computes {f : List Bool → List Bool} (hf : PolyComputes f) : PolyComputes (map f) := by
  unfold map
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith (f ∘ discardPrefix))
      ((const_computes []).pair id_computes)
      (mapWith_computes (discardPrefix_computes.comp hf)))
end WordList
namespace BinaryOpeningEnumeration
open WordList EffectiveOpenability RationalOpenability BinaryOpeningPayment
noncomputable def doubles_computes : PolyComputes doubles := (clients_computes.pair clients_computes).comp cross_computes
noncomputable def triples_computes : PolyComputes triples := ((field_computes 8).pair doubles_computes).comp cross_computes
noncomputable def caps_computes : PolyComputes caps := (clients_computes.pair (field_computes 1)).comp cross_computes
noncomputable def duals_computes : PolyComputes duals := ((field_computes 8).pair clients_computes).comp cross_computes

noncomputable def kinds_computes : PolyComputes kinds := by
  have kindsComputes := (((((((clients_computes.comp (map_computes (unaryTag_computes 0))).append
    (clients_computes.comp (map_computes (unaryTag_computes 1)))).append
    (caps_computes.comp (map_computes (pairTag_computes 2)))).append
    (clients_computes.comp (map_computes (unaryTag_computes 3)))).append
    (const_computes (encode [encode [(4:ℕ).bits]]))).append
    (triples_computes.comp (map_computes (tripleTag_computes 5)))).append
    (triples_computes.comp (map_computes (tripleTag_computes 6)))).append
    (duals_computes.comp (map_computes dualTag_computes))
  unfold kinds
  simpa only [Function.comp_def] using kindsComputes
noncomputable def columns_computes : PolyComputes columns := by
  have columnsComputes := (clients_computes.comp (map_computes (unaryTag_computes 0))).append
    (triples_computes.comp (map_computes variableTag_computes))
  unfold columns
  simpa only [Function.comp_def] using columnsComputes

end BinaryOpeningEnumeration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordOperations WordList
variable {A : Type*}
attribute [local irreducible] mapWith
noncomputable def scores_computes : PolyComputes scores :=
  PolyComputes.comp (f := fun input => pairBits ([],input)) (g := mapWith scoreOp)
    ((const_computes []).pair id_computes) (mapWith_computes scoreOp_computes)
noncomputable def contents_computes : PolyComputes contents := ((const_computes []).pair id_computes).comp (flatMapWith_computes payloadOp_computes)
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DecisionOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NatOps
noncomputable def lt {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>[decide (value (f x)<value (g x))]) := by
  simpa only [←decide_not,not_le] using (le hg hf).not
end NatOps
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_NatWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
noncomputable def natWords_computes : PolyComputes natWords :=
  sign_computes.cond (const_computes []) (tail_computes.comp normalize_computes)
end Signed
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility RationalOpenability EffectiveOpenability
open BinaryOpeningPayment BinaryOpeningEnumeration
noncomputable def rowInput_computes : PolyComputes rowInput := by
  have computation := id_computes.pair (extractPrefix_computes.comp columns_computes)
  exact computation
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

noncomputable def natEq_computes : PolyComputes (fun x=>[natEq x]) := by
  have h := (NatOps.le extractPrefix_computes discardPrefix_computes).cond
    (NatOps.le discardPrefix_computes extractPrefix_computes) (const_computes [false])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases hl : value (extractPrefix x)≤value (discardPrefix x)
  · by_cases hr : value (discardPrefix x)≤value (extractPrefix x)
    · simp [natEq,le_antisymm hl hr]
    · have hn : value (extractPrefix x)≠value (discardPrefix x) := fun he=>hr (he ▸ le_rfl)
      simp [natEq,hl,hr,hn]
  · have hn : value (extractPrefix x)≠value (discardPrefix x) := fun he=>hl (he ▸ le_rfl)
    simp [natEq,hl,hn]

end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FilterItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def filterWith_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (filterWith p) := flatMapWith_computes (filterItem_computes hp)
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SortMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList.Sort

noncomputable def insert_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (insert p) :=
  (filterWith_computes (reverseTest_computes hp)).append
    (cons_computes extractPrefix_computes (filterWith_computes hp))

variable {α : Type*} [LinearOrder α]
noncomputable def op_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (op p) :=
  (Find.item_computes.pair Fold.accum_computes).comp (insert_computes hp)
noncomputable def run_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (run p) :=
  (Fold.pack_computes id_computes (const_computes []) (const_computes [])).comp
    (Fold.run_computes (op_computes hp) (3*Polynomial.X+3))
end WordList.Sort
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves

attribute [local irreducible] MetricTable.get
noncomputable def rawRow_computes : PolyComputes rawRow :=
  ((table_computes.pair (label_computes.comp parentWords_computes)).pair col_computes).comp MetricTable.get_computes
end MetricKMedianRecovery.BitMachine.BinaryLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {q a T L : ℕ}
noncomputable def run (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (step g) (pairBits (runCap.word x,Fold.pack (field 4 x) (context x) (initial x)))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase
open BinaryOpeningPayment

noncomputable def ctxField_computes (k : ℕ) : PolyComputes (ctxField k) := context_computes.comp (field_computes k)
noncomputable def allFacilities_computes : PolyComputes allFacilities := (field_computes 0).comp Indices.run_computes
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic WordList
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment

noncomputable def sf_computes (k : ℕ) : PolyComputes (sf k) := extractPrefix_computes.comp (field_computes k)
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Fuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def fuel_computes : PolyComputes fuel := (BinaryPhaseAdvance.sf_computes 8).comp Count.run_computes
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.map WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run
noncomputable def cf_computes (k : ℕ) : PolyComputes (cf k) := extractPrefix_computes.comp (field_computes k)
noncomputable def contextAt_computes : PolyComputes contextAt :=
  list_computes [cf 0,cf 1,cf 2,discardPrefix,cf 4,cf 5,cf 6,cf 7,cf 8] (by
    intro f hf
    refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨cf_computes _⟩ | exact ⟨discardPrefix_computes⟩)
noncomputable def zeroBudget_computes : PolyComputes zeroBudget :=
  BinaryOpeningEnumeration.clients_computes.comp (map_computes (const_computes (BinaryRational.encode 0)))
noncomputable def start_computes : PolyComputes start := contextAt_computes.pair (extractPrefix_computes.comp zeroBudget_computes)
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordTake
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Take
open WordOperations BinaryArithmetic
noncomputable def number (x : List Bool) : List Bool :=
  (value (lengthBits (discardPrefix x))-value (extractPrefix x)).bits
attribute [local irreducible] number reverse Drop.run
end MetricKMedianRecovery.BitMachine.WordList.Take

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawDrop
open WordOperations BinaryArithmetic
noncomputable def step_computes : PolyComputes step := by
  have hd := NatOps.sub extractPrefix_computes (const_computes [true])
  have hp := hd.pair (discardPrefix_computes.comp WordOperations.tail_computes)
  have hh := (NatOps.zero extractPrefix_computes).cond id_computes hp
  unfold step
  simpa [value,Function.comp_def] using hh
noncomputable def run_computes : PolyComputes run := by
  have hi := BoundedIteration.polynomialRun_computes step_computes Polynomial.X (4*Polynomial.X+1)
  have hh := hi.comp discardPrefix_computes
  have he (x : List Bool) : BoundedIteration.polynomialRun step Polynomial.X (4*Polynomial.X+1) x=
      step^[x.length] x := by
    have ht := BoundedIteration.polynomialRun_eq step Polynomial.X (4*Polynomial.X+1) x (by
      intro j _
      have hb := (iterate_bounds x j).2.2
      obtain ⟨hf,hr⟩ := ProductBits.projections_length x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
        Polynomial.eval_one]
      omega)
    simpa only [Polynomial.eval_X] using ht
  change PolyComputes (fun x=>discardPrefix (step^[x.length] x))
  simpa only [Function.comp_def,he] using hh
end MetricKMedianRecovery.BitMachine.RawDrop
namespace MetricKMedianRecovery.BitMachine.RawTake
open WordOperations BinaryArithmetic
noncomputable def number_computes : PolyComputes number :=
  NatOps.sub (discardPrefix_computes.comp UnaryResources.lengthBits_computes) extractPrefix_computes
attribute [local irreducible] number RawDrop.run
noncomputable def run_computes : PolyComputes run :=
  ((number_computes.pair (discardPrefix_computes.comp reverse_computes)).comp RawDrop.run_computes).comp reverse_computes
end MetricKMedianRecovery.BitMachine.RawTake

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SeedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList BinaryArithmetic
noncomputable def chunk (d : ℕ) (x : List Bool) : List Bool := RawTake.run (pairBits (width d x,
  RawDrop.run (pairBits ((value (width d x)*value (discardPrefix x)).bits,discardPrefix (extractPrefix x)))))
attribute [local irreducible] width RawTake.run RawDrop.run
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFillMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionPad
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def need (x : List Bool) : List Bool := (value (field 2 x)-value (lengthBits (field 1 x))).bits
attribute [local irreducible] need remaining BinaryNatSet.union
end MetricKMedianRecovery.BitMachine.BinaryCompletionPad

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Subsets
open WordOperations
variable {A : Type*}
noncomputable def added_computes : PolyComputes added := by
  unfold added
  simpa only [Function.comp_def] using
    (Find.item_computes.pair Fold.accum_computes).comp (mapWith_computes addLast_computes)
noncomputable def op_computes : PolyComputes op := Fold.accum_computes.append added_computes
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  ((cap d).computes.pair (Fold.pack_computes discardPrefix_computes (const_computes []) (const_computes (encode [[]])))).comp
    (CappedFold.run_computes op_computes)
end MetricKMedianRecovery.BitMachine.WordList.Subsets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field field_computes )
variable {n m : ℕ}
attribute [local irreducible] blueInput
attribute [local irreducible] records
attribute [local irreducible] bluePack
attribute [local irreducible] best
attribute [local irreducible] plan
attribute [local irreducible] rowInput
noncomputable def rows (x : List Bool) : List Bool := BinaryBranchRows.run (rowInput x)
attribute [local irreducible] rows
noncomputable def completion (d : ℕ) (x : List Bool) : List Bool := encode [field 2 x,field 3 x,extractPrefix (field 5 x),parts x,origins x,locations x,classOf 1 x,field 0 (plan d x),field 1 (plan d x),[],rows x]
attribute [local irreducible] completion
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_GridMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGrid
open WordOperations WordList BinaryArithmetic DyadicGrid
open BinaryOpeningPayment (field field_computes )
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def gf_computes (n : ℕ) : PolyComputes (gf n) := discardPrefix_computes.comp (field_computes n)
noncomputable def doubled_computes (n : ℕ) : PolyComputes (doubled n) := by
  change PolyComputes (fun x => (2*value (gf n x)).bits)
  simpa only [value_bits] using NatOps.mul (const_computes (2:ℕ).bits) (gf_computes n)
noncomputable def summed_computes : PolyComputes summed := NatOps.add (gf_computes 0) (gf_computes 1)
noncomputable def upLeft_computes : PolyComputes upLeft := list_computes [summed,doubled 1,doubled 2] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨summed_computes⟩
  · exact ⟨doubled_computes _⟩
  · exact ⟨doubled_computes _⟩)
noncomputable def upRight_computes : PolyComputes upRight := list_computes [doubled 0,summed,doubled 2] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨doubled_computes _⟩
  · exact ⟨summed_computes⟩
  · exact ⟨doubled_computes _⟩)
end MetricKMedianRecovery.BitMachine.BinaryGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_BisectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBisection
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def predWords_computes : PolyComputes predWords := by
  change PolyComputes (fun x=>(value x-1).bits)
  simpa only [value_bits,id_eq] using NatOps.sub id_computes (const_computes (1:ℕ).bits)
noncomputable def logWord_computes : PolyComputes logWord := UnaryResources.copy_computes predWords_computes (const_computes [true])
noncomputable def context_computes : PolyComputes context := list_computes [field 1,field 2,field 3,field 4] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
end MetricKMedianRecovery.BitMachine.BinaryBisection

end OAI
end


