-- Prove2me | Definitions.Def_Q238K036
-- name    : Q238K036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:46.748636+00:00
-- url     : https://prove2.me/theorems/7e309c6d-0ef8-4f28-8ce4-7fb3a6ec689f
-- title:
--   Definitions bundle Q238K036 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 71 declarations of OpenAI's Lean: 71 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.decision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.op_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteInsert.keep_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteInsert.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.fails_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.chooseActive`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.chooseNear`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.active_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.chooseActive`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.constant_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.distance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.near_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.active_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.distance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.nearest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.paramV_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.paramZ_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.scale_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.values_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.contains_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.active_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.ceilWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.clearOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.clearedRows_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.prepared_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.bound_computes` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Machines_LoopInput2`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Values`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K032` and `Q238K033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K039` and `Q238K040`; the statements `OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionRealize_remain_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_demandWords_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalAnchor_integral_spec_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFinish_iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_run_of_candidates_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_run_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_step_pack_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionRealize_remain_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_demandWords_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalAnchor_integral_spec_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFinish_iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_run_of_candidates_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_run_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_step_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K032
import Definitions.Def_Q238K033

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DivNatWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

noncomputable def ceilWords_computes : PolyComputes ceilWords :=
  (negWords_computes.comp floorWords_computes).comp Signed.neg_computes

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

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

noncomputable def rightRowMap_computes : PolyComputes (mapWith RationalArray.dotListsWords) :=
  mapWith_computes RationalArray.dotListsWords_computes
noncomputable def rightRowOp_computes : PolyComputes rightRowOp :=
  PolyComputes.comp (f:=swapWords) (g:=mapWith RationalArray.dotListsWords)
    swapWords_computes rightRowMap_computes
noncomputable def mulMap_computes : PolyComputes (mapWith rightRowOp) := mapWith_computes rightRowOp_computes
noncomputable def mulWords_computes : PolyComputes mulWords :=
  PolyComputes.comp (f:=mulInput) (g:=mapWith rightRowOp) mulInput_computes mulMap_computes
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GetRow2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

noncomputable def diagAt_computes : PolyComputes diagAt := diagInput_computes.comp getEntry_computes
noncomputable def tailDiagValue_computes : PolyComputes tailDiagValue := tailDiagInput_computes.comp diagAt_computes

noncomputable def tailDiagOp_computes : PolyComputes tailDiagOp := by
  have hh := (NatOps.le discardPrefix_computes contextIndex_computes).cond
    (const_computes (BinaryRational.encode 0)) tailDiagValue_computes
  unfold tailDiagOp
  simpa only [decide_eq_true_eq] using hh
noncomputable def tailDiagMap_computes : PolyComputes tailDiagMap :=
  tailDiagMapInput_computes.comp (mapWith_computes tailDiagOp_computes)
noncomputable def tailDiag_computes : PolyComputes tailDiag := tailDiagMap_computes.comp RationalArray.sumWords_computes
noncomputable def negDiag_computes : PolyComputes negDiag :=
  (extractPrefix_computes.comp tailDiag_computes).comp BinaryRational.negWords_computes
noncomputable def muEntry_computes : PolyComputes muEntry := by
  have hl := NatOps.le discardPrefix_computes contextIndex_computes
  have hr := NatOps.le contextIndex_computes discardPrefix_computes
  have hh := hl.cond (hr.cond negDiag_computes (const_computes (BinaryRational.encode 0))) getEntry_computes
  unfold muEntry
  simpa only [decide_eq_true_eq] using hh

noncomputable def muRow_computes : PolyComputes muRow :=
  tailDiagMapInput_computes.comp (mapWith_computes muEntry_computes)
noncomputable def muWords_computes : PolyComputes muWords := matrixIndices_computes.comp (mapWith_computes muRow_computes)
noncomputable def stepInput_computes : PolyComputes stepInput := by
  unfold stepInput
  simpa only [Function.comp_def] using
    (PolyComputes.pair (f:=muWords ∘ discardPrefix) (g:=extractPrefix)
      (PolyComputes.comp (f:=discardPrefix) (g:=muWords)
        discardPrefix_computes muWords_computes) extractPrefix_computes)
noncomputable def stepWords_computes : PolyComputes stepWords := by
  unfold stepWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=stepInput) (g:=mulWords) stepInput_computes mulWords_computes)

end RationalMatrix
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
noncomputable def loopOp_computes : PolyComputes loopOp := by
  unfold loopOp
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=loopInput) (g:=stepWords) loopInput_computes stepWords_computes)
noncomputable def iterateWords_computes : PolyComputes iterateWords :=
  iterationInput_computes.comp (Fold.run_computes loopOp_computes (200*(Polynomial.X+1)^6))
noncomputable def rawDet_computes : PolyComputes rawDet :=
  (iterateWords_computes.comp WordList.head_computes).comp WordList.head_computes
noncomputable def determinantInput_computes : PolyComputes determinantInput :=
  Fold.pack_computes WordList.tail_computes (const_computes []) rawDet_computes
noncomputable def signedDet_computes : PolyComputes signedDet := determinantInput_computes.comp signRun_computes
noncomputable def determinantWords_computes : PolyComputes determinantWords := by
  have hh := isEmpty_computes.cond (const_computes (BinaryRational.encode 1)) signedDet_computes
  unfold determinantWords
  simpa only [decide_eq_true_eq] using hh
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

namespace BinaryClearRow
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid PolytopeCertificate
open WordList RationalMatrix

noncomputable def run_computes : PolyComputes run := coeffWords_computes.pair boundWords_computes
end BinaryClearRow
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

noncomputable def clearOp_computes : PolyComputes clearOp := discardPrefix_computes.comp BinaryClearRow.run_computes
noncomputable def clearedRows_computes : PolyComputes clearedRows := by
  unfold clearedRows
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],rows input)) (g:=mapWith clearOp)
      ((const_computes []).pair rows_computes) (mapWith_computes clearOp_computes))
noncomputable def prepared_computes : PolyComputes prepared :=
  first_computes.pair (second_computes.pair (bound_computes.pair clearedRows_computes))
noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryBoundedDecision.run_computes
end BinaryRationalDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FaceSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryFace
open WordList
noncomputable def decision_computes : PolyComputes decision := decisionInput_computes.comp BinaryRationalDecision.run_computes
noncomputable def op_computes : PolyComputes op :=
  (decision_computes.comp MetricKMedianRecovery.BitMachine.head_computes).cond proposed_computes Find.accum_computes
noncomputable def run_computes : PolyComputes run := Fold.run_computes op_computes (4*Polynomial.X+4)
end BinaryFace
namespace BinaryFinalFace
open WordList BinaryRationalDecision
noncomputable def run_computes : PolyComputes run :=
  (Fold.pack_computes allRows_computes context_computes (const_computes [])).comp BinaryFace.run_computes
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

noncomputable def cramerOp_computes : PolyComputes cramerOp := by
  unfold cramerOp
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=updateColWords ∘ cramerOpInput) (g:=determinantWords)
      (PolyComputes.comp (f:=cramerOpInput) (g:=updateColWords)
        cramerOpInput_computes updateColWords_computes) determinantWords_computes)
noncomputable def cramerWords_computes : PolyComputes cramerWords := by
  unfold cramerWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=cramerInput) (g:=mapWith cramerOp)
      cramerInput_computes (mapWith_computes cramerOp_computes))
noncomputable def firstDet_computes : PolyComputes firstDet :=
  PolyComputes.comp (f:=extractPrefix) (g:=determinantWords) extractPrefix_computes determinantWords_computes
noncomputable def inverseDet_computes : PolyComputes inverseDet :=
  PolyComputes.comp (f:=firstDet) (g:=BinaryRational.invWords) firstDet_computes BinaryRational.invWords_computes
noncomputable def solveInput_computes : PolyComputes solveInput := inverseDet_computes.pair cramerWords_computes
noncomputable def solveWords_computes : PolyComputes solveWords := by
  unfold solveWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=solveInput) (g:=mapWith BinaryRational.mulWords)
      solveInput_computes (mapWith_computes BinaryRational.mulWords_computes))
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

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
noncomputable def transposed_computes : PolyComputes transposed := by
  unfold transposed
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (first input,(coeffs ∘ BinaryFinalFace.run) input))
      (g:=Rectangular.transpose)
      (first_computes.pair
        (PolyComputes.comp (f:=BinaryFinalFace.run) (g:=coeffs) BinaryFinalFace.run_computes coeffs_computes))
      Rectangular.transpose_computes)
noncomputable def gram_computes : PolyComputes gram := by
  unfold gram
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (transposed input,transposed input)) (g:=mapWith rightRowOp)
      (transposed_computes.pair transposed_computes) mulMap_computes)
noncomputable def rhs_computes : PolyComputes rhs := by
  unfold rhs
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (transposed input,(bounds ∘ BinaryFinalFace.run) input))
      (g:=RationalMatrix.mulVec)
      (transposed_computes.pair
        (PolyComputes.comp (f:=BinaryFinalFace.run) (g:=bounds) BinaryFinalFace.run_computes bounds_computes))
      mulVec_computes)
noncomputable def point_computes : PolyComputes point := by
  unfold point
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (gram input,rhs input)) (g:=solveWords)
      (gram_computes.pair rhs_computes) solveWords_computes)
noncomputable def run_computes : PolyComputes run :=
  (BinaryRationalDecision.run_computes.comp MetricKMedianRecovery.BitMachine.head_computes).cond
    (point_computes.comp (prefix_computes true)) (const_computes [])
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
namespace RatOps
noncomputable def le {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>[decide (f x≤g x)]) := by
  have hh := (hf.pair hg).comp BinaryRational.leWords_computes
  simpa only [Function.comp_def,BinaryRational.leWords_pair] using hh
end RatOps
namespace BinaryOpeningActivity
open WordList

noncomputable def fails_computes : PolyComputes (fun x=>[fails x]) :=
  RatOps.le
    (RatOps.mul (RatOps.sub (RatOps.const 1) (RatOps.mul (RatOps.const 3)
      (RatOps.ofWords paramV_computes))) (RatOps.ofWords distanceWord_computes))
    (RatOps.ofWords paramZ_computes)
noncomputable def run_computes : PolyComputes run := (Find.run_computes fails_computes).comp isEmpty_computes
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
namespace RationalMin
open WordList
noncomputable def choose_computes : PolyComputes choose := by
  have hh := (RatOps.le (RatOps.ofWords Find.item_computes)
    (RatOps.ofWords Fold.accum_computes)).cond Find.item_computes Fold.accum_computes
  unfold choose
  simpa only [decide_eq_true_eq] using hh
noncomputable def run_computes : PolyComputes run :=
  (Fold.pack_computes id_computes (const_computes []) seed_computes).comp
    (Fold.run_computes choose_computes (3*Polynomial.X+3))
end RationalMin
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
open WordOperations BinaryArithmetic WordList BinaryOpeningActivity
noncomputable def run_computes : PolyComputes run := values_computes.comp RationalMin.run_computes
end MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RatOps
noncomputable def max {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (max (f x) (g x))) := by
  have hh := (le hf hg).cond hg hf
  simpa only [decide_eq_true_eq,max_def,apply_ite] using hh
end RatOps
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

noncomputable def paramV_computes : PolyComputes (fun x=>BinaryRational.encode (paramV x)) :=
  RatOps.ofWords (itemField_computes 2)
noncomputable def paramZ_computes : PolyComputes (fun x=>BinaryRational.encode (paramZ x)) :=
  RatOps.ofWords (itemField_computes 3)
noncomputable def scale_computes : PolyComputes (fun x=>BinaryRational.encode (scale x)) :=
  RatOps.sub (RatOps.const 1) (RatOps.mul (RatOps.const 3) paramV_computes)
noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  (activityInput_computes.comp BinaryOpeningActivity.run_computes).comp
    MetricKMedianRecovery.BitMachine.head_computes
noncomputable def nearest_computes : PolyComputes (fun x=>BinaryRational.encode (nearest x)) := by
  unfold nearest
  simpa only [Function.comp_def] using
    (RatOps.ofWords (f:=BinaryOpeningNearest.run ∘ activityInput)
      (PolyComputes.comp (f:=activityInput) (g:=BinaryOpeningNearest.run)
        activityInput_computes BinaryOpeningNearest.run_computes))
noncomputable def distance_computes : PolyComputes (fun x=>BinaryRational.encode (distance x)) :=
  RatOps.ofWords distanceWords_computes
noncomputable def summand_computes : PolyComputes (fun x=>BinaryRational.encode (summand x)) := by
  have hsd := RatOps.mul scale_computes distance_computes
  have ha := (RatOps.le distance_computes (RatOps.mul paramV_computes paramZ_computes)).cond
    (RatOps.neg hsd) (RatOps.max (RatOps.sub paramZ_computes hsd) (RatOps.const 0))
  have hi := RatOps.max (RatOps.sub (RatOps.mul scale_computes nearest_computes) hsd) (RatOps.const 0)
  have hh := active_computes.cond ha hi
  unfold summand
  simpa only [decide_eq_true_eq,apply_ite] using hh

noncomputable def values_computes : PolyComputes values := input_computes.comp (mapWith_computes summand_computes)
noncomputable def sumWords_computes : PolyComputes sumWords := values_computes.comp RationalArray.sumWords_computes
noncomputable def run_computes : PolyComputes run :=
  RatOps.sub
    (RatOps.sub (RatOps.ofWords (field_computes 4))
      (RatOps.mul (RatOps.nat ((field_computes 7).comp UnaryResources.lengthBits_computes))
        (RatOps.ofWords (field_computes 5))))
    (RatOps.ofWords sumWords_computes)

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
namespace BinaryOpeningConstant
open WordList RationalLinearFeasibility RationalOpenability

noncomputable def active_computes (k : ℕ) : PolyComputes (fun x=>[active k x]) :=
  (query_computes k).comp BinaryOpeningPayment.active_computes
noncomputable def distance_computes (f j : ℕ) : PolyComputes (fun x=>BinaryRational.encode (distance f j x)) :=
  RatOps.ofWords (distanceWords_computes f j)
noncomputable def chooseActive {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if active k x then f x else g x)) := by
  have hh := (active_computes k).cond hf hg
  simpa only [apply_ite] using hh
noncomputable def near_computes : PolyComputes (fun x=>[decide (near x)]) := by
  have distanceComputes : PolyComputes
      (fun input=>BinaryRational.encode (BinaryOpeningPayment.distance (query 1 input))) := by
    simpa only [Function.comp_def] using
      (PolyComputes.comp (f:=query 1)
        (g:=fun input=>BinaryRational.encode (BinaryOpeningPayment.distance input))
        (query_computes 1) BinaryOpeningPayment.distance_computes)
  unfold near
  exact RatOps.le distanceComputes
    (RatOps.mul BinaryOpeningPayment.paramV_computes BinaryOpeningPayment.paramZ_computes)
noncomputable def constant_computes : PolyComputes (fun x=>BinaryRational.encode (constant x)) := by
  have hz := BinaryOpeningPayment.paramZ_computes
  have hv := BinaryOpeningPayment.paramV_computes
  have h0 := RatOps.const 0
  have hn : PolyComputes (fun x=>BinaryRational.encode (if near x then 0 else -BinaryOpeningPayment.paramZ x)) := by
    have hh := near_computes.cond h0 (RatOps.neg hz)
    simpa only [decide_eq_true_eq,apply_ite] using hh
  exact chooseTag 0 (chooseActive 1 hz h0)
    (chooseTag 1 (chooseActive 1 (RatOps.neg (RatOps.mul (RatOps.add (RatOps.const 1) (RatOps.mul hv hv)) hz)) h0)
    (chooseTag 2 (chooseActive 1 (RatOps.neg (RatOps.mul BinaryOpeningPayment.scale_computes (distance_computes 2 1))) h0)
    (chooseTag 3 (chooseActive 1 hn h0)
    (chooseTag 4 (RatOps.ofWords (extractPrefix_computes.comp BinaryOpeningPayment.run_computes))
    (chooseTag 6 (chooseActive 3
      (chooseActive 1 (RatOps.neg (distance_computes 2 1))
        (RatOps.neg (RatOps.add (RatOps.mul (RatOps.const 2) (distance_computes 2 1)) (distance_computes 2 3)))) h0)
    (chooseTag 7 (chooseActive 1 (RatOps.neg (RatOps.ofWords (BinaryOpeningPayment.itemField_computes 4))) h0) h0))))))

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
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility RationalOpenability

noncomputable def chooseActive {f g : List Bool → ℚ} (k : ℕ)
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningConstant.active k (extractPrefix x) then f x else g x)) := by
  have hh := (extractPrefix_computes.comp (BinaryOpeningConstant.active_computes k)).cond hf hg
  simpa only [Function.comp_def,apply_ite] using hh
noncomputable def chooseNear {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (if BinaryOpeningConstant.near (extractPrefix x) then f x else g x)) := by
  have hh := (extractPrefix_computes.comp BinaryOpeningConstant.near_computes).cond hf hg
  simpa only [Function.comp_def,decide_eq_true_eq,apply_ite] using hh

end BinaryOpeningCoefficient
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
noncomputable def bound_computes : PolyComputes (fun x=>BinaryRational.encode (bound x)) :=
  RatOps.mul (RatOps.add (RatOps.const 1) (RatOps.mul (RatOps.ofWords (field_computes 2))
    (RatOps.ofWords (field_computes 2)))) (RatOps.ofWords (field_computes 3))
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

noncomputable def contains_computes : PolyComputes (fun x=>[contains x]) := by
  have h := ((Find.run_computes natEq_computes).comp isEmpty_computes).cond
    (const_computes [false]) (const_computes [true])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases hx : Find.run natEq x=[] <;> simp [contains,hx]
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
namespace BinaryFiniteInsert
open WordList BinaryPhaseFirst EffectiveOpenability
noncomputable def keep_computes : PolyComputes (fun x=>[keep x]) := by
  have h := ((new_computes.pair discardPrefix_computes).comp natEq_computes).cond
    (const_computes [true]) ((discardPrefix_computes.pair old_computes).comp contains_computes)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  cases he : natEq (pairBits (new x,discardPrefix x)) <;> simp only [keep,he,Function.comp_apply,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
noncomputable def run_computes : PolyComputes run := filterWith_computes keep_computes
end BinaryFiniteInsert
end MetricKMedianRecovery.BitMachine

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

noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  ((extractPrefix_computes.comp context_computes).pair discardPrefix_computes).comp BinaryOpeningPayment.active_computes
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

end OAI
end


