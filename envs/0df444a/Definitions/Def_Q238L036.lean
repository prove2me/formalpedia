-- Prove2me | Definitions.Def_Q238L036
-- name    : Q238L036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:35:29.90333+00:00
-- url     : https://prove2.me/theorems/d6dd22e2-ed8c-40e1-93d1-d69e312aa0c7
-- title:
--   Definitions bundle Q238L036 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 92 declarations of OpenAI's Lean: 92 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.boundWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.coeffWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.solved_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.nextState_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.normWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.updated_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.zeroDirection_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.decision_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.op_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.fails_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.active_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.chooseActive`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.distance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.near_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.caps_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.columns_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.doubles_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.duals_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.kinds_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningEnumeration.triples_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.active_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.distance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.nearest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.paramV_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.paramZ_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.run_computes` and 52 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Machines_LoopInput2`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Values`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L032` and `Q238L033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L039` and `Q238L040`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L032
import Definitions.Def_Q238L033

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

noncomputable def normWords_computes : PolyComputes normWords :=
  (direction_computes.pair direction_computes).comp RationalArray.dotListsWords_computes
noncomputable def zeroDirection_computes : PolyComputes (fun x=>[zeroDirection x]) := by
  have hh := ((RatOps.ofWords normWords_computes).pair (RatOps.const 0)).comp BinaryRational.leWords_computes
  simpa only [zeroDirection,Function.comp_def,BinaryRational.leWords_pair] using hh
noncomputable def updated_computes : PolyComputes updated := by
  unfold updated
  simpa only [Function.comp_def] using
    (cutInput_computes.comp BinaryEllipsoidCut.shapeWords_computes).pair
      (cutInput_computes.comp BinaryEllipsoidCut.centerWords_computes)
noncomputable def nextState_computes : PolyComputes nextState := by
  have hh := (found_computes.comp isEmpty_computes).cond stored_computes
    (zeroDirection_computes.cond stored_computes updated_computes)
  unfold nextState
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
noncomputable def run_computes : PolyComputes run :=
  dim_computes.pair (precision_computes.pair (rows_computes.pair nextState_computes))
end BinaryEllipsoidAdvance
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

noncomputable def run_computes : PolyComputes run :=
  prepared_computes.comp (BoundedIteration.run_computes BinaryEllipsoidAdvance.run_computes)
end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

noncomputable def radiusSquare_computes : PolyComputes radiusSquare :=
  RatOps.mul (RatOps.nat radius_computes) (RatOps.nat radius_computes)
noncomputable def shapeWords_computes : PolyComputes shapeWords := by
  unfold shapeWords
  simpa only [Function.comp_def] using
    (nword_computes.pair radiusSquare_computes).comp BinaryEllipsoidInitial.run_computes
noncomputable def advanceInput_computes : PolyComputes advanceInput :=
  dimBits_computes.pair (gridWords_computes.pair (rows_computes.pair (shapeWords_computes.pair centerWords_computes)))
noncomputable def prepared_computes : PolyComputes prepared :=
  budgetWord_computes.pair (radius_computes.pair advanceInput_computes)
noncomputable def iterated_computes : PolyComputes iterated := prepared_computes.comp BinaryEllipsoidIteration.run_computes
noncomputable def result_computes : PolyComputes result := by
  have hh := (BinaryEllipsoidAdvance.found_computes.comp isEmpty_computes).cond
    (BinaryEllipsoidAdvance.center_computes.comp (prefix_computes true)) (const_computes [])
  unfold result
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
noncomputable def run_computes : PolyComputes run := iterated_computes.comp result_computes
end BinaryWeakSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundOp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

noncomputable def solved_computes : PolyComputes solved := prepared_computes.comp BinaryWeakSolve.run_computes
noncomputable def run_computes : PolyComputes run := by
  have hh := (solved_computes.comp isEmpty_computes).cond (const_computes [false]) (const_computes [true])
  unfold run
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases h : solved x=[] <;> simp [h]
end BinaryDecision
end
open WordOperations BinaryArithmetic
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

namespace BinaryBoundedDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryDecision.run_computes
end BinaryBoundedDecision
namespace BinaryClearRow
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid PolytopeCertificate
open WordList RationalMatrix

noncomputable def coeffWords_computes : PolyComputes coeffWords := by
  unfold coeffWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (scalar input,extractPrefix input))
      (g:=mapWith BinaryRational.mulWords)
      (scalar_computes.pair extractPrefix_computes) (mapWith_computes BinaryRational.mulWords_computes))
noncomputable def boundWords_computes : PolyComputes boundWords :=
  RatOps.mul (RatOps.nat denominator_computes) (RatOps.ofWords discardPrefix_computes)
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

end BinaryOpeningConstant
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

end OAI
end


