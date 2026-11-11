-- Prove2me | Definitions.Def_Q238K029
-- name    : Q238K029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:24:03.758394+00:00
-- url     : https://prove2.me/theorems/1f86d510-a150-4d8c-a8df-9cefb726caf5
-- title:
--   Definitions bundle Q238K029 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 166 declarations of OpenAI's Lean: 164 definitions and 2 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.block`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.entry`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.menus`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBisection.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.score_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.invalid_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.payloadOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.scoreOp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.loop`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.newBest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.newTable`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.payload_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.prepare`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.states`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueStates.blocks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueStates.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.lhs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.rhs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.greenContext`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.greenOracle`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.oracle`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.best`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.blueInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.records`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.base`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow` and 124 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueLookup`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BlueNextTable`, `KMedianRecovery_Branching_BlueProgram`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_BlueTableSize`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchPhysical`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_LabelMember`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Encoding_WordSubsets`, `KMedianRecovery_Machines_ActionMachine`, `KMedianRecovery_Machines_BisectionMachine`, `KMedianRecovery_Machines_DeleteSize`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Machines_LoopInput2`, `KMedianRecovery_Recovery_Answer`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FilterItem`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_Next`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack11`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_SortMath`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K024`, `Q238K025` and `Q238K026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K032`, `Q238K033`, `Q238K034` and `Q238K035`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_matrix_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteMachine_initial_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryInitialAuto_initialInput_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalSearch_run_word_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalSearch_step_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningNearest_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseAdvance_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.answer_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseTrace_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_weights_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_successful_probability_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_matrix_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteMachine_initial_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryInitialAuto_initialInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalSearch_run_word_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalSearch_step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningConstant_constant_source_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningNearest_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningPayment_nearest_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseAdvance_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.answer_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseTrace_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowWord_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_weights_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_successful_probability_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K024
import Definitions.Def_Q238K025
import Definitions.Def_Q238K026

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList
namespace Zip

noncomputable def op_computes : PolyComputes op := by
  let a : PolyComputes (fun x=>discardPrefix (discardPrefix x)) := discardPrefix_computes.comp discardPrefix_computes
  let ys : PolyComputes (fun x=>extractPrefix (discardPrefix (discardPrefix x))) := a.comp extractPrefix_computes
  let os : PolyComputes (fun x=>discardPrefix (discardPrefix (discardPrefix x))) := a.comp discardPrefix_computes
  have hh := ys.comp isEmpty_computes
  have hv := (discardPrefix_computes.comp extractPrefix_computes).pair (ys.comp head_computes)
  have ht := (ys.comp tail_computes).pair (cons_computes hv os)
  unfold op
  simpa only [Function.comp_def,decide_eq_true_eq] using hh.cond a ht
end Zip
end WordList
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryResources
lemma cap_length (x : List Bool) : (cap.word x).length=2*x.length+2 := by
  rw [cap.word_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
lemma lengthBits_eq (x : List Bool) : lengthBits x=x.length.bits := by
  unfold lengthBits
  rw [BoundedIteration.run_eq,inc_iter]
  intro j hj
  rw [inc_iter,cap_length]
  exact (WordList.Indices.bits_length_le j).trans (by omega)

noncomputable def threePower_computes : PolyComputes threePower :=
  (id_computes.pair (cap.computes.pair (const_computes (1:ℕ).bits))).comp
    (BoundedIteration.run_computes triple_computes)
end UnaryResources
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
namespace RationalArray
open RationalHeight
noncomputable def sumInput_computes : PolyComputes sumInput :=
  WordList.Fold.pack_computes id_computes (const_computes []) (const_computes (BinaryRational.encode 0))
end RationalArray
namespace RationalMatrix
open WordList

noncomputable def swapWords_computes : PolyComputes swapWords :=
  discardPrefix_computes.pair extractPrefix_computes
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

noncomputable def diagInput_computes : PolyComputes diagInput := id_computes.pair discardPrefix_computes
noncomputable def contextMatrix_computes : PolyComputes contextMatrix := extractPrefix_computes.comp extractPrefix_computes
noncomputable def contextIndex_computes : PolyComputes contextIndex := extractPrefix_computes.comp discardPrefix_computes
noncomputable def tailDiagInput_computes : PolyComputes tailDiagInput := contextMatrix_computes.pair discardPrefix_computes

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Next
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinarySqrt

noncomputable def low_computes : PolyComputes low := discardPrefix_computes.comp extractPrefix_computes
noncomputable def high_computes : PolyComputes high := discardPrefix_computes.comp discardPrefix_computes

noncomputable def startWords_computes : PolyComputes startWords := by
  have hs := NatOps.add id_computes (const_computes (Nat.bits 1))
  have hh := id_computes.pair ((const_computes []).pair hs)
  change PolyComputes (fun x => pairBits (x,pairBits ([],(value x+1).bits)))
  simpa only [value_bits,id_eq] using hh
end BinarySqrt
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NumAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryEllipsoidRoot

noncomputable def numAbs_computes : PolyComputes numAbs :=
  (extractPrefix_computes.comp extractPrefix_computes).comp tail_computes
noncomputable def den_computes : PolyComputes den := extractPrefix_computes.comp discardPrefix_computes
noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes

noncomputable def radicand_computes : PolyComputes radicand := by
  have hh := NatOps.mul (NatOps.mul numAbs_computes den_computes)
    (NatOps.mul precision_computes precision_computes)
  change PolyComputes (fun x => (value (numAbs x)*value (den x)*(value (precision x)*value (precision x))).bits)
  simpa only [value_bits] using hh
noncomputable def denom_computes : PolyComputes denom := NatOps.mul den_computes precision_computes
end BinaryEllipsoidRoot
open WordOperations BinaryArithmetic
open scoped Matrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
open RationalMatrix

noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
noncomputable def rest_computes : PolyComputes rest := discardPrefix_computes
noncomputable def shape_computes : PolyComputes shape := rest_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest_computes.comp discardPrefix_computes
noncomputable def direction_computes : PolyComputes direction := rest₂_computes.comp extractPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
noncomputable def center_computes : PolyComputes center := rest₃_computes.comp extractPrefix_computes
noncomputable def precision_computes : PolyComputes precision := rest₃_computes.comp discardPrefix_computes
noncomputable def haInput_computes : PolyComputes haInput := shape_computes.pair direction_computes
noncomputable def dimension_computes : PolyComputes (fun x=>BinaryRational.encode (dimension x)) := RatOps.nat dim_computes
noncomputable def rootPrecision_computes : PolyComputes (fun x=>(rootPrecision x).bits) := by
  have hh := NatOps.mul (const_computes (Nat.bits 32)) dim_computes
  change PolyComputes (fun x=>(32*value (dim x)).bits)
  simpa only [value_bits] using hh
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidGrid
open RationalMatrix WordList

noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes.comp extractPrefix_computes
noncomputable def shape_computes : PolyComputes shape := discardPrefix_computes.comp discardPrefix_computes
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes

noncomputable def entryInput_computes : PolyComputes entryInput :=
  ((ctx_computes.comp shape_computes).pair row_computes).pair col_computes
noncomputable def dimension_computes : PolyComputes (fun x=>BinaryRational.encode (dimension x)) :=
  RatOps.nat (ctx_computes.comp dim_computes)
noncomputable def scale_computes : PolyComputes (fun x=>BinaryRational.encode (scale x)) :=
  RatOps.nat (ctx_computes.comp precision_computes)
end BinaryEllipsoidGrid
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryRow
open RationalMatrix

noncomputable def bound_computes : PolyComputes bound := discardPrefix_computes.comp discardPrefix_computes
end BinaryRow
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := discardPrefix_computes.comp discardPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp extractPrefix_computes
noncomputable def stored_computes : PolyComputes stored := rest₂_computes.comp discardPrefix_computes
noncomputable def shape_computes : PolyComputes shape := stored_computes.comp extractPrefix_computes
noncomputable def center_computes : PolyComputes center := stored_computes.comp discardPrefix_computes
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
noncomputable def loopInput_computes : PolyComputes loopInput :=
  extractPrefix_computes.pair (discardPrefix_computes.comp discardPrefix_computes)
noncomputable def iterationInput_computes : PolyComputes iterationInput :=
  Fold.pack_computes WordList.tail_computes id_computes id_computes
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

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidInitial
open RationalMatrix WordList

noncomputable def zeroVector_computes : PolyComputes zeroVector :=
  (id_computes.pair (const_computes (BinaryRational.encode 0))).comp repeatWords_computes
end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

noncomputable def prepared_computes : PolyComputes prepared :=
  extractPrefix_computes.pair (boundCounter.computes.pair (discardPrefix_computes.comp discardPrefix_computes))
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

noncomputable def nword_computes : PolyComputes nword := extractPrefix_computes
noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
noncomputable def pword_computes : PolyComputes pword := rest₁_computes.comp extractPrefix_computes
noncomputable def sword_computes : PolyComputes sword := rest₂_computes.comp extractPrefix_computes
noncomputable def radius_computes : PolyComputes radius := rest₃_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₃_computes.comp discardPrefix_computes
noncomputable def twice_computes : PolyComputes twice := nword_computes.append nword_computes
noncomputable def blocks_computes : PolyComputes blocks :=
  ((copy_computes nword_computes nword_computes).append
    (copy_computes twice_computes (pword_computes.append sword_computes))).append (const_computes [true])
noncomputable def budgetWord_computes : PolyComputes budgetWord := copy_computes twice_computes blocks_computes
noncomputable def powerWords_computes : PolyComputes powerWords :=
  (budgetWord_computes.append (const_computes [true])).comp threePower_computes
noncomputable def centerWords_computes : PolyComputes centerWords :=
  nword_computes.comp BinaryEllipsoidInitial.zeroVector_computes
end BinaryWeakSolve
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

noncomputable def entries_computes : PolyComputes entries := cons_computes discardPrefix_computes extractPrefix_computes
end BinaryClearRow

open WordOperations
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
namespace WordList.Set

noncomputable def target_computes : PolyComputes target :=
  (extractPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def replacement_computes : PolyComputes replacement :=
  (extractPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def oldInput_computes : PolyComputes oldInput :=
  discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)
end WordList.Set
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

noncomputable def cramerOpInput_computes : PolyComputes cramerOpInput :=
  (extractPrefix_computes.comp extractPrefix_computes).pair
    (discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes))
end RationalMatrix
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

noncomputable def context_computes : PolyComputes context := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes
end MetricTable
namespace BinaryOpeningActivity
open WordList

noncomputable def table_computes : PolyComputes table :=
  (extractPrefix_computes.comp extractPrefix_computes).comp extractPrefix_computes
noncomputable def client_computes : PolyComputes client :=
  (extractPrefix_computes.comp extractPrefix_computes).comp discardPrefix_computes
noncomputable def paramV_computes : PolyComputes paramV :=
  (extractPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def paramZ_computes : PolyComputes paramZ :=
  (extractPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
namespace RationalMin
open WordList
noncomputable def seed_computes : PolyComputes seed := by
  have hh := isEmpty_computes.cond (const_computes (BinaryRational.encode 0)) WordList.head_computes
  unfold seed
  simpa only [decide_eq_true_eq] using hh
end RationalMin
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
open WordOperations WordList BinaryArithmetic
variable {A : Type*}
noncomputable def score_computes : PolyComputes score := WordList.head_computes.comp extractPrefix_computes

end MetricKMedianRecovery.BitMachine.BinaryBlueChoice

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
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def list_computes (fs : List (List Bool → List Bool)) (hs : ∀ f∈fs, PolyComputes f) :
    PolyComputes (fun x=>encode (fs.map (fun f=>f x))) := by
  induction fs with
  | nil=>exact const_computes []
  | cons f fs ih=>exact cons_computes (hs f (List.mem_cons_self ..)) (ih (fun g hg=>hs g (List.mem_cons_of_mem _ hg)))
end WordList
namespace BinaryOpeningEnumeration
open WordList EffectiveOpenability RationalOpenability BinaryOpeningPayment
noncomputable def unaryTag_computes (tag : ℕ) : PolyComputes (unaryTag tag) :=
  cons_computes (const_computes tag.bits) (cons_computes id_computes (const_computes []))
noncomputable def pairTag_computes (tag : ℕ) : PolyComputes (pairTag tag) :=
  cons_computes (const_computes tag.bits)
    (cons_computes extractPrefix_computes (cons_computes discardPrefix_computes (const_computes [])))
noncomputable def tripleTag_computes (tag : ℕ) : PolyComputes (tripleTag tag) :=
  cons_computes (const_computes tag.bits)
    (cons_computes (discardPrefix_computes.comp discardPrefix_computes)
      (cons_computes extractPrefix_computes (cons_computes (discardPrefix_computes.comp extractPrefix_computes) (const_computes []))))
noncomputable def dualTag_computes : PolyComputes dualTag :=
  cons_computes (const_computes (7:ℕ).bits)
    (cons_computes discardPrefix_computes (cons_computes extractPrefix_computes (const_computes [])))
noncomputable def variableTag_computes : PolyComputes variableTag :=
  cons_computes (const_computes (1:ℕ).bits)
    (cons_computes extractPrefix_computes (cons_computes (discardPrefix_computes.comp extractPrefix_computes)
      (cons_computes (discardPrefix_computes.comp discardPrefix_computes) (const_computes []))))
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

namespace MetricKMedianRecovery.BitMachine.BinaryBlueMerge
open WordOperations WordList
variable {A : Type*}
noncomputable def payload_computes : PolyComputes payload := WordList.head_computes.comp discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryBlueMerge

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordOperations WordList
variable {A : Type*}
noncomputable def invalid_computes : PolyComputes (fun x=>[invalid x]) := discardPrefix_computes.comp isEmpty_computes
noncomputable def scoreOp_computes : PolyComputes scoreOp := discardPrefix_computes.comp BinaryBlueChoice.score_computes
attribute [local irreducible] mapWith
noncomputable def payloadOp_computes : PolyComputes payloadOp := discardPrefix_computes.comp BinaryBlueMerge.payload_computes
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FilterItem
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def filterItem_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (filterItem p) := by
  have h := hp.cond (cons_computes discardPrefix_computes (const_computes [])) (const_computes [])
  change PolyComputes (fun x=>if p x then encode [discardPrefix x] else [])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl
end WordList
namespace BinaryFiniteInsert
open WordList BinaryPhaseFirst EffectiveOpenability
noncomputable def old_computes : PolyComputes old := extractPrefix_computes.comp extractPrefix_computes
noncomputable def new_computes : PolyComputes new := extractPrefix_computes.comp discardPrefix_computes
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

noncomputable def context_computes : PolyComputes context := extractPrefix_computes.comp extractPrefix_computes
noncomputable def oldBudget_computes : PolyComputes oldBudget := extractPrefix_computes.comp discardPrefix_computes
noncomputable def newFacility_computes : PolyComputes newFacility := discardPrefix_computes.comp extractPrefix_computes
noncomputable def newBudget_computes : PolyComputes newBudget := discardPrefix_computes.comp discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Answer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def answer (x : List Bool) : List Bool :=
  BinaryPhaseFirst.run (pairBits (extractPrefix x,allFacilities (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
open BinaryPhaseFinish
noncomputable def answer : List Bool → List Bool := BinaryPhaseFinish.answer ∘ extractPrefix
noncomputable def step (x : List Bool) : List Bool :=
  if answer x=[] then x else pairBits
    (BinaryPhaseUpdate.run (pairBits (extractPrefix x,(answer x).tail)),cons (answer x).tail (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryPhaseTrace

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

noncomputable def reverseTest_computes {p : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) : PolyComputes (fun x=>[reverseTest p x]) :=
  (discardPrefix_computes.pair extractPrefix_computes).comp hp

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

noncomputable def levelWords_computes : PolyComputes levelWords := extractPrefix_computes
noncomputable def parentWords_computes : PolyComputes parentWords := discardPrefix_computes.comp extractPrefix_computes
noncomputable def heightWords_computes : PolyComputes heightWords := discardPrefix_computes.comp discardPrefix_computes

noncomputable def table_computes : PolyComputes table := extractPrefix_computes.comp extractPrefix_computes
noncomputable def label_computes : PolyComputes label := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes
attribute [local irreducible] MetricTable.get
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordOperations WordList RationalLeaves
attribute [local irreducible] mapWith

noncomputable def table_computes : PolyComputes table := (extractPrefix_computes.comp extractPrefix_computes).comp extractPrefix_computes
noncomputable def item_computes : PolyComputes item := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryLabelMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelMember
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open WordOperations BinaryArithmetic WordList RationalLeaves EffectiveOpenability

noncomputable def alphabet_computes : PolyComputes alphabet := extractPrefix_computes.comp extractPrefix_computes
noncomputable def target_computes : PolyComputes target := extractPrefix_computes.comp discardPrefix_computes
noncomputable def index_computes : PolyComputes index := discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
noncomputable def lengthBits : List Bool → List Bool := UnaryResources.lengthBits ∘ Count.run
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawTake
open WordOperations BinaryArithmetic
noncomputable def number (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (discardPrefix x))-value (extractPrefix x)).bits
noncomputable def run (x : List Bool) : List Bool :=
  (RawDrop.run (pairBits (number x,(discardPrefix x).reverse))).reverse
attribute [local irreducible] number RawDrop.run
end MetricKMedianRecovery.BitMachine.RawTake

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
noncomputable def addLast_computes : PolyComputes addLast :=
  discardPrefix_computes.append (cons_computes extractPrefix_computes (const_computes []))
noncomputable def cap (d : ℕ) : PolynomialCounter ((Polynomial.X+1)^d) := PolynomialCounter.choose _
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  CappedFold.run op (pairBits ((cap d).word x,Fold.pack (discardPrefix x) [] (encode [[]])))
end MetricKMedianRecovery.BitMachine.WordList.Subsets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
variable {n : ℕ}
noncomputable def run (d : ℕ) : List Bool→List Bool := Subsets.run d
noncomputable def blocks (d : ℕ) (x : List Bool) : List Bool := filterWith nonemptyKey (pairBits ([],run d x))
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select
  (mapWith op (pairBits (x,BinaryBlueStates.blocks 3 x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueNextTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueTable
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def row (x : List Bool) : List Bool := pairBits (discardPrefix x,BinaryBlueCell.run x)
noncomputable def next (x : List Bool) : List Bool := mapWith row (pairBits (x,field 2 x))
end MetricKMedianRecovery.BitMachine.BinaryBlueTable

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTableSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLoop
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def newTable (x : List Bool) : List Bool := BinaryBlueTable.next (nextCtx x)
noncomputable def newBest (x : List Bool) : List Bool := BinaryBlueChoice.run
  (pairBits (oldBest x,BinaryBlueLookup.run (pairBits (field 3 (extractPrefix x),newTable x))))
noncomputable def step (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (newTable x,newBest x))
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
noncomputable def loop (x : List Bool) : List Bool := BoundedIteration.run step
  (pairBits (field 4 x,pairBits (cap.word x,initial x)))
noncomputable def run (x : List Bool) : List Bool := if field 3 x=[] then BinaryBlueChoice.encode id (some (0,[])) else oldBest (loop x)
end MetricKMedianRecovery.BitMachine.BinaryBlueLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueProgram
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def states (d : ℕ) (x : List Bool) : List Bool := BinaryBlueStates.run d (pairBits (x,field 2 x))
noncomputable def prepare (d : ℕ) (x : List Bool) : List Bool := encode [field 0 x,field 1 x,states d x,field 2 x,field 3 x]
noncomputable def run (d : ℕ) : List Bool→List Bool := BinaryBlueLoop.run ∘ prepare d
end MetricKMedianRecovery.BitMachine.BinaryBlueProgram

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
attribute [local irreducible] remaining
noncomputable def context (x : List Bool) : List Bool := encode [lengthBits (field 0 x),field 4 x,remaining x,discardPrefix (field 5 x)]
attribute [local irreducible] context
noncomputable def oracle (x : List Bool) : List Bool := encode [field 0 x,field 1 x,context x]
attribute [local irreducible] oracle
attribute [local irreducible] classOf
noncomputable def greenContext (x : List Bool) : List Bool := encode [lengthBits (field 0 x),field 4 x,classOf 0 x,discardPrefix (field 5 x)]
attribute [local irreducible] greenContext
noncomputable def greenOracle (x : List Bool) : List Bool := encode [field 0 x,field 1 x,greenContext x]
attribute [local irreducible] greenOracle
attribute [local irreducible] ballInput
attribute [local irreducible] copyData
noncomputable def parts (x : List Bool) : List Bool := BinaryCopyTables.parts (copyData x)
attribute [local irreducible] parts
attribute [local irreducible] origins
attribute [local irreducible] locations
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

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
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def runCap : PolynomialCounter runCapPoly := PolynomialCounter.choose _
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRows
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n q r : ℕ}
noncomputable def base (j : ℕ) (x : List Bool) : List Bool := extractPrefix (BinarySamplingOracle.reference (oracleInput j x))
noncomputable def capRow (j : ℕ) (x : List Bool) : List Bool := encode [base j x,distances x]
noncomputable def weight (x : List Bool) : List Bool := BinaryAssignmentWeight.run (pairBits
  (discardPrefix x,BinaryAssignmentWeight.identities (field 0 (extractPrefix x))))
noncomputable def redRow (x : List Bool) : List Bool := pairBits (weight x,capRow 1 x)
noncomputable def clients (x : List Bool) : List Bool := mapWith (capRow 0) (pairBits (x,field 1 (field 0 x)))
noncomputable def reds (x : List Bool) : List Bool := mapWith redRow (pairBits (x,field 3 x))
noncomputable def run (x : List Bool) : List Bool := encode [field 4 x,clients x,reds x]
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

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
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def blueInput (x : List Bool) : List Bool := encode [oracle x,classOf 2 x,field 7 x]
attribute [local irreducible] blueInput
noncomputable def records (x : List Bool) : List Bool := BinaryBlueRecords.run (blueInput x)
attribute [local irreducible] records
noncomputable def bluePack (x : List Bool) : List Bool := encode [records x,field 2 x,field 8 x,field 10 x,field 11 x]
attribute [local irreducible] bluePack
noncomputable def best (d : ℕ) (x : List Bool) : List Bool := BinaryBlueProgram.run d (bluePack x)
attribute [local irreducible] best
noncomputable def plan (d : ℕ) (x : List Bool) : List Bool := BinaryBlueOutput.run (pairBits (best d x,field 8 x))
attribute [local irreducible] plan
noncomputable def rowInput (x : List Bool) : List Bool := encode [oracle x,greenOracle x,locations x,classOf 1 x,field 9 x]
attribute [local irreducible] rowInput
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def lhs (x : List Bool) : List Bool := (value (lengthBits (discardPrefix (field 5 x)))+(field 10 x).length).bits
noncomputable def rhs (x : List Bool) : List Bool :=
  (value (lengthBits (extractPrefix (field 5 x)))+value (field 9 x)+value (lengthBits (field 8 x))).bits
noncomputable def run (x : List Bool) : Bool :=
  decide (outside x=[] ∧ badBalls x=[] ∧ badRadii x=[] ∧ value (field 9 x)≤value (lengthBits (classOf 1 x)) ∧ value (lhs x)≤value (rhs x))
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ActionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryActions
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open RationalSampling
variable {n : ℕ}
attribute [local irreducible] RawTake.run
noncomputable def entry (k : ℕ) (x : List Bool) : List Bool :=
  pairBits (k.bits,RawTake.run (pairBits (discardPrefix x,extractPrefix x)))
noncomputable def block (k : ℕ) (x : List Bool) : List Bool :=
  mapWith (entry k) (pairBits (x,BinaryEllipsoidInitial.indices x))
noncomputable def menus (x : List Bool) : List Bool :=
  block 0 (field 0 x)++block 1 (field 1 x++[true])++block 2 (field 2 x)
noncomputable def run (x : List Bool) : List Bool := encode [encode [(0:ℕ).bits,[],[]]]++
  mapWith delete (pairBits ([],extractPrefix x))++crossWith add (pairBits (extractPrefix x,menus (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryActions

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
open BinaryOpeningPayment (field )
noncomputable def num_computes : PolyComputes num := discardPrefix_computes.comp extractPrefix_computes
noncomputable def den_computes : PolyComputes den := discardPrefix_computes.comp discardPrefix_computes
noncomputable def capacity : PolynomialCounter (10*Polynomial.X+20) := PolynomialCounter.choose _
noncomputable def initial_computes : PolyComputes initial := discardPrefix_computes.pair (const_computes (encode ([0,1,1].map Nat.bits)))
noncomputable def runInput (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (capacity.word x,initial x))
noncomputable def runInput_computes : PolyComputes runInput := extractPrefix_computes.pair (capacity.computes.pair initial_computes)
noncomputable def stateRun (query : List Bool→List Bool) : List Bool→List Bool := BoundedIteration.run (step query) ∘ runInput
noncomputable def run (query : List Bool→List Bool) : List Bool→List Bool := finish ∘ stateRun query
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
open BinaryOpeningPayment (field )
noncomputable def run (query : List Bool→List Bool) : List Bool→List Bool := BinaryGrid.run query ∘ input
end MetricKMedianRecovery.BitMachine.BinaryBisection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def capacity : PolynomialCounter capacityPoly := PolynomialCounter.choose capacityPoly
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves BinaryArithmetic
noncomputable def countInter : List Bool → List Bool := lengthBits ∘ inter
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end


