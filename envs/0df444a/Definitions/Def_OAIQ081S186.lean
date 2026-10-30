-- Prove2me | Definitions.Def_OAIQ081S186
-- name    : OAIQ081S186
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:43:31.483117+00:00
-- url     : https://prove2.me/theorems/c0559a20-ca46-4ef4-8add-0653ba202eb9
-- title:
--   Definitions bundle OAIQ081S186 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 47 declarations of OpenAI's Lean: 38 definitions and 9 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.covered`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finishBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.sourceWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.vector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.packedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowsProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.stagedPackedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepareBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.bundle`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.exportCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.inputEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.arithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.core`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.inputBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontendBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postPrefixBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postUniformBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.sourceProduct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.preparationProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.seededOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.arithmeticCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.productCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.rowCode`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.termCode`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceProgram.bound`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HeadSourceLocality`, `SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend`, `SubexponentialSAT_SqrtLogSpace_HighQueryProgram`, `SubexponentialSAT_SqrtLogSpace_HighQuerySetup`, `SubexponentialSAT_SqrtLogSpace_NativeQueryArithmetic`, `SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBank`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameFinish`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankUniversal`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramConcrete`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceCall`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStaging`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramDefinitions`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExports`, `SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedSource`, `SubexponentialSAT_SqrtLog_LeafProgramQueryArithmetic`, `SubexponentialSAT_SqrtLog_LeafProgramSource`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendPost`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendPostBound`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendRun`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendUniform`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolationReplay`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`, `SubexponentialSAT_Subexp_UniversalRowExecution`, `SubexponentialSAT_Subexp_UniversalRowProgram`, `SubexponentialSAT_Subexp_UniversalRowSourceProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S180`, `OAIQ081S181`, `OAIQ081S182`, `OAIQ081S183` and `OAIQ081S185` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S189` and `OAIQ081S190`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_frontend_budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.covered_uncovered_cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal_generated`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.staged_native_row_relSourceSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.exportCost_poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.guarded_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.inputEnvelope_poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.front_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_input_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_with_inputLengths`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval_uniform`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowEmitCall.command_eval` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_frontend_budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.colored_source_admissible`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.actual_product_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.accepted_command_front_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_front_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_kept_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.covered_uncovered_cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal_generated`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.native_relSourceSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.staged_native_row_relSourceSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.exportCost_poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.guarded_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.inputEnvelope_poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.front_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_input_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_eval_with_inputLengths`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend_time_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval_uniform`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S180
import Definitions.Def_OAIQ081S181
import Definitions.Def_OAIQ081S182
import Definitions.Def_OAIQ081S183
import Definitions.Def_OAIQ081S185

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

def termCode (one x : Word) (t : Term Word) : Word :=
  pushWord t.value ++ pushWord t.inverseNode ++ pushWord x ++ operator true ++
    productCode one x t.factors ++ operator true ++ operator true

def rowCode (zero one x : Word) (r : Row Word) : Word :=
  pushWord r.delta ++ (r.terms.map (termCode one x)).flatten ++
    pushWord zero ++ operators false r.terms.length ++ operator false

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

def productCost (one x : Word) (fs : List (Factor Word)) : ℕ :=
  scanCost encodeFactor (factorCost x) fs + 8 * one.length + 4 * fs.length + 13

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed producer from packed scalar/cache tables to row postfix bytes. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceProgram

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)

def bound (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (delta limit zero one : Word) : ℕ :=
  UniversalRowDataProgram.cost t width rowWidth positions delta limit +
    2048 * UniversalRowProgram.inputSize zero one
      (UniversalRowDataProgram.row t positions delta limit) ^ 2 + 4

end SubexponentialSAT.Subexp.UniversalRowSourceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramDefinitions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed source-value table program. Its definitions and structural
interfaces are independent of the full integer numerator execution proof. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open IntegerRingLiftProgram

def callback : Code := .seq numerator (.seq modelScaledCommand
  (.seq (clear 253) (clear 254)))

def tableProgram := LayoutSourceValuesProgram.program callback

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def vector : Code := .call (ProgramLinking.liftProgram LayoutSourceValuesProgram.Native.tableProgram id vectorPorts)
def universal : Code := .seq stageTypes (.seq vector (.seq mismatches (.seq compareTypes
  (.seq delta (.seq stageEmitter emit)))))

def covered : Code := .ite 5 (.seq compareBlocks (.ite 7 universal zero)) zero

def command : Code := .seq lookup (.seq (.ite 4 covered uncovered) cleanup)
def program := compiled command 304 287

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def sourceWord (tables : UniversalRowLoop.Tables) (positions : List ℕ) (a : Data) : List Bool :=
  UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314) (a.stacks 313++a.stacks 314)
    (UniversalRowDataProgram.row tables positions (deltaWord a) (a.stacks 47))

def finishBound (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (a : Data) (B : ℕ) : ℕ :=
  18*(a.stacks 23).length+9*(a.stacks 24).length+35+
    (7*B+6+(7*emitterSize a+50+
      UniversalRowSourceProgram.bound tables width rowWidth positions
        (deltaWord a) (a.stacks 47) (a.stacks 313) (a.stacks 314)+120*B+180))

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def packedSource : Code := .call (ProgramLinking.liftProgram
  LayoutProgram.SourceBank.program id sourcePorts)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source numerator uses empty scalar work tapes5/10. The polynomial
executor retains its modulus/width there. Two reversible transfers isolate
these phases without touching the native high arithmetic cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def stagedPackedSource : Code := .seq stageScalarWork (.seq packedSource unstageScalarWork)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramConcrete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual finite source-row controller. This is a fixed composition of
native plan lookup, source dispatch, polynomial execution and row emission. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- The lookup's retained register4 reports actual pair membership. Missing
factor incidences produce a complete ambient zero-row table. Caller parks the
four target-cutoff caches before entry and restores them after exit; the full
source cutoff is always read from210. -/
def sourceRows : Code := sourceRowsWith stagedPackedSource

def sourceRowsProgram := compiled sourceRows 337 205

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankUniversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The universal branch has a concrete trace and a typed polynomial witness.
The only table used below is returned by the actual native vector program. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

def nativeBudget (p : Parameters r Q d) (S : ℕ) (a : Data)
    (codes : Fin Q → ModelCode p.t d) (u y : UniversalType r Q 1) : ℕ :=
  Staging.cost 0 1 stageTypesOps a+
  LayoutSourceValuesProgram.Native.tableBudget p.aWord.length p.R p.width.length
    (pairLength p.power) p.t d u y+
  (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
    UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
  finishBound (SourceTyped.tables RingProgram.flat codes p.inverse p.negative p.difference)
    p.ringWidth p.rowWidth (nativePositions u y)
    (branchState a (fun _=>false) (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten
      (nativeIndices u y))
    (S+Q*(d*SubexpLiftRing.baseWidth 3 p.t)+(nativeIndices u y).length)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source callback used by the actual incidence-table loop. The fixed
command stages source controls, protects all four target caches, invokes the
concrete source-row instruction table, restores the target caches, and clears
source-only controls. The local source correctness theorem is joined below
through its actual execution, never through a supplied polynomial oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev core : Cmd 16 768 := .call (ProgramLinking.liftProgram
  LayoutSourceRowsProgram.sourceRowsProgram id workerPort)
abbrev command : Cmd 16 768 := .seq SourceStaging.before
  (.seq SourceControls.prepare (.seq core
    (.seq SourceStaging.after SourceControls.cleanup)))

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSourceLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete source locality for the streamed head evaluation.
The source correspondence is `NodeConcrete.fixedSourceRow_baseline_eq` in
LeafProgramNodeConcretePlan, the actual residualJet in
LeafProgramNodeConcreteResidual, and residualProduct in
LeafProgramNodeConcreteResidualProduct. Fixed-high bits cancel in the full
integer signatures; every correction specialization uses one common U. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog



open OAI SubexpLiftRing SubexpQuarticRing
open MulticolorTypes Subexp.ConstructivePacking
open LeafProgram LeafProgram.NodeConcrete
open LayoutProgram PerturbationAssembly Polynomial

noncomputable section

variable {r Q d n : ℕ}


/-- The actual selected-factor product for one owned color group. IDs outside
the hash and optional marked range retain the original neutral-factor branch. -/
def sourceProduct (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (ids : List ℕ) :=
  Squarefree.canonical q.u q.J ((ids.map
    (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
      (RingBasis.basis (q.p.model.F q.p.t)) q.code
      (residualJet q.p q.ps q.packing H high q.theta state)
      (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def prepareBudget (m : Model) : ℕ := Cache.runtimeBound m+1+
  exportModelBudget (Interval.finalModel m)+clearModelBudget (Interval.finalModel m)

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid persistent metadata export, offset construction, mask conversion, and
scratch cleanup after the guarded numeric bank has been computed. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


noncomputable def postBudget (m : Circuit.Model) (prepared beforeClean : Data) (descending : List Bool) : ℕ :=
  Exports.prepareBudget m+
    LayoutOffsetProgram.budget (prepared.stacks 725) (prepared.stacks 720) (prepared.stacks 727)+
    (12*descending.length+8)+cleanupCost beforeClean

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram

noncomputable def frontendBudget (q : Query) (k : ℕ) (counted prepared beforeClean : Data)
    (tau : List Bool) (l : Fin 8 → ℕ) : ℕ :=
  SubexpScopeCountSetup.countBudget (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))+
    coreBudget q k counted tau l+
    postBudget (Execute.guardedModel (q.input k) l) prepared beforeClean
      (highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPostBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def postPrefixBudget (m : Circuit.Model) (n : ℕ) : ℕ :=
  Exports.prepareBudget m+offsetModelBudget m+12*n+8

def postUniformBudget (m : Circuit.Model) (n A : ℕ) : ℕ :=
  525*postPrefixBudget m n+524*A+789

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendUniform
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def Query.inputBudget (q : Query) (k : ℕ) : ℕ :=
  q.hashCountBudget+q.coreInputBudget k+
    postUniformBudget (Execute.guardedModel (q.input k) (q.inputLengths k))
      (BinaryArithmetic.toNat q.ambient) (q.coreInputBudget k)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original actual marked-scope/high-mask/parameter frontend is lifted
into the shared leaf ABI. Upper caller words and the marked mass collector
are retained; the lower workspace is reclaimed by an actual cleanup program. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

noncomputable def budget (q : LeafQueryFrontend.Query) (k : ℕ) : ℕ :=
  10*q.index.length+q.inputBudget k+12

noncomputable def acceptedBudget (q : LeafQueryFrontend.Query) (k : ℕ) := q.inputBudget k+5

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram SubexpQuarticRing SubexpLiftRing

/-- Complete actual preparation from the physically present finite numeric
bank. No modulus, polynomial, table, scalar cache, node list, idempotent
array, or arithmetic readiness predicate occurs among the premises. -/
theorem producerCommand_eval (a : Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters a=Bank.state r w)
    (initialWidth V bankWidth : ℕ)
    (hinit : ∀ i,(a.stacks i).length ≤ initialWidth)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ bankWidth)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34) :
    ∃ n ≤ producerBudget m initialWidth V bankWidth, ∃ e : Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)),
      Eval producerCommand n a e ∧ Produced m hd M cache u e ∧
      (∀ i,320 ≤ i.val → i.val < 340 → e.stacks i=a.stacks i) := by
  let b0 := numberBudget m initialWidth V bankWidth
  let b1 := coreBudget (m.val 33) (m.val 34) bankWidth
  let w1 := initialWidth+b0+b1+1
  let b2 := constantsBudget w1 (baseWidth 3 (m.val 33)) (m.val 34)
  let w2 := w1+b2+1
  let b3 := nodesBudget w2 (m.val 33) (m.val 34) (m.val 21)
  let w3 := w2+b3+1
  let b4 := idempotentBudget (m.val 33) w3
  let w4 := w3+b4+1
  obtain ⟨n0,hn0,a0,w',he0,hshape,hinput,h191,h209,h243,h296,hbank,hcollector⟩ :=
    numberPhase_eval a m w r hs ha initialWidth V bankWidth (fun i _ => hinit i) hv hw
  have hval (i : Fin 64) (hi44 : i≠44) (hi45 : i≠45) :
      BinaryArithmetic.toNat (w' i)=m.val i :=
    (hshape.1 i).trans (Serialization.frame m i hi44 hi45)
  let depth := List.replicate (m.val 34) true
  have hdp : 0 < depth.length := by simpa [depth] using hd
  have hcoreInput : CoreInput (w' 33) depth a0 := by
    simpa [depth,hval 34 (by decide) (by decide)] using hinput
  have htword : CounterPrograms.value (w' 33)=m.val 33 := by
    simpa only [CounterPrograms.value_eq_toNat] using hval 33 (by decide) (by decide)
  obtain ⟨n1,hn1,a1,M,cache,u,he1,hcore,hcoreframe⟩ :=
    coreCommand_eval a0 (w' 33) depth (m.val 33) ht hdp htword hcoreInput
  have hcore' : CoreOutput (m.val 33) (m.val 34) (IrreducibleSearch.data hd) M cache u a1 := by
    exact hcore.reindex (by simp [depth]) hdp hd
  have hn1' : n1 ≤ b1 := by
    simp only [depth,List.length_replicate] at hn1
    apply hn1.trans
    have hlen := (hshape.2 33).trans (hw 33)
    dsimp [b1]
    unfold coreBudget scalarBudget
    gcongr
  have hwidth1 : ∀ i,(a1.stacks i).length ≤ w1 := by
    intro i
    have hh := eval_width_le (he0.seq he1) hinit i
    dsimp [w1,b0]
    omega
  have hmeta1 (i : Fin 640) (hi : i∉coreWritePorts) : a1.stacks i=a0.stacks i := hcoreframe i hi
  obtain ⟨n2,hn2,a2,he2,hcache2,hcf⟩ := constantsPhase_produces a1 hcore' w1 hwidth1
  have hwidth2 : ∀ i,(a2.stacks i).length ≤ w2 := by
    intro i
    have hh := eval_width_le he2 hwidth1 i
    dsimp [w2,b2]
    omega
  have hmeta2 (i : Fin 640) (hi : i∉constantStartPorts)
      (hj : i∉([190,249,250,251] : List (Fin 640))) (hk : i∉coreWritePorts) :
      a2.stacks i=a0.stacks i := (hcf i ⟨hi,hj⟩).trans (hmeta1 i hk)
  have hq2 : BinaryArithmetic.toNat (a2.stacks 361)=m.val 21 := by
    rw [hmeta2 361 (by decide) (by decide) (by decide)]
    rw [show a0.stacks 361=w' 21 from hbank 21]
    exact hval 21 (by decide) (by decide)
  have hc2 : a2.stacks 296=List.replicate (m.val 21) true := by
    rw [hmeta2 296 (by decide) (by decide) (by decide),h296,hval 21 (by decide) (by decide)]
  have hz2 : a2.stacks 203=List.replicate (baseWidth 3 (m.val 33)) false :=
    hcache2.scalarZero.trans (IdempotentPreparationProgram.Scalar.canonical_zero_bytes _ _ hcache2.canonical)
  have hw2 : (a2.stacks 280).length=(m.val 34)*baseWidth 3 (m.val 33) := by
    rw [hcache2.fullZero,←LeafProgram.Constants.constantCode_flat,RingProgram.flat_length]
  obtain ⟨n3,hn3,a3,he3,hflat,hframed,hnf⟩ := nodesPhase_eval a2 (m.val 33) (m.val 34)
    (m.val 21) w2 ht hwidth2 hz2 hcache2.degree hq2 hc2 hw2
  have hcache3 := hcache2.frame (e:=a3) (by
    intro i hi
    apply hnf
    simp only [ringCachePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have hwidth3 : ∀ i,(a3.stacks i).length ≤ w3 := by
    intro i
    have hh := eval_width_le he3 hwidth2 i
    dsimp [w3,b3]
    omega
  have ht3 : CounterPrograms.value (a3.stacks 373)=m.val 33 := by
    rw [hnf 373 (by decide),hmeta2 373 (by decide) (by decide) (by decide)]
    rw [show a0.stacks 373=w' 33 from hbank 33]
    exact htword
  obtain ⟨n4,hn4,a4,MI,cacheI,uI,he4,hidem,hiinv,hif⟩ :=
    idempotentPhase_eval a3 (m.val 33) w3 ht ht3 hwidth3
  have hcache4 := hcache3.frame (e:=a4) (by
    intro i hi
    apply hif
    simp only [ringCachePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have hwidth4 : ∀ i,(a4.stacks i).length ≤ w4 := by
    intro i
    have hh := eval_width_le he4 hwidth3 i
    dsimp [w4,b4]
    omega
  obtain ⟨e,he5,hcache5,hnative,hclean,hff⟩ := finalCleanup_produces a4 hcache4
  have hn5 := clearPortsCost_bound finalDiscard a4 w4 (fun i _ => hwidth4 i)
  have hmeta (i : Fin 640) (hfin : i∉finalDiscard) (hid : i∉idempotentStartPorts)
      (hnd : i∉296::nodesStartPorts) (hcs : i∉constantStartPorts)
      (halias : i∉([190,249,250,251] : List (Fin 640))) (hco : i∉coreWritePorts) :
      e.stacks i=a0.stacks i :=
    (hff i hfin).trans ((hif i hid).trans ((hnf i hnd).trans (hmeta2 i hcs halias hco)))
  refine ⟨n0+n1+n2+n3+n4+(clearPortsCost finalDiscard a4+32),?_,e,M,cache,u,?_,?_,?_⟩
  · change _ ≤ b0+b1+b2+b3+b4+finalDiscard.length*(2*w4+3)+32
    omega
  · simpa only [producerCommand,Nat.add_assoc] using
      he0.seq (he1.seq (he2.seq (he3.seq (he4.seq he5))))
  · refine ⟨hcache5,hnative,?_,?_,?_,?_,?_,?_,hclean⟩
    · rw [hmeta 191 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h191,
        hval 0 (by decide) (by decide)]
    · rw [hmeta 209 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h209,hshape.1 44]
    · rw [hmeta 243 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h243,
        hval 42 (by decide) (by decide)]
    · rw [hff 256 (by decide),hif 256 (by decide),hflat]
    · rw [hff 300 (by decide),hif 300 (by decide),hframed]
    · exact ⟨MI,cacheI,uI,(hff 281 (by decide)).trans hidem,hiinv⟩
  · intro i hlo hhi
    obtain ⟨hf,hi,hn,hc,ha,hk⟩ := collector_not_touched i hlo hhi
    exact (hmeta i hf hi hn hc ha hk).trans (hcollector i hlo hhi)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram

/-- The fixed finite instruction table realizes the full producer contract. -/
theorem producerProgram_runs (a : Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters a=Bank.state r w)
    (initialWidth V bankWidth : ℕ)
    (hinit : ∀ i,(a.stacks i).length ≤ initialWidth)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ bankWidth)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34) :
    ∃ e : Data, ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
      (cache : RingProgram.ScalarCache 3 (m.val 33))
      (u : RingProgram.ScalarCode 3 (m.val 33)),
      RunsIn producerProgram (producerBudget m initialWidth V bankWidth+1)
        (a.withPC (some producerProgram.entry)) (e.withPC none) ∧
      Produced m hd M cache u e ∧
      (∀ i,320 ≤ i.val → i.val < 340 → e.stacks i=a.stacks i) := by
  obtain ⟨n,hn,e,M,cache,u,he,hp,hf⟩ :=
    producerCommand_eval a m w r hs ha initialWidth V bankWidth hinit hv hw ht hd
  exact ⟨e,M,cache,u,⟨n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he (parameters 0) 300⟩,hp,hf⟩

/-- The outer leaf uses the same actual producer in its larger fixed
ambient. Parser/branch registers and the collector's tapes are retained. -/
theorem producerProgram_lifted (base : StructuredProgram.State 40 768)
    (a : Data) (hbase : projectState wideRegisters wideStacks base=a)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters a=Bank.state r w)
    (initialWidth V bankWidth : ℕ)
    (hinit : ∀ i,(a.stacks i).length ≤ initialWidth)
    (hv : ∀ i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀ i,(Circuit.result Serialization.code m).len i ≤ bankWidth)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34) :
    ∃ n ≤ producerBudget m initialWidth V bankWidth+1, ∃ e : Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)),
      Eval producerWideCall n base (embedState wideRegisters wideStacks base e) ∧
      Produced m hd M cache u e ∧
      (∀ i : Fin 40,16 ≤ i.val → i.val < 24 →
        (embedState wideRegisters wideStacks base e).regs i=base.regs i) ∧
      (∀ i : Fin 768,640 ≤ i.val →
        (embedState wideRegisters wideStacks base e).stacks i=base.stacks i) ∧
      (∀ i : Fin 640,320 ≤ i.val → i.val < 340 →
        (embedState wideRegisters wideStacks base e).stacks (wideStacks i)=base.stacks (wideStacks i)) := by
  obtain ⟨e,M,cache,u,⟨n,hn,hr⟩,hp,hf⟩ :=
    producerProgram_runs a m w r hs ha initialWidth V bankWidth hinit hv hw ht hd
  refine ⟨n,hn,e,M,cache,u,?_,hp,?_,?_,?_⟩
  · exact eval_call_from_state producerProgram wideRegisters wideStacks base
      wideRegisters_injective wideStacks_injective (hbase.symm ▸ hr)
  · intro i hlo hhi
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    dsimp [wideRegisters] at hh
    split_ifs at hh <;> simp only [] at hh <;> omega
  · intro i hlo
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    dsimp [wideStacks] at hh
    have := j.isLt
    omega
  · intro i hlo hhi
    rw [embedState_stack _ _ _ _ wideStacks_injective i,hf i hlo hhi]
    exact congrArg (fun z : Data => z.stacks i) hbase.symm

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Paid staging of the native interpolation-cache producer in the wide
leaf machine. The private 320-tape bank is disjoint from all ring and
collector masters. Native table computation is followed by paid extraction
of all five outputs; the entire staging bank is then cleared. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation
open BitProgram StructuredCalls StackRoutines SubexpLiftRing SubexpQuarticRing

/-- The central call is exactly the verified finite cache producer, with no
replacement of its inverse or difference tables by semantic values. -/
theorem coreCall_eval (base : Data) (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (minusOne : InterpolationCacheProgram.Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : InterpolationCacheProgram.Store)
    (xs : List (InterpolationCacheProgram.Coeff t d))
    (hr : InterpolationCacheProgram.Ready t a M cache minusOne s)
    (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈InterpolationCacheProgram.inputEmpty,s i=[])
    (hs : ∀i,base.stacks (localPorts i)=s i) :
    ∃n ≤ InterpolationCacheProgram.budget t d xs.length+1,∃rf,
      Eval coreCall n base (embedState localRegisters localPorts base
        (⟨rf,InterpolationCacheProgram.finalStore t a M cache minusOne xs s⟩ :
          InterpolationCacheProgram.Data)) := by
  obtain ⟨n,rf,hn,he⟩ := InterpolationCacheProgram.program_run t a M cache hz minusOne hW
    s xs hr hm hc (base.regs ∘ localRegisters)
  have hp : projectState localRegisters localPorts base=
      (⟨base.regs ∘ localRegisters,s⟩ : InterpolationCacheProgram.Data) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; exact hs i
  exact ⟨n,hn,rf,eval_call_from_state InterpolationCacheProgram.program
    localRegisters localPorts base localRegisters_injective localPorts_injective (hp.symm ▸ he)⟩

/-- All five cache outputs, including unary lengths, are generated and
extracted by the fixed program. Old scratch need not initially be empty. -/
theorem command_eval (base : Data) (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (minusOne : InterpolationCacheProgram.Coeff t d) (hW : 0 < d*baseWidth 3 t)
    (xs : List (InterpolationCacheProgram.Coeff t d))
    (hi : Inputs t model M cache minusOne base)
    (hm : base.stacks 256=xs.flatMap RingProgram.flat)
    (W : ℕ) (hw : ∀i,(base.stacks i).length ≤ W) :
    ∃n ≤ 10000*(W+InterpolationCacheProgram.budget t d xs.length+2),∃e : Data,
      Eval command n base e ∧
      e.stacks 713=InterpolationCacheProgram.inverseBytes t model M cache minusOne xs ∧
      e.stacks 714=InterpolationCacheProgram.negativeBytes t model M cache minusOne xs ∧
      e.stacks 715=InterpolationCacheProgram.differenceBytes t model M cache minusOne xs ∧
      e.stacks 716=List.replicate (xs.length*(d*baseWidth 3 t)) true ∧
      e.stacks 717=List.replicate (d*baseWidth 3 t) true ∧
      (∀i∈privatePorts,e.stacks i=[]) ∧
      (∀i,i∉privatePorts → i≠699 → i∉([713,714,715,716,717] : List (Fin 768)) →
        e.stacks i=base.stacks i) ∧
      (∀i : Fin 40,16 ≤ i.val → i.val < 38 → e.regs i=base.regs i) := by
  let a0 := clearedPorts (699::privatePorts) base
  let a1 := staged base
  have he0 := clearPorts_eval (699::privatePorts) base
  have he1 := copyPlan_eval inputPlan a0 inputPlan_ports
    (by simp [a0,clearedPorts_stacks])
  have hw0 := cleared_width (699::privatePorts) base W hw
  have hw1 := copied_width inputPlan a0 W hw0
  have hs1 : a1.stacks 699=[] := by
    simp [a1,staged,inputPlan,copiedPlan,copied,clearedPorts_stacks]
  have hm1 : stagedStore base 256=xs.flatMap RingProgram.flat := by
    simpa [stagedStore_eq,inputIndex] using hm
  obtain ⟨nc,hnc,rf,hec⟩ := coreCall_eval a1 t model M cache hz minusOne hW
    (stagedStore base) xs (staged_ready base t model M cache minusOne hi) hm1
    (staged_inputEmpty base) (fun _=>rfl)
  let raw : InterpolationCacheProgram.Data :=
    ⟨rf,InterpolationCacheProgram.finalStore t model M cache minusOne xs (stagedStore base)⟩
  let a2 := embedState localRegisters localPorts a1 raw
  have hs2 : a2.stacks 699=[] := by
    rw [show a2.stacks 699=a1.stacks 699 from
      embedState_stack_frame _ _ _ _ _ (by
        rintro ⟨i,h⟩; have := congrArg Fin.val h; dsimp [localPorts] at this; omega)]
    exact hs1
  have hp := copyPlan_eval outputPlan a2 outputPlan_ports hs2
  let a3 := copiedPlan outputPlan a2
  let e := clearedPorts privatePorts a3
  have he3 := clearPorts_eval privatePorts a3
  have hwidth := eval_width hec hw1
  have hw2 : ∀i,(a2.stacks i).length ≤ W+InterpolationCacheProgram.budget t d xs.length+2 := by
    intro i
    have hh := hwidth i
    change (a2.stacks i).length ≤ W+nc+1 at hh
    omega
  have hw3 := copied_width outputPlan a2 _ hw2
  have hb0 := clearPortsCost_bound (699::privatePorts) base W (fun i _=>hw i)
  have hb1 := copyPlanCost_bound inputPlan a0 W hw0
  have hbo := copyPlanCost_bound outputPlan a2 _ hw2
  have hb3 := clearPortsCost_bound privatePorts a3 _ (fun i _=>hw3 i)
  have hout (i : Fin 320) : a2.stacks (localPorts i)=raw.stacks i :=
    embedState_stack _ _ _ _ localPorts_injective i
  have h599 : a2.stacks 599=InterpolationCacheProgram.inverseBytes t model M cache minusOne xs := hout 259
  have h600 : a2.stacks 600=InterpolationCacheProgram.negativeBytes t model M cache minusOne xs := hout 260
  have h601 : a2.stacks 601=InterpolationCacheProgram.differenceBytes t model M cache minusOne xs := hout 261
  have h602 : a2.stacks 602=List.replicate (xs.length*(d*baseWidth 3 t)) true := hout 262
  have h603 : a2.stacks 603=List.replicate (d*baseWidth 3 t) true := hout 263
  refine ⟨clearPortsCost (699::privatePorts) base+copyPlanCost inputPlan a0+
    nc+copyPlanCost outputPlan a2+clearPortsCost privatePorts a3,?_,e,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hprivate : privatePorts.length = 320 := by simp [privatePorts]
    simp only [List.length_cons,hprivate] at hb0 hb3
    norm_num [inputPlan] at hb1
    norm_num [outputPlan] at hbo
    unfold inputPlan outputPlan
    omega
  · simpa only [command,Nat.add_assoc,staged,a0,a1,a3,e] using
      he0.seq (he1.seq (hec.seq (hp.seq he3)))
  · simp [e,clearedPorts_stacks,privatePorts_not_high 713 (by decide),
      a3,copiedPlan,copied,outputPlan,h599]
  · simp [e,clearedPorts_stacks,privatePorts_not_high 714 (by decide),
      a3,copiedPlan,copied,outputPlan,h600]
  · simp [e,clearedPorts_stacks,privatePorts_not_high 715 (by decide),
      a3,copiedPlan,copied,outputPlan,h601]
  · simp [e,clearedPorts_stacks,privatePorts_not_high 716 (by decide),
      a3,copiedPlan,copied,outputPlan,h602]
  · simp [e,clearedPorts_stacks,privatePorts_not_high 717 (by decide),
      a3,copiedPlan,copied,outputPlan,h603]
  · intro i hi'; simp [e,clearedPorts_stacks,hi']
  · intro i hpriv h699 ho
    have hlocal : ¬∃j,localPorts j=i := by
      rintro ⟨j,rfl⟩; exact hpriv (by simp [privatePorts])
    have hdout : ∀p∈outputPlan,p.2≠i := by
      intro p hp'
      simp only [outputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp'
      rcases hp' with rfl|rfl|rfl|rfl|rfl <;> intro hh <;> subst i <;> simp at ho
    have hdin : ∀p∈inputPlan,p.2≠i := by
      intro p hp' hh
      have hpv : p.2∈privatePorts := by
        simp only [inputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp'
        rcases hp' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      exact hpriv (hh ▸ hpv)
    rw [show e.stacks i=a3.stacks i by simp [e,clearedPorts_stacks,hpriv]]
    rw [show a3.stacks i=a2.stacks i from copiedPlan_frame outputPlan a2 i (fun p hp => Ne.symm (hdout p hp))]
    rw [show a2.stacks i=a1.stacks i from embedState_stack_frame _ _ _ _ _ hlocal]
    rw [show a1.stacks i=a0.stacks i from copiedPlan_frame inputPlan a0 i (fun p hp => Ne.symm (hdin p hp))]
    simp [a0,clearedPorts_stacks,hpriv,h699]
  · intro i hlo hhi
    have h38 : i≠38 := by intro he; subst i; omega
    have h39 : i≠39 := by intro he; subst i; omega
    rw [show e.regs i=a3.regs i from cleared_register_frame privatePorts a3 i h38 h39]
    rw [show a3.regs i=a2.regs i from copied_register_frame outputPlan a2 i h38 h39]
    rw [show a2.regs i=a1.regs i from embedState_register_frame _ _ _ _ _ (by
      rintro ⟨j,hj⟩; have := congrArg Fin.val hj; dsimp [localRegisters] at this; omega)]
    rw [show a1.regs i=a0.regs i from copied_register_frame inputPlan a0 i h38 h39]
    exact cleared_register_frame (699::privatePorts) base i h38 h39

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual arithmetic preparation per query: ring caches, interpolation
caches, then the inverse layout denominator. All three run before branching. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

 def arithmetic : Code := .seq Ring.command LayoutDenominatorProgramQuery.command

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual query arithmetic with fixed ordinary polynomial time and space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- The arithmetic suffix is the original ring, interpolation and denominator
program, with no residual evaluator or node-loop argument. -/
def arithmeticCommand : Cmd 40 768 := arithmetic

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-only closure of the physical parameter/cache/export costs, including
the exact binary word lengths used by the subsequent offset producer. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BinaryArithmetic Bank Circuit Asymptotic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def inputEnvelope (a : Args) := inputMeasure a+nativeCost a+loopCap a.1+5

def exportCost (a : Args) := Exports.prepareBudget (guarded a)

/-- The offset producer receives actual exported binary B/Q/R words. Include
all three physical length caps and the numeric exponent R in one bound. -/
def bundle (a : Args) := nativeCost a+exportCost a+
  (guarded a).len 3+(guarded a).len 21+(guarded a).len 29+(guarded a).val 29+1+offsetCost a

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolationReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay footprint of the existing interpolation producer. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem command_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Interpolation.command := by
  have hc : AvoidsCmd LeafProgram.OuterCarried.hidden coreCall := by
    apply avoids_call_lift_of_range
    intro i
    apply visible
    right
    change 340 ≤ 340+i.val
    omega
  have hi : AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.copyPlan inputPlan) := copyPlan _ (by
    intro p hp
    simp only [inputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have ho : AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.copyPlan outputPlan) := copyPlan _ (by
    intro p hp
    simp only [outputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide)
  exact ⟨clearPorts _ (by
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · decide
    · exact private_visible i hi),hi,hc,ho,clearPorts _ private_visible⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem producerCommand_avoids : AvoidsCmd hidden producerCommand := by
  have hc : ∀i∈finalDiscard,¬hidden i := by
    intro i hi hh
    have h := hidden_bounds hh
    exact (collector_not_touched i h.1 h.2).1 hi
  exact ⟨number,core,constants,nodes,idempotents,clearPorts _ hc,resetAll⟩

theorem producerWideCall_avoids :
    AvoidsCmd LeafProgram.OuterCarried.hidden producerWideCall :=
  avoids_liftProgram _ _ _ _ (avoids_compiled hidden producerCommand
    producerCommand_avoids (parameters 0) 300)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- Actual packing followed by actual ring/interpolation/denominator setup. -/
def command : Cmd 40 768 := .seq PackingCallerProgram.command arithmeticCommand

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

/-- Packing, searched ring production, interpolation and the denominator are
executed once per marked or accepted query, before high-assignment iteration. -/
def preparationProgram := compiled NativeQueryPreparation.command 700 728

def prepare : Code := .call (ProgramLinking.liftProgram preparationProgram
  id HighMarkedFrontend.stackMap)

open HashGreedyProgram.NativeRound

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

noncomputable def seededOutput (front : Data) (output : Lower)
    (seedRegs : Fin 2 → Bool) : Data :=
  HighCountSeed.initialized (preparedOutput front output) seedRegs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source parameter object is derived from the executed query's numeric
bank, ring setup, and native head cache. Source order and jet order remain distinct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

theorem numeric_field (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (produce (q.input k)).Q < 3^((numeric q k l).val 34) := by
  rw [numeric_d q k l hg]
  exact extensionDegree_sufficient _

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end


