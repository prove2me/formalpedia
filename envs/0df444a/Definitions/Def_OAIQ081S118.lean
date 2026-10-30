-- Prove2me | Definitions.Def_OAIQ081S118
-- name    : OAIQ081S118
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:31:02.389359+00:00
-- url     : https://prove2.me/theorems/e98a4126-5246-48ca-843b-a7775f5c15f9
-- title:
--   Definitions bundle OAIQ081S118 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 80 declarations of OpenAI's Lean: 69 definitions, 5 inductive types or structures and 6 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.executionInitialization`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.executionPreparation`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.CheckInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.LocalInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.LocalReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.VertexInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.belowClauseCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.coefficientOffset`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.emitted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.finishCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.finishPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.finishedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.increment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.incremented`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.indexArithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.indexWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.initialStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.initializeCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.liftArithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.offsetWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.outputState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.paddedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portAccum`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionInit`, `SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionPrepare`, `SubexponentialSAT_SqrtLog_CodeRowsProgram`, `SubexponentialSAT_SqrtLog_CodeRowsProgramAppend`, `SubexponentialSAT_SqrtLog_CodeRowsProgramArithmetic`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCheckLoop`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCode`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCounter`, `SubexponentialSAT_SqrtLog_CodeRowsProgramFinish`, `SubexponentialSAT_SqrtLog_CodeRowsProgramInitialize`, `SubexponentialSAT_SqrtLog_CodeRowsProgramInvariant`, `SubexponentialSAT_SqrtLog_CodeRowsProgramLocal`, `SubexponentialSAT_SqrtLog_CodeRowsProgramOffset`, `SubexponentialSAT_SqrtLog_CodeRowsProgramPaddingCall`, `SubexponentialSAT_SqrtLog_CodeRowsProgramPort`, `SubexponentialSAT_SqrtLog_CodeRowsProgramPrepare`, `SubexponentialSAT_SqrtLog_CodeRowsProgramRow`, `SubexponentialSAT_SqrtLog_CodeRowsProgramSide`, `SubexponentialSAT_SqrtLog_CodeRowsProgramStorage`, `SubexponentialSAT_SqrtLog_CodeRowsProgramVertexLoop`, `SubexponentialSAT_SqrtLog_CodeRowsProgramVertexStep`, `SubexponentialSAT_SqrtLog_CostAssemblyRingBounds`, `SubexponentialSAT_SqrtLog_CostAssemblyRingSetup`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramPair`, `SubexponentialSAT_SqrtLog_HashCircuitProgramCost`, `SubexponentialSAT_SqrtLog_HornerProgramModel`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_RingProgramTableModel`, `SubexponentialSAT_SqrtLog_RingTripleBounds`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101` and `OAIQ081S102` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S139`, `OAIQ081S140`, `OAIQ081S141`, `OAIQ081S142`, `OAIQ081S143`, `OAIQ081S144`, `OAIQ081S145`, `OAIQ081S146`, `OAIQ081S150`, `OAIQ081S151` and `OAIQ081S152`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.initializeLocal_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.belowClauseCount_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.checkLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.initialize_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.padding_call_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexIteration_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexStep_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.writeRow_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add_spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.initializeLocal_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.belowClauseCount_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.initialize_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.padding_call_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexIteration_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexStep_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.writeRow_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add_spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev Code := Cmd 40 896

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact initialization and scan-state bridges for the native local CRT
controller. Only finite stack programs occur in these statements. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

/-- The initialization code, kept shallow so its trace can be checked
independently of the later arithmetic stages. Definitionally equal to
`initializeLocal` in the final controller. -/
def executionInitialization : Code :=
  .seq (SubexpPolynomialConstructor.construct 207 104 240)
    (.seq (copy 214 215) (.seq (copy 216 217) (SubexpLocalCRTSetup.token 229)))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

/-- Definitionally identical to the final controller's preparation code. -/
def executionPreparation (sm sa : Code) : Code :=
  .seq (SubexpLocalCRTSetup.clearMany [217,229])
    (.seq (replace 240 223) (.seq (clear 240) (.seq constantCommand
      (.seq (inverseConstantsCommand sm sa)
        (.seq (SubexpPolynomialConstructor.construct 207 104 220) (copy 192 242))))))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite table for sparse code rows. Runtime loops visit vertices,
local checks, and local ports only. The original clause count is used for a
binary comparison, never as the bound of a per-row scan. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev copy (src dst : Fin 64) : Cmd 16 64 :=
  .call (StackRoutines.copyProgram src dst 24 0 1)
abbrev clear (src : Fin 64) : Cmd 16 64 := .call (StackRoutines.clearProgram src 0 1)
abbrev push (dst : Fin 64) (b : Bool) : Cmd 16 64 := Subexp.TupleProgram.pushConst dst 0 b

abbrev liftArithmetic (c : Cmd 8 64) : Cmd 16 64 := liftCommand c 0 0 low8 id

abbrev indexArithmetic : Cmd 8 64 :=
  .seq (ArithmeticCalls.multiplyAt (arithmeticPorts 0))
    (ArithmeticCalls.addAt (arithmeticPorts 1))

abbrev readCoefficient : Cmd 16 64 :=
  .call (ProgramLinking.liftProgram Cell.program cellRegisters cellStacks)

abbrev shiftVertex : Cmd 16 64 :=
  .seq (copy 2 17) (.seq (.base (.atom (.copy 7 12)))
    (.call (ProgramLinking.liftProgram Shift.program low8 shiftStacks)))

abbrev belowClauseCount : Cmd 16 64 :=
  .call (ProgramLinking.liftProgram Compare.program low8 compareStacks)

/-- Coefficients are 0, 1, or 2, with one-hot bits saved on registers8/9. -/
abbrev coefficientOffset : Cmd 16 64 :=
  .ite 9 (.seq (copy 4 22) (push 22 false))
    (.ite 8 (copy 4 22) (.base .skip))

abbrev appendSlot : Cmd 16 64 :=
  .seq coefficientOffset
    (.seq (liftArithmetic (ArithmeticCalls.addAt (arithmeticPorts 2)))
      (.seq (copy 5 25)
        (.seq (.call (ProgramLinking.liftProgram ModularPrograms.paddingProgram low8 paddingStacks))
          (.seq (clear 23) (clear 22)))))

abbrev increment (src : Fin 64) : Cmd 16 64 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) low3 (incrementStacks src))

abbrev preparePort : Cmd 16 64 :=
  .seq readCoefficient (.seq shiftVertex
    (.seq (liftArithmetic indexArithmetic) belowClauseCount))

abbrev finishPort : Cmd 16 64 :=
  .seq (.ite 7 appendSlot (.base .skip))
    (.seq (clear 18) (.seq (clear 20) (.seq (clear 21) (increment 14))))

abbrev portStep : Cmd 16 64 := .seq preparePort finishPort

def portLoop : UnaryForPrograms.Ports 16 64 := ⟨15,10,11⟩
def rowLoop : UnaryForPrograms.Ports 16 64 := ⟨16,10,11⟩
def vertexLoop : UnaryForPrograms.Ports 16 64 := ⟨8,14,15⟩

abbrev writeRow : Cmd 16 64 :=
  .seq (.call (ProgramLinking.liftProgram RowSelectionProgramSelect.frameProgram low3 frameStacks))
    (push 12 true)

abbrev rowStep : Cmd 16 64 :=
  .seq (copy 6 15) (.seq (copy 9 1)
    (.seq (UnaryForPrograms.forCmd portLoop portStep) (.seq (clear 14) writeRow)))

abbrev sideStep (side : Bool) : Cmd 16 64 :=
  .seq (.base (.atom (.set 12 side)))
    (.seq (copy 10 0) (.seq (copy 7 16) (UnaryForPrograms.forCmd rowLoop rowStep)))

abbrev vertexStep : Cmd 16 64 :=
  .seq (sideStep false) (.seq (sideStep true) (increment 2))

abbrev initializeCommand : Cmd 16 64 :=
  .seq (push 12 false) (.seq (copy 11 25)
    (.call (ProgramLinking.liftProgram ModularPrograms.paddingProgram low8 zeroVertexStacks)))

abbrev command : Cmd 16 64 :=
  .seq initializeCommand (.seq (UnaryForPrograms.forCmd vertexLoop vertexStep) (clear 2))

def program := compiled command 10 12

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls SubexponentialSAT.BinaryArithmetic

def indexWidth (d : State 8 64) : ℕ :=
  (d.stacks 18).length+(d.stacks 3).length+(d.stacks 14).length+2

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def copied (src dst : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,copyStacks src dst d.stacks⟩

def cleared (src : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,Function.update d.stacks src []⟩

def pushed (dst : Fin 64) (b : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 b,Function.update d.stacks dst (b::d.stacks dst)⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularArithmetic

def initialStacks (d : Data) : Fin 64 → List Bool :=
  Function.update (Function.update d.stacks 12 [false]) 2 (List.replicate (d.stacks 11).length false)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramOffset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def offsetWord (d : Data) : List Bool :=
  if d.regs 9 then false::d.stacks 4 else if d.regs 8 then d.stacks 4 else []

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPaddingCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularPrograms

def paddedStacks (d : Data) : Fin 64 → List Bool :=
  Function.update
    (Function.update (Function.update d.stacks 25 []) 23
      ((d.stacks 23).drop (d.stacks 25).length)) 13
    ((SubexpLiftRing.fixedBits (d.stacks 25).length (BinaryArithmetic.toNat (d.stacks 23))).reverse++d.stacks 13)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramAppend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def appendCost (d : Data) : ℕ :=
  100*((d.stacks 21).length+(d.stacks 4).length+2)^2 +
    9*(d.stacks 4).length+11*(d.stacks 5).length+
    2*((d.stacks 21).length+(d.stacks 4).length+2)+30

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCounter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

noncomputable def incremented (d : Data) (src : Fin 64) (hs : src≠41) : Data :=
  CounterForPrograms.install (counterPorts src hs) d false false (d.regs 2)
    (CounterPrograms.ripple true (d.stacks src)) []

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def emitted (d : Data) : List Bool :=
  if d.regs 7 then
    (SubexpLiftRing.fixedBits (d.stacks 5).length
      (BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d))).reverse++d.stacks 13
  else d.stacks 13

def finishedStacks (d : Data) : Fin 64 → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update
      (Function.update d.stacks 13 (emitted d)) 18 []) 20 []) 21 []) 14
    (CounterPrograms.ripple true (d.stacks 14))

def finishCost (d : Data) : ℕ := appendCost d+
  2*((d.stacks 18).length+(d.stacks 20).length+(d.stacks 21).length)+
  8*(d.stacks 14).length+20

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def portWidth (d : Data) : ℕ :=
  (d.stacks 2).length+(d.stacks 3).length+(d.stacks 4).length+
    (d.stacks 5).length+(d.stacks 14).length+3

def preparedStacks (d : Data) (qt st shifted product idx : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update
    (Function.update (Function.update (Function.update d.stacks 0 qt) 1 st) 18 shifted)
      20 product) 21 idx

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPort
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def portIndex (d : Data) (pairs : List (Bool × Bool)) : ℕ :=
  BinaryArithmetic.toNat (Shift.result (d.regs 12) pairs)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14)

def portAccum (d : Data) (a b : Bool) (pairs : List (Bool × Bool)) : List Bool :=
  if portIndex d pairs < BinaryArithmetic.toNat (d.stacks 4) then
    (SubexpLiftRing.fixedBits (d.stacks 5).length
      (portIndex d pairs+coefficientValue a b (BinaryArithmetic.toNat (d.stacks 4)))).reverse++d.stacks 13
  else d.stacks 13

def portStacks (d : Data) (qt st acc : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update (Function.update (Function.update d.stacks 0 qt) 1 st)
    13 acc) 14 (CounterPrograms.ripple true (d.stacks 14))

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramInvariant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

structure LocalInvariant {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool) (i : ℕ) (d : Data) : Prop where
  position : i ≤ D
  registers : ∀ j : Fin 16, 12 ≤ j.val → d.regs j=base.regs j
  source : d.stacks 0=CodeSearchProgram.scalarFrames ((List.ofFn (Q a)).drop i)++qt
  shiftSource : d.stacks 1=shiftRows ((List.ofFn shifts).drop i)++st
  accum : d.stacks 13=(rowPayload b m (prefixSlots m shifts Q side v a i)).reverse++base.stacks 13
  index : BinaryArithmetic.toNat (d.stacks 14)=i
  indexLength : (d.stacks 14).length ≤ i
  other : ∀ j : Fin 64, j≠0 → j≠1 → j≠13 → j≠14 → j≠15 → d.stacks j=base.stacks j

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramLocal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

structure LocalReady {r : ℕ} (base : Data) (D m b : ℕ) (side : Bool)
    (v : Cayley.Cube r) : Prop where
  mode : base.regs 12=side
  vertex : base.stacks 2=vertexBits v
  degree : BinaryArithmetic.toNat (base.stacks 3)=D
  modulus : BinaryArithmetic.toNat (base.stacks 4)=m
  width : (base.stacks 5).length=b
  capacity : 3*m ≤ 2^b
  work : ∀ j : Fin 64, 17 ≤ j.val → j.val ≤ 41 → base.stacks j=[]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.StackRoutines

def rowCost (d : Data) (D b : ℕ) : ℕ :=
  7*(d.stacks 6).length+7*(d.stacks 9).length+
    D*(2000*(portWidth d+D+1)^2+2)+2*D+4*(D*b)+23

def rowStacks (d : Data) (qt payload : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update d.stacks 0 qt) 12
    (true::(Encoding.frame payload++d.stacks 12))

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCheckLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

structure CheckInvariant {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (b i : ℕ) (d : Data) : Prop where
  registers : ∀ j : Fin 16, 12 ≤ j.val → d.regs j=base.regs j
  source : d.stacks 0=matrixSuffix Q i
  output : d.stacks 12=collectedRows b ((checkRows m shifts Q side v).take i) (base.stacks 12)
  other : ∀ j : Fin 64, j≠0 → j≠12 → j≠16 → d.stacks j=base.stacks j

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def sideCost (d : Data) (D t b : ℕ) : ℕ :=
  7*(d.stacks 10).length+7*(d.stacks 7).length+t*(rowCost d D b+2)+13

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertexStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def vertexCost (d : Data) (D t b : ℕ) : ℕ := 2*sideCost d D t b+8*(d.stacks 2).length+8

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertexLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

structure VertexInvariant {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (b i : ℕ) (d : Data) : Prop where
  position : i ≤ 2^r
  value : BinaryArithmetic.toNat (d.stacks 2)=i
  width : i < 2^r → (d.stacks 2).length=r
  length : (d.stacks 2).length ≤ r+1
  output : d.stacks 12=collectedRows b (vertexPrefix m shifts Q i) (base.stacks 12)
  other : ∀ j : Fin 64, j≠2 → j≠8 → j≠12 → d.stacks j=base.stacks j

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native serializer endpoint. Runtime bounds are carried in unary tapes;
source arrays and arithmetic operands are copied by the actual table. -/

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def inputState {r D t : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3) : Data :=
  ⟨regs,fun j => if j=3 then dword else if j=4 then mword else if j=5 then width else
    if j=6 then List.replicate D true else if j=7 then List.replicate t true else
    if j=8 then List.replicate (2^r) true else if j=9 then CodeSearchProgram.matrixFrames shifts else
    if j=10 then CodeSearchProgram.matrixFrames Q else if j=11 then List.replicate r true else []⟩

def outputState {r D t m : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3) : Data :=
  ⟨regs,Function.update (Function.update (inputState regs dword mword width shifts Q).stacks 8 [])
    12 (rowStream width.length m shifts Q)⟩

def cost {r D t : ℕ} (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3) : ℕ :=
  let d := inputState (fun _ => false) dword mword width shifts Q
  2^r*(vertexCost ⟨d.regs,initialStacks d⟩ D t width.length+2)+13*r+18

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram
open SubexponentialSAT.SubexpQuarticRing

theorem tableEncoding_length {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B) :
    (tableEncoding table).length = d^3 * B := by
  have hlen (i j k : Fin d) : (table i j k).val.length = B := (table i j k).property
  simp [tableEncoding, List.length_flatten, List.map_ofFn,
 Function.comp_def, hlen]
  ring

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native Horner evaluation in the actual arbitrary-degree unramified
RingModel. The instruction table is independent of precision, extension
degree and polynomial length. Ring caches are explicit runtime inputs. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) :=
  (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def modelCoefficients (t : ℕ) {d : ℕ} (a : RingModel.Data d) :
    List.Vector (Word (baseWidth 3 t)) d :=
  List.Vector.ofFn (RingProgram.liftCoefficientsRun t a.coefficients).1

@[simp] theorem modelCoefficients_get (t : ℕ) {d : ℕ} (a : RingModel.Data d) :
    (modelCoefficients t a).get = (RingProgram.liftCoefficientsRun t a.coefficients).1 := by
  funext i
  exact List.Vector.get_ofFn _ _

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
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
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing StackRoutines

def coreBudget (t d bitWidth : ℕ) : ℕ :=
  scalarBudget t bitWidth+1 + (7*baseWidth 3 t+8) +32 +
  (3*IrreducibleSearchBootstrap.totalCost d+7*baseWidth 3 t+d*(28*t+14)+15) +
  (7*baseWidth 3 t+8) +208000*(d+1)^5*(t+1)^2

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing StackRoutines

def nodesBudget (W t d Q : ℕ) : ℕ :=
  nodesStartPorts.length*(2*W+3)+2*(9*W+8)+
    (RingNodeProgram.budget (baseWidth 3 t) W d Q+5)+
    2*(7*(Q*(d*baseWidth 3 t))+8)+(Q*(28*(d*baseWidth 3 t)+33)+11)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyRingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed polynomial bound for the actual ring producer's numerical cost.
The size cap includes the unary numeric bank bound V, so large stored values
are not silently replaced by their binary lengths. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

open LeafRingSetupProgram LeafParametersProgram CostAssembly.Polynomial

def polynomialEnvelope (S : ℕ) : ℕ :=
  let b0 := numberEnvelope S
  let b1 := coreEnvelope S
  let w1 := S+b0+b1+1
  let b2 := constantsBudget w1 (2*S) S
  let w2 := w1+b2+1
  let b3 := nodesBudget w2 S S S
  let w3 := w2+b3+1
  let b4 := idempotentEnvelope S w3
  let w4 := w3+b4+1
  b0+b1+b2+b3+b4+finalDiscard.length*(2*w4+3)+32

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyRingSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup
open LeafRingSetupProgram LeafParametersProgram CostAssembly.Polynomial

theorem nodes_ordinary {f g h j : ℕ → ℕ}
    (hf : Ordinary f) (hg : Ordinary g) (hh : Ordinary h) (hj : Ordinary j) :
    Ordinary (fun S => nodesBudget (f S) (g S) (h S) (j S)) := by
  unfold nodesBudget RingNodeProgram.budget RingNodeProgram.stepBudget
  simp only [RingProgram.ternary_baseWidth]
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const nodesStartPorts.length) (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 3))) (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 9) hf) (ordinary_const 8)))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 8) hf) (ordinary_const 8)) (ordinary_mul hj (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul hh (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 100) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) hg) hf) (ordinary_const 1)) 2)) (ordinary_mul (ordinary_const 14) (ordinary_mul (ordinary_const 2) hg))) (ordinary_mul (ordinary_const 8) hf)) (ordinary_const 19))) (ordinary_mul (ordinary_const 25) hf)) (ordinary_mul (ordinary_const 7) hh)) (ordinary_const 35)) (ordinary_const 1)))) (ordinary_const 5))) (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul hj (ordinary_mul hh (ordinary_mul (ordinary_const 2) hg)))) (ordinary_const 8)))) (ordinary_add (ordinary_mul hj (ordinary_add (ordinary_mul (ordinary_const 28) (ordinary_mul hh (ordinary_mul (ordinary_const 2) hg))) (ordinary_const 33))) (ordinary_const 11)))

theorem polynomialEnvelope_ordinary : Ordinary polynomialEnvelope := by
  have h0 := numberEnvelope_ordinary
  have h1 := coreEnvelope_ordinary
  have hw1 := ordinary_add (ordinary_add (ordinary_add ordinary_id h0) h1) (ordinary_const 1)
  have h2 := constants_ordinary hw1 (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id
  have hw2 := ordinary_add (ordinary_add hw1 h2) (ordinary_const 1)
  have h3 := nodes_ordinary hw2 ordinary_id ordinary_id ordinary_id
  have hw3 := ordinary_add (ordinary_add hw2 h3) (ordinary_const 1)
  have h4 := idempotent_ordinary ordinary_id hw3
  have hw4 := ordinary_add (ordinary_add hw3 h4) (ordinary_const 1)
  have hsum := ordinary_add (ordinary_add (ordinary_add (ordinary_add h0 h1) h2) h3) h4
  have htail := ordinary_mul (ordinary_const finalDiscard.length)
    (ordinary_add (ordinary_mul (ordinary_const 2) hw4) (ordinary_const 3))
  exact ordinary_add (ordinary_add hsum htail) (ordinary_const 32)

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
def encode {B degree J : ℕ} (P : Array B degree J) : List Bool := DensePolynomialProgram.encode P.1

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native arbitrary-width coefficient multiply-and-accumulate. The high
workspace computes the ring product; the low workspace updates one encoded
array cell. Its runtime index scans and all transfers are explicitly paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpConvolutionPair
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

structure Ready (s : Store) (a b c : Coeff (baseWidth p t) degree)
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool) : Prop where
  high : ∀ i, s (RingCall.ports i) =
    (RingScan.serviceState (fun _ => false) M.bits [] (RingProgram.flat a)
      (RingProgram.flat b) [] scalarWidth cache.zero.val (RingTriple.tableEncoding table)).stacks i
  low : ∀ i : Fin 20, s (lowPort (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i)) =
    (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] scalarWidth [] frame).stacks i
  array : s 102 = earlier.flatten ++ (RingProgram.flat c ++ rest)
  index : s 103 = indexWord
  indexLength : indexWord.length = earlier.length
  width : s 104 = widthWord
  widthLength : widthWord.length = degree * baseWidth p t
  rows : ∀ row ∈ earlier, row.length = widthWord.length
  scalarWidthLength : scalarWidth.length = baseWidth p t
  degreeLength : (s 204).length = degree
  scratch : s 120 = []
  work : ∀ j : Fin 256, 112 ≤ j.val → j.val ≤ 119 → s j = []

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

def stepBudget (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d) : ℕ :=
  let value := match seed.lookup k with
    | none => x
    | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
  6*(key k).length + 11*(RingProgram.flat x).length + 15 +
    Dictionary.insertBudget (Squarefree.Program.encodeDictionary key RingProgram.flat seed)
      (key k) (RingProgram.flat value) (Dictionary.codeBranchBudget (baseWidth p t) d)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

def bytes {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) : List Bool :=
  Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat entries)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def valueMul (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar x : RingProgram.Code (Word (baseWidth p t)) d) :=
  (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table scalar x).1

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Loop stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

def encode {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) : List Bool :=
  Program.rawEntries (Program.encodeDictionary key RingProgram.flat entries)

@[simp] theorem encode_nil {B d : ℕ} (key : K → List Bool) :
    encode (B := B) (d := d) key [] = [] := rfl

@[simp] theorem encode_cons {B d : ℕ} (key : K → List Bool)
    (a : K × RingProgram.Code (Word B) d) (entries) :
    encode key (a :: entries) = Encoding.frame (key a.1) ++
      Encoding.frame (RingProgram.flat a.2) ++ encode key entries := rfl

def scaled (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :=
  entries.map (fun a => (a.1, valueMul p t M cache table scalar a.2))

def loopBudget {B d : ℕ} (key : K → List Bool) :
    List (K × RingProgram.Code (Word B) d) → ℕ
  | [] => 1
  | a :: entries => stepBudget B d (key a.1).length + 2 + loopBudget key entries

def budget {B d : ℕ} (key : K → List Bool) (entries : List (K × RingProgram.Code (Word B) d)) : ℕ :=
  loopBudget key entries + 3*(encode key entries).length + 4

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Entry (n B d : ℕ) := Squarefree.Index (Fin n) × RingProgram.Code (Word B) d

def coefficientBytes {n B d : ℕ} (entries : List (Entry n B d)) : List (Squarefree.KeyMapProgram.Entry n) :=
  entries.map fun a => (a.1,RingProgram.flat a.2)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev bytes {n B d : ℕ} := @Normalize.bytes (Squarefree.Index (Fin n)) B d Squarefree.encodeIndex

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial envelopes for the concrete native raw-hash interpreter.
S bounds the number of retained keys; B and d are actual encoded coefficient
width and extension dimension. No arithmetic or parser callback is free. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open Native

variable {n B d u J S : ℕ} {vars : Finset (Fin n)}

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t)
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (hS : u*J*(Squarefree.Sparse.supportUniverse vars J).card ≤ S)

variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (hd : degree.length = d)

/-- The table consists of one actual serialized incidence dictionary for each
original variable. It is the same table for every literal occurrence. -/
def entries (incidence : Fin n → List (Product.Entry n B d)) : List (List Bool × List Bool) :=
  incidenceEntries (fun (_ : Unit) v => Product.bytes (incidence v)) ()

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev restoreOld : Cmd 8 18 := move 14 0 13

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/

end OAI.Algorithms
end


