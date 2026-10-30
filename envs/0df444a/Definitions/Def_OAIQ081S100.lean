-- Prove2me | Definitions.Def_OAIQ081S100
-- name    : OAIQ081S100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:19:36.734917+00:00
-- url     : https://prove2.me/theorems/70aa2a44-9696-4dd2-853e-335881519ec2
-- title:
--   Definitions bundle OAIQ081S100 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 62 definitions and 15 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.constant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.inverseCoefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.linear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.padded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.scalarAdd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.scalarMul`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.zero`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.binaryStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.callAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.constantCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.defectCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.differenceCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.differenceInverseCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.geometricAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.hornerCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.hornerStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.includeNodeCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.initializeLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.linearFactorCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.nativeRepeat`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.positiveLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.repairCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.replace`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.scanCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.seedCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.seq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.seq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.conversionPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CRTLocalProgram`, `SubexponentialSAT_SqrtLog_CRTLocalProgramCall`, `SubexponentialSAT_SqrtLog_CRTLocalProgramConstant`, `SubexponentialSAT_SqrtLog_CRTLocalProgramCorrection`, `SubexponentialSAT_SqrtLog_CRTLocalProgramDifference`, `SubexponentialSAT_SqrtLog_CRTLocalProgramFactor`, `SubexponentialSAT_SqrtLog_CRTLocalProgramGeometricAt`, `SubexponentialSAT_SqrtLog_CRTLocalProgramHorner`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInclude`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInverse`, `SubexponentialSAT_SqrtLog_CRTLocalProgramLoops`, `SubexponentialSAT_SqrtLog_CRTLocalProgramModel`, `SubexponentialSAT_SqrtLog_CRTLocalProgramModelCorrectness`, `SubexponentialSAT_SqrtLog_CRTLocalProgramNative`, `SubexponentialSAT_SqrtLog_CRTLocalProgramScan`, `SubexponentialSAT_SqrtLog_CodeParametersProgramUnary`, `SubexponentialSAT_SqrtLog_DensePolynomialProgram`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramFixed`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramMul`, `SubexponentialSAT_SqrtLog_HornerProgramServices`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_ReconstructionProgramRing`, `SubexponentialSAT_SqrtLog_RingProgramFold`, `SubexponentialSAT_SqrtLog_RingProgramModel`, `SubexponentialSAT_SqrtLog_RingScanContractBridge`, `SubexponentialSAT_SubexpPolynomialIterationControl`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports the bundles `OAIQ081S082` and `OAIQ081S083` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S116`, `OAIQ081S117`, `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S120`, `OAIQ081S121`, `OAIQ081S122`, `OAIQ081S123`, `OAIQ081S124`, `OAIQ081S125`, `OAIQ081S126`, `OAIQ081S127`, `OAIQ081S128`, `OAIQ081S129`, `OAIQ081S130`, `OAIQ081S131`, `OAIQ081S132`, `OAIQ081S133`, `OAIQ081S134`, `OAIQ081S135`, `OAIQ081S136` and `OAIQ081S137`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionCommand_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.includeNodeCommand_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.physicalCap_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.add_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_UnaryForPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control unary-counted callbacks

The counter is a Boolean stack whose length is the iteration count. Its bits
are ignored. The controller pops before each callback and tests the presence
flag; callbacks preserve the remaining counter tail and may clobber all
registers. Every observation contains an actual callback evaluation.
-/

namespace SubexponentialSAT.UnaryForPrograms

open BitProgram StructuredProgram
open CounterForPrograms (budgetSum)

variable {R S : ℕ}

def popped (p : Ports R S) (d : Data R S) : Data R S :=
  ⟨readRegs d.regs p.bit p.flag (d.stacks p.counter).head?,
    Function.update d.stacks p.counter (d.stacks p.counter).tail⟩

@[simp] theorem popped_counter (p : Ports R S) (d : Data R S) :
    (popped p d).stacks p.counter = (d.stacks p.counter).tail := by simp [popped]

@[simp] theorem popped_flag (p : Ports R S) (d : Data R S) :
    (popped p d).regs p.flag = (d.stacks p.counter).head?.isSome := by
  simp [popped, readRegs]

abbrev loopCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .while p.flag (.seq body (popCmd p))

abbrev forCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .seq (popCmd p) (loopCmd p body)

@[simp] theorem size_forCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.size (forCmd p body) = StructuredCalls.size body + 3 := by
  simp [ StructuredCalls.size, StructuredProgram.size]
  omega

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialIterationControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusing the polynomial multiplication workspace in a runtime-counted
loop. The output on 244 is moved back to accumulator 240, with all temporary
bits erased. The loop itself is the verified unary controller. -/

namespace SubexponentialSAT.SubexpPolynomialIterationControl

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

def commit : Code := .seq (clear 240) (.seq (transfer 244 245) (transfer 245 240))

def step (service : Code) : Code := .seq service commit

def counterPorts : UnaryForPrograms.Ports 16 256 := ⟨246, 0, 1⟩
def repeatLoop (iteration : Code) : Code := UnaryForPrograms.forCmd counterPorts iteration

end SubexponentialSAT.SubexpPolynomialIterationControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramLoops
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native loops used by independent-precision local Hermite CRT.

The arithmetic argument is a finite `Cmd`, never a semantic instruction.
`ServiceSpec` is the exact trace contract discharged by the native represented
ring/array callbacks. All iteration counts remain on runtime stack 246.
-/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def binaryStep (code : Code) : Code := SubexpPolynomialIterationControl.step code
def nativeRepeat (code : Code) : Code := SubexpPolynomialIterationControl.repeatLoop code

/-- Replace a high persistent port by a preserving copy from another port. -/
def replace (src dst : Fin 256) : Code := .seq (clear dst) (copy src dst)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native fixed-control Horner iteration, shared by scalar nilpotent repair
and the independently truncated local polynomial inverse. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def hornerStep (multiply add : Code) : Code :=
  .seq (binaryStep multiply)
    (.seq (replace 220 241) (.seq (binaryStep add) (replace 222 241)))

def hornerCommand (multiply add : Code) : Code := nativeRepeat (hornerStep multiply add)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native residue-power preparation with dynamic extension degree and ring
precision. Stack 209 contains a unary residue-size-minus-two exponent;
stack 212 independently contains the unary ring precision. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def seq_p1 (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq_p1

def seedCommand (multiply : Code) : Code :=
  replace 207 240 ;; replace 205 241 ;; replace 209 246 ;;
    nativeRepeat (binaryStep multiply) ;; replace 240 208

/-- The remaining scalar inverse stages: form the residue defect, then run
the precision-many geometric recurrence. Every operator is a fixed command. -/
def defectCommand (multiply add : Code) : Code :=
  binaryStep multiply ;; replace 211 241 ;; binaryStep multiply ;;
    replace 207 241 ;; binaryStep add ;; replace 240 222

def repairCommand (multiply add : Code) : Code :=
  replace 104 240 ;; replace 222 241 ;; replace 207 220 ;; replace 212 246 ;;
    hornerCommand multiply add ;; replace 208 241 ;; binaryStep multiply ;;
    replace 240 208 ;;
    SubexpLocalCRTSetup.clearMany [220, 222, 240, 241]

def inverseCommand (multiply add : Code) : Code :=
  seedCommand multiply ;; defectCommand multiply add ;; repairCommand multiply add

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed native binary calls at arbitrary persistent ports. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def callAt (code : Code) (left right dst : Fin 256) : Code :=
  .seq (replace left 240) (.seq (replace right 241)
    (.seq code (.seq (SubexpLocalCRTSetup.clearMany [240,241])
      (.seq (replace 244 dst) (clear 244)))))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramGeometricAt
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def geometricAt (multiply add : Code) : Code :=
  .seq (replace 242 240) (.seq (replace 222 241) (.seq (replace 243 246)
    (.seq (hornerCommand multiply add) (.seq (replace 240 224)
      (SubexpLocalCRTSetup.clearMany [240,241])))))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCorrection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native local Hermite correction once the truncated cofactor and its
constant inverse have been prepared. Only output244 changes. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def correctionCommand (multiply add : Code) : Code :=
  .seq (callAt multiply 223 228 222)
    (.seq (callAt add 222 220 222)
      (.seq (geometricAt multiply add)
        (.seq (callAt multiply 224 227 224)
          (.seq (callAt multiply 224 225 224)
            (.seq (replace 224 244) (SubexpLocalCRTSetup.clearMany [222,224]))))))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def constantCommand : Code :=
  .seq (copy 223 247) (.seq (takeCell 247 205) (clear 247))

/-- All coefficient-to-polynomial padding is performed by native constructor
loops. The scalar inverse uses t, while each constructor uses J. -/
def inverseConstantsCommand (sm sa : Code) : Code :=
  .seq (inverseCommand sm sa)
    (.seq (callAt sm 208 211 205)
      (.seq (SubexpPolynomialConstructor.construct 208 104 227)
        (.seq (SubexpPolynomialConstructor.construct 205 104 228)
          (SubexpLocalCRTSetup.clearMany [205,208]))))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramDifference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical inverse builder for a difference of two supplied nodes. The
residue exponent and nilpotence precision are the independent runtime inputs
209 and 212; no loop enumerates the lifted ring. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def differenceCommand (multiply add : Code) : Code :=
  .seq (callAt multiply 218 211 219) (.seq (callAt add 213 219 205) (clear 219))

def differenceInverseCommand (multiply add : Code) : Code :=
  .seq (differenceCommand multiply add) (.seq (inverseCommand multiply add) (clear 205))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def linearFactorCommand (multiply add : Code) : Code :=
  .seq (differenceCommand multiply add)
    (.seq (SubexpPolynomialConstructor.construct 205 207 241) (clear 205))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInclude
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One included-node update of the truncated local cofactor. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def includeNodeCommand (scalarMultiply scalarAdd polynomialMultiply : Code) : Code :=
  .seq (replace 240 223) (.seq (clear 240)
    (.seq (linearFactorCommand scalarMultiply scalarAdd)
      (.seq (replace 223 240) (.seq (clear 223) (.seq (replace 243 246)
        (.seq (nativeRepeat (binaryStep polynomialMultiply)) (clear 241)))))))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def scanCommand (sm sa pm : Code) : Code :=
  SubexpNodeScanControl.command (includeNodeCommand sm sa pm)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed native local-Hermite controller. Ring precision is read from212
and jet order from243. Protected polynomial service metadata192/193 are
prepared by the caller. All arithmetic calls are ordinary finite programs. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def seq_p0 (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq_p0

def initializeLocal : Code :=
  SubexpPolynomialConstructor.construct 207 104 240 ;;
  copy 214 215 ;; copy 216 217 ;; SubexpLocalCRTSetup.token 229

def prepareLocalInverse (sm sa : Code) : Code :=
  SubexpLocalCRTSetup.clearMany [217,229] ;;
  replace 240 223 ;; clear 240 ;; constantCommand ;;
  inverseConstantsCommand sm sa ;;
  SubexpPolynomialConstructor.construct 207 104 220 ;;
  copy 192 242

def positiveLocal (sm sa pm pa : Code) : Code :=
  initializeLocal ;; scanCommand sm sa pm ;; prepareLocalInverse sm sa ;;
  correctionCommand pm pa ;; SubexpLocalCRTSetup.clearMany [220,223,227,228,242]

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete ternary coefficient input and the executable represented arithmetic
for the supplied-polynomial unramified ring model. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

theorem modelPolynomial (t : ℕ) (ht : 0 < t) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    quotientPolynomial (scalarRing 3 t M cache) (liftCoefficientsRun t a.coefficients).1 =
      a.F t := by
  unfold quotientPolynomial RingModel.Data.F
  congr 1
  funext i
  exact liftCoefficientsRun_correct t ht a.coefficients i

/-- An entirely executable program for the actual supplied ternary polynomial.
Its table and coefficient words can be retained across all later operations. -/
def modelProgram (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    RingProgram (Code (ScalarCode 3 t) d) :=
  quotientProgram (scalarProgram 3 t M cache) (liftCoefficientsRun t a.coefficients).1

/-- Explicit preparation retains both coefficient words and the generated table. -/
def modelProgramRun (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    RingProgram (Code (ScalarCode 3 t) d) × ℕ :=
  let coefficients := liftCoefficientsRun t a.coefficients
  let prepared := quotientProgramRun (scalarProgram 3 t M cache) coefficients.1
  (prepared.1, coefficients.2 + prepared.2)

@[simp] theorem modelProgramRun_value (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    (modelProgramRun t a M cache).1 = modelProgram t a M cache := rfl

noncomputable def modelRing (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) : RepresentedRing (Code (ScalarCode 3 t) d) (a.O t) := by
  letI : Fact (1 < 3^t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  let ops := scalarRing 3 t M cache
  let c := (liftCoefficientsRun t a.coefficients).1
  have hf : quotientPolynomial ops c = a.F t := modelPolynomial t ht a M cache
  exact represented ops (SubexponentialSAT.LiftRing.of (a.F t)) (RingBasis.basis (a.F t))
    (structureTableRun ops.program c).1 (zeroVector ops.program d) (oneVectorRun ops.program d).1
    (by
      intro i j
      rw [RingBasis.basis_mul (a.F t) (a.F_monic t ht) (a.F_degree t ht) i j]
      apply Finset.sum_congr rfl
      intro k _
      have hc : ops.decode ((structureTableRun ops.program c).1 i j k) =
          RingBasis.structureConstant (a.F t) i j k := by
        rw [structureTableRun_remainder ops hd]
        change (Polynomial.X^(i.val+j.val) %ₘ quotientPolynomial ops c).coeff k = _
        rw [hf]
        rfl
      rw [hc])
    (by simp only [denote, zeroVector, ops.zero_correct,
      map_zero, zero_mul, Finset.sum_const_zero])
    (by
      have hc (i : Fin d) : ops.decode ((oneVectorRun ops.program d).1 i) =
          RingBasis.coordinates (a.F t) (a.F_monic t ht) (a.F_degree t ht) 1 i := by
        rw [RingBasis.one_coordinates _ _ _ hd]
        exact congrFun (oneVectorRun_correct ops d) i
      unfold denote
      simp_rw [hc]
      exact RingBasis.reconstruct _ _ _ 1)

@[simp] theorem modelRing_program (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) :
    (modelRing t ht hd a M cache).program = modelProgram t a M cache := rfl

/-- The decoder is exactly reconstruction from the model's coefficient basis. -/
theorem modelRing_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) :
    (modelRing t ht hd a M cache).decode x =
      (a.coordinates t ht).symm (fun i => wordValue 3 t (x i)) := by
  change (∑ i, SubexponentialSAT.LiftRing.of (a.F t) (wordValue 3 t (x i)) * RingBasis.basis (a.F t) i) = _
  exact (RingBasis.coordinates_symm (a.F t) (a.F_monic t ht) (a.F_degree t ht) _).symm

@[simp] theorem modelRing_coordinates (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) :
    a.coordinates t ht ((modelRing t ht hd a M cache).decode x) =
      (fun i => wordValue 3 t (x i)) := by
  rw [modelRing_decode]
  exact (a.coordinates t ht).apply_symm_apply _

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Coeff (B d : ℕ) := RingProgram.Code (Word B) d

def words {B d : ℕ} (P : List (Coeff B d)) : List (Word B) :=
  P.flatMap List.ofFn

def encode {B d : ℕ} (P : List (Coeff B d)) : List Bool :=
  (P.map RingProgram.flat).flatten

@[simp] theorem words_length {B d : ℕ} (P : List (Coeff B d)) :
    (words P).length = P.length * d := by
  induction P with
  | nil => simp [words]
  | cons a P ih => simp [words, Nat.add_mul, Nat.add_comm]

@[simp] theorem encode_cons {B d : ℕ} (a : Coeff B d) (P : List (Coeff B d)) :
    encode (a :: P) = RingProgram.flat a ++ encode P := rfl

@[simp] theorem encode_nil {B d : ℕ} : encode ([] : List (Coeff B d)) = [] := rfl

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramMul
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dense convolution and old-compatible cached-array services.
The local pair premise is an actual fixed-command trace; all scans, writes,
copies, counter steps, and final halts are included by the audited controller.
A concrete native ring-pair instantiation is supplied separately. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*}

def result (ops : RingProgram C) (J : ℕ) (P Q : List C) : List C :=
  SubexponentialSAT.TruncatedConvolution.run ops.zeroRun.1
    (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) J P Q

@[simp] theorem result_length (ops : RingProgram C) (J : ℕ) (P Q : List C) :
    (result ops J P Q).length = J := SubexponentialSAT.TruncatedConvolution.run_length _ _ _ _ _ _

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

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
abbrev Array (B degree J : ℕ) := {P : List (Coeff B degree) // P.length = J}

def add {B degree J : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff B degree))
    (P Q : Array B degree J) : Array B degree J :=
  ⟨(SubexponentialSAT.SubexpDensePolynomial.addProgram ops P.1 Q.1).1, by
    rw [SubexponentialSAT.SubexpPolynomialAddService.addProgram_length,P.2,Q.2,Nat.max_self]⟩
def mul {B degree J : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff B degree))
    (P Q : Array B degree J) : Array B degree J :=
  ⟨result ops J P.1 Q.1,result_length ops J P.1 Q.1⟩


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-length array instantiation of the local Hermite algebra. The
constructor and head split are exact identities of physical bit strings. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Model
open Polynomial
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram

abbrev Poly (B d J : ℕ) := Fixed.Array B d J

noncomputable def denote {B d J : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (P : Poly B d J) : R[X] :=
  SubexponentialSAT.PolynomialAlgorithm.denote (P.1.map decode)

def padded {B d : ℕ} (zero low high : Coeff B d) (J : ℕ) : Poly B d J :=
  ⟨Constructor.coefficients zero low high J, Constructor.coefficients_length _ _ _ _⟩

def constant {B d : ℕ} (zero a : Coeff B d) (J : ℕ) : Poly B d J := padded zero a zero J

def linear {B d : ℕ} (zero one a : Coeff B d) (J : ℕ) : Poly B d J := padded zero a one J

def zero {B d : ℕ} (z : Coeff B d) (J : ℕ) : Poly B d J :=
  ⟨List.replicate J z, by simp⟩

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramModelCorrectness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Model
open Polynomial
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram

variable {B d J : ℕ} {R : Type*} [CommRing R]

def scalarMul (ops : RepresentedRing (Coeff B d) R) (a b : Coeff B d) : Coeff B d :=
  (ops.program.mulRun a b).1

def scalarAdd (ops : RepresentedRing (Coeff B d) R) (a b : Coeff B d) : Coeff B d :=
  (ops.program.addRun a b).1

def inverseCoefficient (ops : RepresentedRing (Coeff B d) R)
    (minusOne c : Coeff B d) (q t : ℕ) : Coeff B d :=
  inverseValue (scalarMul ops) (scalarAdd ops) ops.zeroRun.1 ops.oneRun.1 minusOne c (q-2) t

def corrected (ops : RepresentedRing (Coeff B d) R) (minusOne c : Coeff B d)
    (q t : ℕ) (factor jet : Poly B d J) : Poly B d J :=
  let z := ops.zeroRun.1
  let a := inverseCoefficient ops minusOne c q t
  correctionValue (Fixed.mul ops.program) (Fixed.add ops.program)
    (zero z J) (constant z ops.oneRun.1 J)
    (constant z (scalarMul ops a minusOne) J) (constant z a J) factor jet J

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

def coordinateTriples {d : ℕ} (table : Fin d → Fin d → Fin d → C)
    (x y : Code C d) (k : Fin d) : List (Triple C) :=
  (List.ofFn fun i : Fin d => List.ofFn fun j : Fin d => (x i, y j, table i j k)).flatten

@[simp] theorem coordinateTriples_length {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) (k : Fin d) :
    (coordinateTriples table x y k).length = d * d := by
  simp [coordinateTriples, List.length_flatten, List.map_ofFn, List.sum_ofFn]

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContractBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Whole-vector native multiplication after explicitly paid triple expansion. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- The required source format groups the triple stream by output coordinate,
then by the two operand indices. Producing it is a separate paid program. -/
def multiplicationBlocks {d B : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) : List (List (WordTriple B)) :=
  List.ofFn fun k : Fin d => RingProgram.coordinateTriples table x y k

@[simp] theorem multiplicationBlocks_length {d B : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) (x y : RingProgram.Code (Word B) d) :
    (multiplicationBlocks table x y).length = d := by simp [multiplicationBlocks]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dense-polynomial arithmetic with arbitrary runtime ring
coefficient width. Native ring multiplication and every convolution scan are
included in the cost, and the output has the usual polynomial meaning. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def nativeMulProgram := compiled nativeMulCommand 240 244

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {degree : ℕ}
  (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
  (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

@[simp] theorem model_add_native (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (x y : Coeff (baseWidth 3 t) d) :
    ((RingProgram.modelProgram t a M cache).addRun x y).1 =
      (RingProgram.addRun (RingProgram.scalarProgram 3 t M cache) x y).1 := rfl

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-length coefficient-array carriers for the local CRT/Horner loops.
The multiplication service obtains its zero array and length from protected
caches192/193. The relocation is in the finite instruction table, so no tape
copy is charged or hidden by the change of physical port names. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod


def mulCommand : Code := .call (ProgramLinking.liftProgram nativeMulProgram id ports)

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving CRT adapters for the native arbitrary-degree ring
programs. The adapter is a fixed finite table. Its cost includes three input
copies, the actual native trace, output copying and cleanup. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

abbrev nativeCall {l : ℕ} (p : Program 8 32 l) : Code :=
  .call (ProgramLinking.liftProgram p registers ports)

abbrev command {l : ℕ} (p : Program 8 32 l) : Code :=
  .seq (copy 240 136) (.seq (copy 241 137) (.seq (copy 204 139)
    (.seq (nativeCall p) (.seq (copy 128 244) (clear 128)))))

end SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (ServiceSpec)

def add : Code := ReconstructionProgram.RingAdapter.command RingScan.serviceAddProgram
def multiply : Code := ReconstructionProgram.RingAdapter.command RingScan.serviceMulProgram

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual native scalar and polynomial programs instantiate every local
service. The remaining hypotheses concern bytes and clean workspace. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram

def budget (nodes index q t d J : ℕ) : ℕ :=
  localBudget nodes index (q-2) t J
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (nativeMulBudget J d (baseWidth 3 t))
    (AddService.budget d (baseWidth 3 t) J J)
    (d*baseWidth 3 t) (J*(d*baseWidth 3 t))

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/


/-! Explicit paid binary-to-unary copies for code-search metadata. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

def conversionPorts (o : Fin 64) : Fin 3 → Fin 77 :=
  ![port 62,port o,work 1 (by decide) 0]

end SubexponentialSAT.SqrtLog.CodeParametersProgram

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

abbrev clearCarry : Cmd 8 18 := .call (StackRoutines.clearProgram 0 0 1)

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


