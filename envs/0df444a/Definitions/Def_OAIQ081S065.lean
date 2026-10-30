-- Prove2me | Definitions.Def_OAIQ081S065
-- name    : OAIQ081S065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:50:10.292995+00:00
-- url     : https://prove2.me/theorems/ea8c04fe-1ee8-498c-a0ce-f89df6527481
-- title:
--   Definitions bundle OAIQ081S065 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 51 definitions and 4 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.afterAppendIndex`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.innerAfter`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.innerDone`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.outerDone`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.restore`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseOperandIO.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseOperandIO.afterParse`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseOperandIO.popped`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseOperandIO.takeResult`, `OAI.Algorithms.SubexponentialSAT.SubexpJetCellProgram.updatedState`, `OAI.Algorithms.SubexponentialSAT.SubexpJetInitProgram.repeatOut`, `OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorProgram.dimensionPopped`, `OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorProgram.registersReset`, `OAI.Algorithms.SubexponentialSAT.SubexpLiteralChunkProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpLiteralChunkProgram.straightResult`, `OAI.Algorithms.SubexponentialSAT.SubexpNegatedQueryProgram.state`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationPrefixProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationPrefixProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersets`, `OAI.Algorithms.SubexponentialSAT.SubexpPolynomialAddService.prepared`, `OAI.Algorithms.SubexponentialSAT.SubexpPolynomialMultiplyService.nativeInput`, `OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl.multiplied`, `OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl.prepared`, `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.cfg`, `OAI.Algorithms.SubexponentialSAT.SubexpPostfixInterpreter.bootProgram`, `OAI.Algorithms.SubexponentialSAT.SubexpProjectedInterpreter.bootMap`, `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.prepared`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.ClausePayload`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.decodeClause`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.decodeFields`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.encodedFormula`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.formulaRecords`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.invariant`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.pushed`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.selected`, `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.transferred` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SubexpConvolutionControl`, `SubexponentialSAT_SubexpConvolutionOuter`, `SubexponentialSAT_SubexpConvolutionRows`, `SubexponentialSAT_SubexpDenseLiteralPadding`, `SubexponentialSAT_SubexpDenseOperandIO`, `SubexponentialSAT_SubexpDenseProgram`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpJetCellProgram`, `SubexponentialSAT_SubexpJetInitProgram`, `SubexponentialSAT_SubexpLinearFactorProgram`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_SubexpNegatedQueryProgram`, `SubexponentialSAT_SubexpNormalizationPrefixProgram`, `SubexponentialSAT_SubexpNormalizationProgram`, `SubexponentialSAT_SubexpPolynomialAddService`, `SubexponentialSAT_SubexpPolynomialMultiplyService`, `SubexponentialSAT_SubexpPolynomialServiceControl`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpPostfixInterpreter`, `SubexponentialSAT_SubexpProjectedInterpreter`, `SubexponentialSAT_SubexpRowPostfixServices`, `SubexponentialSAT_SubexpTautologyFilterProgram`, `SubexponentialSAT_SubexpTautologyProgram`, `SubexponentialSAT_SubexpUnaryRangeProgram`, `SubexponentialSAT_WorkspaceCleanupProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S025`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S032`, `OAIQ081S036`, `OAIQ081S042` and `OAIQ081S043` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S081`; the statement `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.includeNodeCommand_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.initializeLocal_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsCommand_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add_spec` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S036
import Definitions.Def_OAIQ081S042
import Definitions.Def_OAIQ081S043

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite control for triangular, truncated convolution

Polynomial coefficients occupy equal-width flat cells. Both input arrays have
D cells. The left array is consumed; the right array is retained. The output
array is preallocated with D zero cells. Unary loop counters and indices are
runtime stacks, so changing D does not change this control program.

The scalar product-and-accumulate command is inserted as a fixed command. Its
concrete implementation uses the quartic multiplier and the persistent cell
updater; it is never a semantic-function instruction.
-/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

def afterAppendIndex (d : Data) (index : Fin 256) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks index (false :: d.stacks index)⟩

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The triangular convolution controller charges actual fixed-width reads,
copies, and cell writes. The local pair contract is a contract for a fixed
finite command and is instantiated by the concrete quartic/jet service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

def innerAfter (w : Buffers) (accumulator rightTail cellsLeft : List Bool) : Buffers :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update w 7 cellsLeft) 6 rightTail) 9 []) 10 []) 2 accumulator)
    3 (false :: w 3)

def innerDone (w : Buffers) (target suffix : List Bool) (count : ℕ) : Buffers :=
  Function.update (Function.update
    (Function.update (Function.update w 2 target) 3 (List.replicate count false ++ w 3))
    6 suffix) 7 []

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The outer triangular loop of the fixed convolution controller. Each row
copies the preserved right-hand array, consumes one left coefficient, and
executes only the still-relevant output positions. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

def outerDone (w : Buffers) (target : List Bool) (count : ℕ) : Buffers :=
  Function.update (Function.update (Function.update (Function.update w 0 []) 2 target)
    4 (List.replicate count false ++ w 4)) 5 []

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete postfix instruction dispatch and literal push

The fixed prefix tags are push `0`, add `10`, and multiply `11`.
A push tag is followed by an `Encoding.frame` coefficient payload. End of
the code stack ends the instruction stream. The base dispatcher exposes
explicit service exits. The linked program implements literal push through
the actual frame parser and a Boolean-stack encoding loop; scalar arithmetic
remains at explicit service boundaries.

Registers: 0 last bit, 1 successful-pop flag, 2 binary-operation flag.
Stacks: 0 serialized code, 1 unary operand depth, 2 framed operand data.
The operand data stack is preserved throughout dispatch. On a successful
dispatch the depth stack has already been adjusted for the pending service.
The linked literal service uses stack 3 as initially empty scratch and returns
to dispatch with that scratch empty and the framed operand list updated.
-/

namespace SubexponentialSAT.SubexpPostfixControl

open BitProgram

def cfg (pc : Option (Fin 20)) (value present operation : Bool)
    (code depth operands : List Bool) : Cfg 3 3 20 :=
  ⟨pc, triple value present operation, triple code depth operands⟩

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite control for dense coefficient projection

The controller below is an actual finite instruction table. Its local callback
contract is deliberately an actual `StructuredCalls.Eval` of a fixed program:
it must be discharged by the concrete lookup and record-emission programs.
It is not an assumption that an abstract ring operation takes one machine step.
The concrete callback integration and product-pair builder are separate stages.
-/

namespace SubexponentialSAT.SubexpDenseProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace RawEmitter

open SubexponentialSAT.SubexpRecordScan SubexponentialSAT.SubexpArgumentProgram

@[simp] theorem storage_update_four (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 4 x = storage a b c d x f := by
  first | done | (funext i; fin_cases i <;> rfl)

end RawEmitter

end SubexponentialSAT.SubexpDenseProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with linked arithmetic services

The interpreter contains the concrete tag dispatcher and literal loader, two
initialization instructions, and the supplied finite arithmetic instruction
tables. Arithmetic correctness is required as a local Boolean-machine trace
contract; an arithmetic operation is never added to the instruction language.
-/

namespace SubexponentialSAT.SubexpPostfixInterpreter

open BitProgram
open SubexpPostfixControl

variable {r s a b : ℕ}

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)

/-- The empty operand-list marker is written by two real instructions. -/
abbrev bootProgram : Program 3 4 3 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := fun pc => if pc = 0 then .set 0 false 1
    else if pc = 1 then .push 2 0 2 else .halt

end SubexponentialSAT.SubexpPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

open BitProgram
open SubexpPostfixControl

@[simp] theorem registers_update0 (v p op b : Bool) :
    Function.update (registers v p op) 0 b = registers b p op := by
  funext i
  fin_cases i <;> simp [registers, Function.update, triple, Fin.addCases]
@[simp] theorem registers_update1 (v p op b : Bool) :
    Function.update (registers v p op) 1 b = registers v b op := by
  funext i
  fin_cases i <;> simp [registers, Function.update, triple, Fin.addCases]
@[simp] theorem registers_update2 (v p op b : Bool) :
    Function.update (registers v p op) 2 b = registers v p b := by
  funext i
  fin_cases i <;> simp [registers, Function.update, triple, Fin.addCases]

open SubexpPostfixGlobal

/-! ## Entry from arbitrary caller registers -/

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseOperandIO
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite framing operations at the physical postfix operand port.
These routines preserve the code/depth stacks and all surrounding data. -/

namespace SubexponentialSAT.SubexpDenseOperandIO

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 128

abbrev afterParse (d : Data) (bits tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks 27 tail) 29 bits.reverse⟩

def popped (d : Data) : Data := (StructuredProgram.Atom.pop 27 0 1).eval d

def takeResult (d : Data) (dst : Fin 128) (bits tail : List Bool) : Data :=
  afterTransfer (afterParse (popped d) bits tail) 29 dst 0 1

end SubexponentialSAT.SubexpDenseOperandIO

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Padding arbitrary literal payloads for the dense interpreter

The existing five-label padding table already truncates long inputs. This
module proves that behavior without a length precondition, then connects the
table to the actual framed operand stack. The cached dense zero array supplies
the requested bit width; no dimension is baked into the program control.
-/

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store )

noncomputable def restore (s : Store) (small : Fin 128 → List Bool) : Store :=
  Function.extend smallPorts small s

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetCellProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete addition into one packed jet cell

The persistent jet, unary index, and cell width are on stacks 102, 103, and
104. The array subprogram uses 112--117, and order-preserving moves use 118.
All instruction tables are fixed independently of widths and indices. The
full service reads the old cell, invokes the actual flattened quartic adder,
and writes the sum back. Its endpoint changes only the contribution and jet
stacks; all other caller stacks and registers 8--15 are preserved.
-/

namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

/-- The explicit state expression obtained by composing the eight services. -/
def updatedState (d : Data) (regs : Fin 8 → Bool) (old result : List Bool)
    (earlier : List (List Bool)) (rest : List Bool) : Data :=
  let d₁ := afterCopy d 103 113 0 1
  let d₂ := readOut d₁ old
  let d₃ := moveOut d₂ 112 9
  let d₄ := addOut d₃ regs result
  let d₅ := moveOut d₄ 8 112
  let d₆ := afterCopy d₅ 103 113 0 1
  let d₇ := replaceOut d₆ earlier result rest
  clearOut d₇ 112

end SubexponentialSAT.SubexpJetCellProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Initializing the packed output jet

The input dimension is a unary word on stack 109 and the scalar word width is
the length of stack 10.  The fixed program constructs one four-word zero
coefficient on stack 104 and copies it D times to stack 102.  It preserves both
input words.  No zero array is supplied as an input certificate.
-/

namespace SubexponentialSAT.SubexpJetInitProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def repeatOut (d : Data) (D : ℕ) (cell output : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    Function.update (Function.update d.stacks 108 []) 102
      (Subexp.BlockCopyProgram.copies D cell ++ output)⟩

end SubexponentialSAT.SubexpJetInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLinearFactorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime construction of a padded linear polynomial. The low and high
coefficient cells occupy stacks 100 and 101. The unary dimension is on 109,
the base-word width is on 10, and the output array is on 102. -/

namespace SubexponentialSAT.SubexpLinearFactorProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev registersReset (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false, d.stacks⟩

abbrev dimensionPopped (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks 108).head?, Function.update d.stacks 108 (d.stacks 108).tail⟩

end SubexponentialSAT.SubexpLinearFactorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiteralChunkProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual literal-index to chunk-index conversion

The input is one reversed canonical unary literal field and a binary chunk
width. The fixed program decodes the variable index, counts it into binary,
divides by the chunk width, and constructs the reversed canonical chunk field.
-/

namespace SubexponentialSAT.SubexpLiteralChunkProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 19

def straightResult : List (StructuredProgram.Atom 8 19) → Data → Data
  | [], d => d
  | a :: as, d => straightResult as (a.eval d)

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNegatedQueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving complemented-literal queries

The clause iterator supplies a literal's unary word in reverse order. This
fixed program preserves that query on stack 0 and writes the reversed unary
word for the opposite literal on stack 1. Stacks 2 and 3 are empty workspaces
on entry and return. All costs below count actual finite-program transitions.
-/

namespace SubexponentialSAT.SubexpNegatedQueryProgram

open BitProgram StructuredCalls
open ParserProgram (pair)

abbrev state (value present : Bool) (query result work scratch : List Bool) : State 2 4 :=
  ⟨pair value present, slots query result work scratch⟩

end SubexponentialSAT.SubexpNegatedQueryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded-clause tautology testing

The outer iterator reads unary literal records. For each literal, a concrete
program builds its opposite's query, copies the preserved clause, and runs the
proved encoded membership program. All data-dependent repetition is in those
finite programs and the record iterator.
-/

namespace SubexponentialSAT.SubexpTautologyProgram

open BitProgram StructuredCalls

abbrev Data := State 10 8

def mark (d : Data) : Data :=
  ⟨Function.update d.regs 9 (d.regs 4), d.stacks⟩

def invariant (C : List ℕ) (d : Data) : Prop :=
  d.stacks 2 = encodedClause C ∧ d.stacks 1 = [] ∧ d.stacks 3 = [] ∧
    d.stacks 4 = [] ∧ d.stacks 5 = [] ∧ d.stacks 6 = []

def perLiteralCost (C : List ℕ) (bits : List Bool) : ℕ :=
  100 * ((encodedClause C).length + 1) * (bits.length + 1)

def initialized (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 0 2 d.stacks⟩

def Ready (d : Data) : Prop := ∀ i : Fin 8, i ≠ 0 → d.stacks i = []

def finished (d : Data) : Data :=
  ⟨(ExecCNFSubset.cleared 0 d).regs,
    Function.update (ExecCNFSubset.cleared 0 d).stacks 1 [d.regs 9]⟩

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

open BitProgram StructuredCalls

abbrev Data := State 13 11

def decodeFields : List (List Bool) → Option (List ℕ)
  | [] => some []
  | bits :: rest => do
      let (c, tail) ← Encoding.readNat bits
      if tail.isEmpty then
        let cs ← decodeFields rest
        pure (c :: cs)
      else none

def decodeClause (bits : List Bool) : Option (List ℕ) := do
  let (fields, rest) ← ProgramEncoding.readRecords bits
  if rest.isEmpty then decodeFields fields else none

def transferred (source target : Fin 11) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks source target d.stacks⟩

def cleared (port : Fin 11) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

def selected (d : Data) : Data :=
  ⟨Function.update d.regs 12 (!(d.regs 9)), d.stacks⟩

def invariant (d : Data) : Prop := ∀ i : Fin 11, 3 ≤ i.val → d.stacks i = []

def ClausePayload (bits : List Bool) : Prop :=
  ∃ C : List ℕ, bits = SubexpTautologyProgram.encodedClause C

def formulaRecords (F : List (List ℕ)) : List (List Bool) :=
  F.map SubexpTautologyProgram.encodedClause

def encodedFormula (F : List (List ℕ)) : List Bool :=
  Encoding.encodeList SubexpTautologyProgram.encodedClause F

def pushed (stack : Fin 11) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

def Ready (d : Data) : Prop := invariant d ∧ d.stacks 1 = [] ∧ d.stacks 2 = []

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Actual literal cleanup followed by tautology removal

This is a fixed program on the original declared variable universe. Its two
stages use the same input/output port and restore empty work stacks. The exact
list order and the length bound are retained for subsequent clause absorption.
-/

namespace SubexponentialSAT.SubexpNormalizationPrefixProgram

open BitProgram StructuredCalls

abbrev Data := State 13 11
abbrev Ready := ExecCleanLiteralsProgram.Ready

end SubexponentialSAT.SubexpNormalizationPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

abbrev Data := State 15 16

def removeSupersets (F : List (List ℕ)) : List (List ℕ) :=
  F.filter fun C => !(F.any fun D => ExecCNF.strictSubset D C)

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialAddService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cached dense addition for the local CRT controller. The fixed service
copies operands 240/241, invokes the actual dense-add instruction table, and
moves its output to 244. All native workspace is restored. -/

namespace SubexponentialSAT.SubexpPolynomialAddService

open BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def prepared (s : Store) : Store :=
  Function.update (Function.update s 8 (s 240)) 9 (s 241)

end SubexponentialSAT.SubexpPolynomialAddService

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialServiceControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical marshalling for a reusable truncated-product service. Cached
operands, a zero array, and the unary dimension occupy 240--243. The native
convolution buffers are restored after each invocation and the result goes
to 244. All copying, clearing, and reversal is performed by fixed programs. -/

namespace SubexponentialSAT.SubexpPolynomialServiceControl

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl

def prepared (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    100 (s 240)) 101 (s 241)) 102 (s 242)) 106 (s 243)

def multiplied (s : Store) (out : List Bool) : Store :=
  Function.update (Function.update s 101 (s 241)) 102 out

end SubexponentialSAT.SubexpPolynomialServiceControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialMultiplyService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A reusable concrete multiplication service for local CRT loops. The
native convolution workspace is empty again on return; only output 244 is
changed. Runtime polynomial arrays and the unary dimension are cached in
240--243. This module composes physical copy/clear loops with the actual
quartic convolution program. -/

namespace SubexponentialSAT.SubexpPolynomialMultiplyService

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def nativeInput (s : Store) : Buffers :=
  ![s 240, s 241, s 242, [], [], s 243, [], [], [], [], []]

end SubexponentialSAT.SubexpPolynomialMultiplyService

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpProjectedInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with a real literal-projection call

The literal bytes are parsed and pushed by the concrete loader, then passed to
an actual finite projection service before dispatch resumes. Arithmetic and
projection contracts refer to traces of supplied Boolean instruction tables.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open BitProgram
open SubexpPostfixControl (triple controlLabel literalLabel pushLoopProgram
  literalService serializeCode serializeInstr operandDepth)
open SubexpPostfixInterpreter (register stack bootProgram )

variable {r s a b c : ℕ}

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)
  (loader : Program (3 + r) (4 + s) c)

def bootMap : Fin 3 → Fin (37 + (2 + (a + (b + c)))) :=
  triple (bootLabel 0) (bootLabel 1) (baseLabel 0)


end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Framed arithmetic calls for source-row postfix expressions

The physical interpreter keeps its operand list on stack 27. These fixed
commands read two framed operands, call a dense polynomial service on
240/241, and frame its result from 244. All temporary stacks are restored;
the caller's remaining operands and every other stack are preserved.
-/

namespace SubexponentialSAT.SubexpRowPostfixServices

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl (Store Data )

def prepared (s : Store) (left right tail : List Bool) : Store :=
  Function.update (Function.update (Function.update s 27 tail) 241 right) 240 left

end SubexponentialSAT.SubexpRowPostfixServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

open BitProgram StructuredCalls SubexpIncidencePlanPrimitives

abbrev Data := StructuredProgram.State 10 10

abbrev data (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) : Data :=
  ⟨regs, ![base.stacks 0, [], base.stacks 2, [], base.stacks 4,
    unary j, unary n, out, base.stacks 8, base.stacks 9]⟩

def selected (d : Data) : Data := ⟨Function.update d.regs 4 true, d.stacks⟩

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_WorkspaceCleanupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual fixed workspace cleanup

The selected ports are part of the finite program. Their initial contents
and lengths are arbitrary. Every clear is an existing measured instruction
loop, and all unselected stacks and non-scratch registers are preserved.
-/

namespace SubexponentialSAT.WorkspaceCleanupProgram

open BitProgram StackRoutines StructuredCalls

def cost {r s : ℕ} (ports : List (Fin s)) (d : State r s) : ℕ :=
  2 * (ports.map (fun i => (d.stacks i).length)).sum + 3 * ports.length

end SubexponentialSAT.WorkspaceCleanupProgram

end OAI.Algorithms
end


