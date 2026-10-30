-- Prove2me | Definitions.Def_OAIQ081S028
-- name    : OAIQ081S028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:28:06.681663+00:00
-- url     : https://prove2.me/theorems/3e45bc6c-aced-47e1-865d-93c8053f9bde
-- title:
--   Definitions bundle OAIQ081S028 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 140 declarations of OpenAI's Lean: 88 definitions, 1 instance and 51 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.defectState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.initializedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localUpdate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.loopReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.preparedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.repairState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.seedState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.pop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowPayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.resetLog`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter.callResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter.finalNative`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter.initialNative`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.addState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractCopyCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractCopyZero`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractEmit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractFinish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractPop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.countCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.countInit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.countLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.countPop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.countScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.countSquare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.countSquareProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.countState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.emitReverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.finishAdd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.popCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.restoreAccumulator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceAfterClear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceAfterCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceAfterTransfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceCopy` and 48 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ProgramStateFrames`, `SubexponentialSAT_SqrtLog_CRTLocalProgramCall`, `SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionInit`, `SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionPrepare`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInverse`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInverseTrace`, `SubexponentialSAT_SqrtLog_CRTLocalProgramLoops`, `SubexponentialSAT_SqrtLog_CRTLocalProgramScan`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCell`, `SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic`, `SubexponentialSAT_SqrtLog_CodeRowsProgramSlots`, `SubexponentialSAT_SqrtLog_CodeRowsProgramStream`, `SubexponentialSAT_SqrtLog_CodeRowsProgramVertex`, `SubexponentialSAT_SqrtLog_LeafParametersProgramLog`, `SubexponentialSAT_SqrtLog_ReconstructionProgramRing`, `SubexponentialSAT_SqrtLog_RingScanAdd`, `SubexponentialSAT_SqrtLog_RingScanAddLoop`, `SubexponentialSAT_SqrtLog_RingScanContract`, `SubexponentialSAT_SqrtLog_RingScanContractLoop`, `SubexponentialSAT_SqrtLog_RingScanCount`, `SubexponentialSAT_SqrtLog_RingScanLoad`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RingScanServiceAdd`, `SubexponentialSAT_SqrtLog_RingScanServiceBasic`, `SubexponentialSAT_SqrtLog_RingScanServiceLifts`, `SubexponentialSAT_SqrtLog_RingScanTriple`, `SubexponentialSAT_SqrtLog_RingTripleBasic`, `SubexponentialSAT_SqrtLog_RingTripleBridge`, `SubexponentialSAT_SqrtLog_RingTripleExpand`, `SubexponentialSAT_SqrtLog_RingTripleMatrix`, `SubexponentialSAT_SqrtLog_RingTripleProgram`, `SubexponentialSAT_SqrtLog_RingTripleRows`, `SubexponentialSAT_SqrtLog_SetupGuard`, `SubexponentialSAT_SubexpBlockParameterProgram`, `SubexponentialSAT_SubexpConvolutionAlgebra`, `SubexponentialSAT_SubexpConvolutionControl`, `SubexponentialSAT_SubexpConvolutionStore`, `SubexponentialSAT_SubexpEnumerationProgram`, `SubexponentialSAT_SubexpGuardProgram`, `SubexponentialSAT_SubexpLocalCRTSetup`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_SubexpPolynomialIterationControl`, `SubexponentialSAT_Subexp_BlockCopyProgram`, `SubexponentialSAT_Subexp_PackingLeftovers`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S004` and `OAIQ081S005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S048`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S063`, `OAIQ081S064` and `OAIQ081S065`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S004
import Definitions.Def_OAIQ081S005

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Lift any fixed structured command by compiling and calling its finite
instruction table. The extra source instruction is its final return. -/
abbrev liftCommand {r s R S : ℕ} (c : Cmd r s) (inputStack outputStack : Fin s)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram (compiled c inputStack outputStack) register stack)

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls

abbrev Data := State 16 256

def afterClear (d : Data) (src : Fin 256) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

/-- Proof-level state embedding; the executable code uses fixed numeric ports. -/
noncomputable def buffers (base : Store) (w : Buffers) : Store :=
  Function.extend bufferPorts w base

@[simp] theorem buffers_port (base : Store) (w : Buffers) (i : Fin 11) :
    buffers base w (bufferPorts i) = w i := bufferPorts.injective.extend_apply _ _ _

@[simp] theorem buffers_100 (base : Store) (w : Buffers) : buffers base w 100 = w 0 := buffers_port base w 0
@[simp] theorem buffers_101 (base : Store) (w : Buffers) : buffers base w 101 = w 1 := buffers_port base w 1
@[simp] theorem buffers_102 (base : Store) (w : Buffers) : buffers base w 102 = w 2 := buffers_port base w 2
@[simp] theorem buffers_103 (base : Store) (w : Buffers) : buffers base w 103 = w 3 := buffers_port base w 3
@[simp] theorem buffers_105 (base : Store) (w : Buffers) : buffers base w 105 = w 4 := buffers_port base w 4
@[simp] theorem buffers_106 (base : Store) (w : Buffers) : buffers base w 106 = w 5 := buffers_port base w 5
@[simp] theorem buffers_108 (base : Store) (w : Buffers) : buffers base w 108 = w 6 := buffers_port base w 6
@[simp] theorem buffers_109 (base : Store) (w : Buffers) : buffers base w 109 = w 7 := buffers_port base w 7
@[simp] theorem buffers_110 (base : Store) (w : Buffers) : buffers base w 110 = w 8 := buffers_port base w 8
@[simp] theorem buffers_198 (base : Store) (w : Buffers) : buffers base w 198 = w 9 := buffers_port base w 9
@[simp] theorem buffers_199 (base : Store) (w : Buffers) : buffers base w 199 = w 10 := buffers_port base w 10

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialIterationControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev ready {S : Type*} (base : Store) (encode : S → List Bool) (a : S)
    (counter : List Bool) : Store :=
  Function.update (Function.update base 240 (encode a)) 246 counter

end SubexponentialSAT.SubexpPolynomialIterationControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramLoops
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem lowFrame_refl (s : Store) : LowFrame s s := fun _ _ => rfl

theorem lowFrame_trans {a b c : Store} (hab : LowFrame a b) (hbc : LowFrame b c) :
    LowFrame a c := fun i hi => (hbc i hi).trans (hab i hi)

theorem lowFrame_update {base s : Store} (h : LowFrame base s)
    (i : Fin 256) (hi : 205 ≤ i.val) (v : List Bool) :
    LowFrame base (Function.update s i v) := by
  intro j hj
  have hji : j ≠ i := by intro he; subst j; omega
  simpa [hji] using h j hj

abbrev loopReady {C : Type*} (base : Store) (encode : C → List Bool)
    (a : C) (counter : List Bool) : Store :=
  SubexpPolynomialIterationControl.ready base encode a counter

theorem lowFrame_loopReady {C : Type*} (base : Store) (encode : C → List Bool)
    (a : C) (counter : List Bool) : LowFrame base (loopReady base encode a counter) :=
  lowFrame_update (lowFrame_update (lowFrame_refl base) 240 (by decide) _) 246 (by decide) _

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockCopyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for copying a local table into every block

Stack 0 contains the encoded local table, stack 1 the output suffix, stack 2
is empty scratch, and stack 3 contains the unary number of blocks.  The same
finite program handles all table lengths and block counts.  It preserves the
local table and prefixes one copy per block to the output.  This is the compact
block-major representation of the repeated local basis/complement arrays;
scattering their coordinates through the packing is a separate operation.
-/

namespace SubexponentialSAT.Subexp.BlockCopyProgram

open BitProgram StructuredCalls StackRoutines

abbrev popCount : Cmd 3 4 := .base (.atom (.pop 3 0 2))

abbrev copyTable : Cmd 3 4 := .call (copyProgram 0 1 2 (0 : Fin 3) 1)

abbrev body : Cmd 3 4 := .seq copyTable popCount

abbrev loop : Cmd 3 4 := .while 2 body

abbrev command : Cmd 3 4 := .seq popCount loop

/-- Twelve control labels, independent of the runtime block count/table size. -/
abbrev program : Program 3 4 (size command + 1) := compiled command 0 1

@[simp] theorem program_labels : size command + 1 = 12 := rfl

end SubexponentialSAT.Subexp.BlockCopyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalCRTSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual cache initialization for one local CRT correction. The zero and
one arrays are physically built from scalar cells and the runtime dimension;
the complete node stream and unary skip index are then copied into work.
-/

namespace SubexponentialSAT.SubexpLocalCRTSetup

open BitProgram StructuredCalls SubexpConvolutionControl

def cleared : List (Fin 256) → Store → Store
  | [], s => s
  | i :: rest, s => cleared rest (Function.update s i [])

theorem cleared_apply (slots : List (Fin 256)) (s : Store) (j : Fin 256) :
    cleared slots s j = if j ∈ slots then [] else s j := by
  induction slots generalizing s with
  | nil => simp [cleared]
  | cons i rest ih =>
      rw [cleared, ih]
      by_cases hi : j = i <;> by_cases hr : j ∈ rest <;>
        simp [hi, hr ]

end SubexponentialSAT.SubexpLocalCRTSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def seedState {C : Type*} (s : Store) (encode : C → List Bool) (a b : C) : Store :=
  Function.update (Function.update (Function.update s 240 (encode b)) 241 (encode a))
    208 (encode b)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverseTrace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def defectState {C : Type*} (s : Store) (encode : C → List Bool) (z one : C) : Store :=
  Function.update (Function.update (Function.update s 240 (encode z)) 241 (encode one))
    222 (encode z)

def repairState {C : Type*} (s : Store) (encode : C → List Bool) (value : C) : Store :=
  SubexpLocalCRTSetup.cleared [220,222,240,241] (Function.update s 208 (encode value))

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed native binary calls at arbitrary persistent ports. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

instance instDecidableCachePort (i : Fin 256) : Decidable (CachePort i) := by
  unfold CachePort
  infer_instance

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact initialization and scan-state bridges for the native local CRT
controller. Only finite stack programs occur in these statements. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def initializedLocal (s : Store) (one : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update s 240 one)
    215 (s 214)) 217 (s 216)) 229 [true]

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def preparedLocal (s : Store) (factor one inverse negInverse zero : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update s 240 []) 223 factor) 227 inverse) 228 negInverse) 220 one) 242 zero

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def localUpdate {C P : Type*} (cm ca : C → C → C) (pm : P → P → P)
    (linear : C → P) (theta minusOne : C) (J : ℕ) (acc : P) (c : C) : P :=
  (fun p => pm p (linear (differenceValue cm ca theta c minusOne)))^[J] acc

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native five-pop decoder for the scalar frames emitted by code search.
It consumes one frame and exposes its two little-endian scalar bits. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev command : Cmd 4 1 :=
  .seq (.base (.atom (.pop 0 0 1)))
    (.seq (.base (.atom (.pop 0 2 1)))
      (.seq (.base (.atom (.pop 0 0 1)))
        (.seq (.base (.atom (.pop 0 3 1))) (.base (.atom (.pop 0 0 1))))))

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native operations for adding a Cayley shift to a vertex word.
The Boolean mode chooses left or right incidence; shift frames are consumed
on both sides so each iteration advances exactly one local port. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev pop : Cmd 8 4 := .base (.atom (.pop 1 4 5))

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlots
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse local-slot specifications. A row lists at most D original clause
indices, including any zero coefficients; shortening only removes slots whose
actual shifted edge index lies outside the original m coordinates. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

/-- Forward payload inside an outer row frame. The standard frame reader
returns its reversal, exactly the raw tuple ABI expected by the materializer. -/
def rowPayload (b m : ℕ) (ss : List (Fin m × SparseCode.F3)) : List Bool :=
  (ss.map fun s => SubexpLiftRing.fixedBits b (s.1.val+m*s.2.val)).flatten

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

def rowRecords {m : ℕ} (b : ℕ) (rs : List (List (Fin m × SparseCode.F3))) : List Bool :=
  rs.flatMap fun row => true::Encoding.frame (rowPayload b m row)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SubexponentialSAT.BinaryArithmetic

@[simp] theorem vertexBits_length {r : ℕ} (v : Cayley.Cube r) :
    (vertexBits v).length=r := List.length_ofFn

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs for the growing packing parameters

Numbers are little-endian Boolean stacks, with leading zeroes allowed. The
programs below manipulate only bits and stacks; natural-number quantities in
their specifications and cost bounds are not machine registers.
-/

namespace SubexponentialSAT.SubexpParameterProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.CounterPrograms

/-- Straight-line syntax for a fixed list of primitive operations. -/
def atoms {r s : ℕ} : List (StructuredProgram.Atom r s) → StructuredProgram.Cmd r s
  | [] => .skip
  | op :: ops => .seq (.atom op) (atoms ops)

/-! ## Consume a most-significant zero prefix and the leading one -/

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramLog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The extension-degree operation is a fixed instruction table, working on
arbitrary padded binary input. The zero case is guarded separately. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev resetLog : Cmd 3 3 := .base (SubexpParameterProgram.atoms
  [.set 0 false, .set 1 false, .set 2 false])

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
open CRTLocalProgram (LowFrame )

def initialNative (base : Store) (x y : List Bool) : Fin 32 → List Bool :=
  nativeStacks (base 194) (base 202) (base 203) (base 201) [] x y (base 204)

def finalNative (base : Store) (out : List Bool) : Fin 32 → List Bool :=
  nativeStacks (base 194) (base 202) (base 203) (base 201) out [] [] []

def Ready (base : Store) : Prop :=
  base 120 = [] ∧ ∀ i, base (ports i) = finalNative base [] i

def callResult (s : Store) (out : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    136 []) 137 []) 139 []) 128 out

theorem ports_low (i : Fin 32) : (ports i).val < 205 := by
  fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed-control dynamic coefficient loader

The source contains a flat vector. A preserved unary width word determines
how many bits are removed. Exactly that many bits are prefixed, in their
original order, to the destination. Control size is independent of both the
width and the number of coefficients.
-/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines

def loadState (regs : Fin 2 → Bool) (src dst width count scratch : List Bool) : State 2 5 :=
  ⟨regs, loadTapes src dst width count scratch⟩

theorem load_copy_stacks (src dst width : List Bool) :
    copyStacks (2 : Fin 5) 3 (loadTapes src dst width [] []) =
      loadTapes src dst width width [] := by
  funext i
  fin_cases i <;> simp [copyStacks, loadTapes]

theorem load_finish_stacks (word tail dst width : List Bool) :
    transferStacks (4 : Fin 5) 1 (loadTapes tail dst width [] word.reverse) =
      loadTapes tail (word ++ dst) width [] [] := by
  funext i
  fin_cases i <;> simp [transferStacks, loadTapes]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar addition inside a flat, runtime-sized coefficient scan. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def addState (regs : Fin 8 → Bool) (modulus left right xs ys out count width : List Bool) :
    State 8 15 := ⟨regs, addTapes modulus left right xs ys out count width⟩

theorem loadRegisters_injective : Function.Injective loadRegisters := by decide
theorem loadXStacks_injective : Function.Injective loadXStacks := by decide
theorem loadYStacks_injective : Function.Injective loadYStacks := by decide

theorem reset_two (v pr : Bool) :
    readRegs (![v, pr] : Fin 2 → Bool) 0 1 none = ![false, false] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem update_false_regs (regs : Fin 8 → Bool) :
    Function.update (Function.update regs 1 false) 3 false = readRegs regs 1 3 none := rfl

theorem scalarStacks_injective : Function.Injective scalarStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 15 => x.val) h)

abbrev emitReverse : Cmd 8 15 := .call (transferProgram 0 10 1 3)

theorem emit_stacks (modulus word xs ys out count width : List Bool) :
    transferStacks (0 : Fin 15) 10 (addTapes modulus word [] xs ys out count width) =
      addTapes modulus [] [] xs ys (word.reverse ++ out) count width := by
  funext i
  by_cases h0 : i = 0
  · subst i; simp [transferStacks, addTapes]
  · by_cases h10 : i = 10
    · subst i; simp [transferStacks, addTapes]
    · simp [transferStacks, addTapes, h0, h10]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAddLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The vector length is a unary input, never a generated list of instructions. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev popCount : Cmd 8 15 := .base (.atom (.pop 11 1 3))


abbrev finishAdd : Cmd 8 15 := .call (transferProgram 10 0 1 3)

theorem finish_stacks (modulus out width : List Bool) :
    transferStacks (10 : Fin 15) 0 (addTapes modulus [] [] [] [] out [] width) =
      addTapes modulus out.reverse [] [] [] [] [] width := by
  funext i
  by_cases h0 : i = 0
  · subst i; simp [transferStacks, addTapes]
  · by_cases h10 : i = 10
    · subst i; simp [transferStacks, addTapes]
    · simp [transferStacks, addTapes, h0, h10]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTriple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native three-scalar product and accumulator step. Triples are serialized
as consecutive fixed-width words; both width and triple count remain data. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem loadHeadStacks_injective : Function.Injective loadHeadStacks := by decide

abbrev restoreAccumulator : Cmd 8 15 := .call (transferProgram 10 1 1 3)

theorem restore_stacks (modulus term xs ys saved count width : List Bool) :
    transferStacks (10 : Fin 15) 1 (addTapes modulus term [] xs ys saved count width) =
      addTapes modulus term saved.reverse xs ys [] count width := by
  funext i
  by_cases h1 : i = 1
  · subst i; simp [transferStacks, addTapes]
  · by_cases h10 : i = 10
    · subst i; simp [transferStacks, addTapes]
    · simp [transferStacks, addTapes, h1, h10]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed outer loop contracts a runtime-sized sequence of triple blocks. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def contractState (regs : Fin 8 → Bool)
    (modulus left stream count width outer inner zero out : List Bool) : State 8 20 :=
  ⟨regs, contractTapes modulus left stream count width outer inner zero out⟩

theorem contractLower_injective : Function.Injective contractLower := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 20 => x.val) h)

abbrev contractCopyCount : Cmd 8 20 := .call (copyProgram 16 11 19 1 3)
abbrev contractCopyZero : Cmd 8 20 := .call (copyProgram 17 0 19 1 3)
abbrev contractEmit : Cmd 8 20 := .call (transferProgram 0 18 1 3)

theorem copy_count_stacks (modulus stream width outer inner zero out : List Bool) :
    copyStacks (16 : Fin 20) 11
      (contractTapes modulus [] stream [] width outer inner zero out) =
    contractTapes modulus [] stream inner width outer inner zero out := by
  funext i; fin_cases i <;> simp [copyStacks, contractTapes]

theorem copy_zero_stacks (modulus stream count width outer inner zero out : List Bool) :
    copyStacks (17 : Fin 20) 0
      (contractTapes modulus [] stream count width outer inner zero out) =
    contractTapes modulus zero stream count width outer inner zero out := by
  funext i; fin_cases i <;> simp [copyStacks, contractTapes]

theorem contract_emit_stacks (modulus word stream width outer inner zero out : List Bool) :
    transferStacks (0 : Fin 20) 18
      (contractTapes modulus word stream [] width outer inner zero out) =
    contractTapes modulus [] stream [] width outer inner zero (word.reverse ++ out) := by
  funext i; fin_cases i <;> simp [transferStacks, contractTapes]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContractLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native whole-vector contraction, with both dimensions held on data tapes. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev contractPop : Cmd 8 20 := .base (.atom (.pop 15 1 3))

abbrev contractFinish : Cmd 8 20 := .call (transferProgram 18 0 1 3)

theorem contract_finish_stacks (modulus stream width inner zero out : List Bool) :
    transferStacks (18 : Fin 20) 0 (contractTapes modulus [] stream [] width [] inner zero out) =
    contractTapes modulus out.reverse stream [] width [] inner zero [] := by
  funext i; fin_cases i <;> simp [transferStacks, contractTapes]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native loop produces a unary square from a unary input. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines

abbrev countState (regs : Fin 2 → Bool) (source counter out : List Bool) : State 2 4 :=
  ⟨regs, countTapes source counter out⟩

abbrev countCopy : Cmd 2 4 := .call (copyProgram 0 2 3 0 1)
abbrev countInit : Cmd 2 4 := .call (copyProgram 0 1 3 0 1)
abbrev countPop : Cmd 2 4 := .base (.atom (.pop 1 0 1))
abbrev countLoop : Cmd 2 4 := .while 1 (.seq countCopy countPop)
abbrev countScan : Cmd 2 4 := .seq countPop countLoop
abbrev countSquare : Cmd 2 4 := .seq countInit countScan

theorem count_copy_stacks (source counter out : List Bool) :
    copyStacks (0 : Fin 4) 2 (countTapes source counter out) =
      countTapes source counter (source ++ out) := by
  funext i; fin_cases i <;> simp [copyStacks, countTapes]

theorem count_init_stacks (source out : List Bool) :
    copyStacks (0 : Fin 4) 1 (countTapes source [] out) = countTapes source source out := by
  funext i; fin_cases i <;> simp [copyStacks, countTapes]

abbrev countSquareProgram : Program 2 4 (size countSquare+1) := compiled countSquare 0 2

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port primitives for dynamic Cartesian triple expansion. All loop
bounds and coefficient widths are words on stacks, not generated code. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev Data := State 2 16

def state (regs : Fin 2 → Bool) (s : Store) : Data := ⟨regs, tapes s⟩

abbrev copy (src dst : Fin 16) : Cmd 2 16 := .call (copyProgram src dst 15 0 1)
abbrev transfer (src dst : Fin 16) : Cmd 2 16 := .call (transferProgram src dst 0 1)

def afterClear (d : Data) (dst : Fin 16) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks dst d.stacks⟩
def afterCopy (d : Data) (src dst : Fin 16) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩
def afterTransfer (d : Data) (src dst : Fin 16) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

theorem loadPorts_injective (which : Fin 3) : Function.Injective (loadPorts which) := by
  fin_cases which <;> decide

def afterLoad (d : Data) (which : Fin 3) (word tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks (loadPorts which 0) tail)
      (loadPorts which 1) (word ++ d.stacks (loadPorts which 1))⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

def leftBits {B : ℕ} : List (Word B × Word B) → List Bool
  | [] => []
  | p :: ps => p.1.val ++ leftBits ps

def rightBits {B : ℕ} : List (Word B × Word B) → List Bool
  | [] => []
  | p :: ps => p.2.val ++ rightBits ps

def rowBits {B : ℕ} (x : List Bool) : List (Word B × Word B) → List Bool
  | [] => []
  | p :: ps => (x ++ p.1.val ++ p.2.val) ++ rowBits x ps

theorem leftBits_length {B : ℕ} (ps : List (Word B × Word B)) :
    (leftBits ps).length = ps.length * B := by
  induction ps with
  | nil => simp [leftBits]
  | cons p ps ih =>
      simp only [leftBits, List.length_append, ih, List.length_cons, Nat.add_mul]
      rw [p.1.property]
      omega

abbrev popJ : Cmd 2 16 := .base (.atom (.pop 12 0 1))

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

abbrev Row (B : ℕ) := Word B × List (Word B × Word B)

def xBits {B : ℕ} : List (Row B) → List Bool
  | [] => []
  | r :: rs => r.1.val ++ xBits rs

def tableBits {B : ℕ} : List (Row B) → List Bool
  | [] => []
  | r :: rs => rightBits r.2 ++ tableBits rs

def matrixBits {B : ℕ} : List (Row B) → List Bool
  | [] => []
  | r :: rs => rowBits r.1.val r.2 ++ matrixBits rs

def RowsFit {B : ℕ} (s : Store) (rows : List (Row B)) : Prop :=
  ∀ r ∈ rows, leftBits r.2 = s.y ∧ s.degree.length = r.2.length

abbrev popI : Cmd 2 16 := .base (.atom (.pop 11 0 1))

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleExpand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem xBits_length {B : ℕ} (rows : List (Row B)) :
    (xBits rows).length = rows.length * B := by
  induction rows with
  | nil => simp [xBits]
  | cons r rows ih =>
      simp only [xBits, List.length_append, ih, List.length_cons]
      rw [r.1.property]
      ring

abbrev startMatrix : Cmd 2 16 := .seq (copy 0 4) (copy 9 11)

def MatrixFits {B : ℕ} (s : Store) (rows : List (Row B)) : Prop :=
  xBits rows = s.x ∧ s.degree.length = rows.length ∧ RowsFit s rows

abbrev allTableBits {B : ℕ} : List (List (Row B)) → List Bool
  | [] => []
  | a :: rest => tableBits a ++ allTableBits rest

abbrev allTripleBits {B : ℕ} : List (List (Row B)) → List Bool
  | [] => []
  | a :: rest => matrixBits a ++ allTripleBits rest

abbrev popK : Cmd 2 16 := .base (.atom (.pop 10 0 1))

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem rowBits_length {B : ℕ} (x : List Bool) (pairs : List (Word B × Word B)) :
    (rowBits x pairs).length = pairs.length * (x.length + 2 * B) := by
  induction pairs with
  | nil => simp [rowBits]
  | cons p pairs ih =>
      simp [rowBits, ih, p.1.property, p.2.property]
      ring

theorem matrixBits_length {B : ℕ} (s : Store) (rows : List (Row B))
    (hfit : RowsFit s rows) :
    (matrixBits rows).length = rows.length * (3 * B * s.degree.length) := by
  induction rows with
  | nil => simp [matrixBits]
  | cons r rows ih =>
    have hr := (hfit r (by simp)).2
    have hrest : RowsFit s rows := fun a ha => hfit a (by simp [ha])
    simp only [matrixBits, List.length_append, rowBits_length, r.1.property,
      ih hrest, List.length_cons, ← hr]
    ring

theorem allTripleBits_length {B : ℕ} (s : Store) (matrices : List (List (Row B)))
    (hfit : ∀ a ∈ matrices, MatrixFits s a) :
    (allTripleBits matrices).length = matrices.length * (3 * B * s.degree.length^2) := by
  induction matrices with
  | nil => simp [allTripleBits]
  | cons a matrices ih =>
    have ha := hfit a (by simp)
    have hrest : ∀ a ∈ matrices, MatrixFits s a := fun a h => hfit a (by simp [h])
    simp only [allTripleBits, List.length_append, matrixBits_length s a ha.2.2,
      ← ha.2.1, ih hrest, List.length_cons]
    ring

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The input/output of the dynamic expander is exactly the k-major table and
triple stream used by the native ring contraction. `List.ofFn` below describes
the serialized input and theorem; the fixed program builds the repeated stream
by actual counted loops and paid source copies. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

theorem allTableBits_map {B : ℕ} (ms : List (List (Row B))) :
    allTableBits ms = (ms.map tableBits).flatten := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [allTableBits, List.map_cons, List.flatten_cons, ih]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native coefficient-ring ABI. All service programs have fixed size. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def serviceWorkState (regs : Fin 8 → Bool) (s : ServiceStore) : State 8 32 :=
  ⟨regs, serviceTapes s⟩

def serviceState (regs : Fin 8 → Bool)
    (modulus result x y degree width zero table : List Bool) : State 8 32 :=
  serviceWorkState regs ⟨modulus, result, x, y, degree, width, zero, table, [], [], [], [], []⟩

abbrev serviceCopy (src dst : Fin 32) : Cmd 8 32 := .call (copyProgram src dst 31 1 3)
abbrev serviceTransfer (src dst : Fin 32) : Cmd 8 32 := .call (transferProgram src dst 1 3)

def serviceAfterCopy (s : State 8 32) (src dst : Fin 32) : State 8 32 :=
  ⟨readRegs s.regs 1 3 none, copyStacks src dst s.stacks⟩
def serviceAfterClear (s : State 8 32) (dst : Fin 32) : State 8 32 :=
  ⟨readRegs s.regs 1 3 none, clearStacks dst s.stacks⟩
def serviceAfterTransfer (s : State 8 32) (src dst : Fin 32) : State 8 32 :=
  ⟨readRegs s.regs 1 3 none, transferStacks src dst s.stacks⟩

abbrev servicePrepare : Cmd 8 32 := serviceCopy 22 20

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem serviceAddPorts_injective : Function.Injective serviceAddPorts := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 32 => x.val) h)

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceLifts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem serviceExpandPorts_injective : Function.Injective serviceExpandPorts := by decide
theorem serviceCountPorts_injective : Function.Injective serviceCountPorts := by decide
theorem serviceContractPorts_injective : Function.Injective serviceContractPorts := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 32 => x.val) h)

abbrev serviceCount : Cmd 8 32 := .call
  (ProgramLinking.liftProgram countSquareProgram loadRegisters serviceCountPorts)


end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native service for arbitrary-degree coefficient-ring products. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev serviceDegree : Cmd 8 32 := serviceTransfer 11 15

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete binary guard control for the subexponential schedule

The comparator below has a fixed instruction table, reads arbitrary-width
little-endian binary words, and uses only Boolean operations and stack pops.
Schedule arithmetic is not an instruction of this program.
-/

namespace SubexponentialSAT.SubexpGuardProgram

open BitProgram BinaryArithmetic

namespace Compare

/-- Eight one-bit registers, two stacks, and twelve fixed labels. Register zero
is the result; both operand stacks are consumed. Entry resets the borrow bit. -/
abbrev program : Program 8 2 12 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .pop 0 1 3 2
    | 2 => .pop 1 2 4 3
    | 3 => .bor 5 3 4 4
    | 4 => .branch 5 5 11
    | 5 => .bnot 6 1 6
    | 6 => .band 6 6 2 7
    | 7 => .bxor 7 1 2 8
    | 8 => .bnot 7 7 9
    | 9 => .band 7 7 0 10
    | 10 => .bor 0 6 7 1
    | _ => .halt

end Compare

open StructuredProgram


end SubexponentialSAT.SubexpGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Guard

open BitProgram StructuredCalls

def squarePorts : ArithmeticCalls.Ports 12 where
  left := 0
  right := 0
  out := 3
  work := work
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i h; have hval : i.val + 6 = 0 := congrArg Fin.val h; omega
  work_ne_right := by intro i h; have hval : i.val + 6 = 0 := congrArg Fin.val h; omega
  work_ne_out := by intro i h; have hval : i.val + 6 = 3 := congrArg Fin.val h; omega

def productPorts : ArithmeticCalls.Ports 12 where
  left := 3
  right := 1
  out := 4
  work := work
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i h; have hval : i.val + 6 = 3 := congrArg Fin.val h; omega
  work_ne_right := by intro i h; have hval : i.val + 6 = 1 := congrArg Fin.val h; omega
  work_ne_out := by intro i h; have hval : i.val + 6 = 4 := congrArg Fin.val h; omega

end SubexponentialSAT.SqrtLog.Setup.Guard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBlockParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual block-size and block-threshold arithmetic

The three input words contain `s`, `delta`, and `Q`.  The width `k` is part
of the fixed code.  Seven high stacks are a reusable empty work bank; the
fifteen low stacks retain inputs, constants, and computed intermediate words.
Every arithmetic operation below invokes a proved finite Boolean program.
-/

namespace SubexponentialSAT.SubexpBlockParameterProgram

open BitProgram StructuredCalls BinaryArithmetic

abbrev Data := State 8 22

end SubexponentialSAT.SubexpBlockParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial semantics of the triangular update schedule used by the
actual convolution controller. This file assigns no execution costs. -/

namespace SubexponentialSAT.SubexpConvolutionAlgebra

open Polynomial
open TruncatedConvolution

section Algebra

variable {R : Type*} [CommSemiring R]

@[simp] theorem denote_replicate_zero (D : ℕ) :
    PolynomialAlgorithm.denote (List.replicate D (0 : R)) = 0 := by
  induction D with
  | zero => rfl
  | succ D ih => simp [List.replicate_succ, ih]

end Algebra

end SubexponentialSAT.SubexpConvolutionAlgebra

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded interval enumeration by fixed finite control

A current label and a remaining count live on little-endian Boolean stacks.
The program invokes an actual body command once per label and advances using
verified finite-table increment/decrement routines.  Mathematical state
embeddings below occur only in execution proofs; no instruction evaluates an
arbitrary semantic function.
-/

namespace SubexponentialSAT.SubexpEnumerationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open SubexponentialSAT.CounterPrograms

variable {R S : ℕ}

abbrev Data := StructuredProgram.State

end SubexponentialSAT.SubexpEnumerationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

open BitProgram StructuredCalls

abbrev Code := Cmd 8 18

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end


