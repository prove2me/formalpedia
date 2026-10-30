-- Prove2me | Definitions.Def_OAIQ081S029
-- name    : OAIQ081S029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:28:09.199035+00:00
-- url     : https://prove2.me/theorems/9a9ad5bd-3bc2-4157-b230-ac1b367adc5e
-- title:
--   Definitions bundle OAIQ081S029 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 88 declarations of OpenAI's Lean: 60 definitions, 1 inductive type or structure, 2 instances and 25 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.combine`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.frames`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.arithmeticPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.chronologicalRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.coefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.index`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.matrixRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.slot`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.slots`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedSupportCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedSupportProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedSupportRoundRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordRejects`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.lessAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.supportAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.ternaryCell`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.unaryLessCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.unaryLessProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordRejects`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordTailCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.RingSetup.coreEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.RingSetup.numberEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.arithmeticBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.candidates`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.constantsBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.finalDiscard`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelect.frameAtom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelect.frameBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelect.frameCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelect.frameLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelect.frameProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.IsCodeword`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.edgeEquiv` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CodeRowsProgramCode`, `SubexponentialSAT_SqrtLog_CodeRowsProgramRows`, `SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic`, `SubexponentialSAT_SqrtLog_CodeRowsProgramSlotSemantics`, `SubexponentialSAT_SqrtLog_CodeRowsProgramSlots`, `SubexponentialSAT_SqrtLog_CodeSearchProgramCompare`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCountTail`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphWord`, `SubexponentialSAT_SqrtLog_CodeSearchProgramScan`, `SubexponentialSAT_SqrtLog_CodeSearchProgramSupport`, `SubexponentialSAT_SqrtLog_CodeSearchProgramWord`, `SubexponentialSAT_SqrtLog_CodeSearchProgramWordTail`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramArithmetic`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks`, `SubexponentialSAT_SqrtLog_CostAssemblyPolynomial`, `SubexponentialSAT_SqrtLog_CostAssemblyRingBounds`, `SubexponentialSAT_SqrtLog_CostAssemblyRingSetup`, `SubexponentialSAT_SqrtLog_CostAssemblyUniform`, `SubexponentialSAT_SqrtLog_IdempotentProgramCompleteCost`, `SubexponentialSAT_SqrtLog_IdempotentProgramMachine`, `SubexponentialSAT_SqrtLog_IrreducibleSearch`, `SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RowSelectionProgramSelectFrame`, `SubexponentialSAT_SqrtLog_SparseCodeBasic`, `SubexponentialSAT_SqrtLog_SparseCodeConstruct`, `SubexponentialSAT_SqrtLog_WalshExistenceEnumeration`, `SubexponentialSAT_SqrtLog_WalshExistenceParity`, `SubexponentialSAT_SubexpConvolutionPair`, `SubexponentialSAT_SubexpEnumerationPayload`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpLinearFactorProgram`, `SubexponentialSAT_SubexpOrderedTupleData`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpPostfixGlobal`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_MatrixProgram`, `SubexponentialSAT_Subexp_MatrixVectorProgram`, `SubexponentialSAT_Subexp_MatrixWordEncoding`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S004`, `OAIQ081S005`, `OAIQ081S006` and `OAIQ081S007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062`, `OAIQ081S063`, `OAIQ081S064` and `OAIQ081S065`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_nativeEnvelope_bound`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_nativeEnvelope_bound`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S004
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

theorem cartesianOutput_length (tuples alphabet : Records) :
    (cartesianOutput tuples alphabet).length = tuples.length * alphabet.length := by
  simp only [cartesianOutput, List.length_reverse]
  induction tuples with
  | nil => simp
  | cons tuple tuples ih => simp [ih, Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationPayload
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed machine emitting the encoded increment schedule

The input contains the actual one-pass increment payload and the unary number
of outer basepoints.  `BlockCopyProgram.program` preserves that payload and
emits one copy for each outer basepoint.  The payloads below are computed from
the supplied vector arrays, and their lengths follow from the proved coset
cardinalities rather than from numerical premises about execution.

This is the increment schedule used by the separate color sums.  It does not
construct the basis arrays, add outer basepoints, or evaluate the summands.
The cost of preparing the input stacks remains a separate obligation.
-/

namespace SubexponentialSAT.SubexpEnumerationPayload

open scoped BigOperators

/-- The canonical little-endian binary word for an actual field element. -/
def scalarBits {p : ℕ} [Fact p.Prime] (x : ZMod p) : List Bool :=
  SubexpLiftRing.fixedBits (scalarWidth p) x.val

@[simp] theorem scalarBits_length {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    (scalarBits x).length = scalarWidth p :=
  SubexpLiftRing.fixedBits_length _ _

end SubexponentialSAT.SubexpEnumerationPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared interfaces for sparse ternary parity checks

The definitions distinguish edge coordinates from graph vertices. Parallel
edges have different ports. All construction theorems built on these interfaces
must eventually discharge the local-distance and graph-mixing hypotheses.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

section Words

variable {C R : Type*} [Fintype C]

def IsCodeword (Q : CheckMatrix R C) (w : C → F3) : Prop :=
  ∀ r, check Q w r = 0

end Words

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed eight-label program counts nonzero two-bit cells. The input is
consumed and the count is emitted in unary. This is an actual support counter,
not a unit-cost application of `List.countP`. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram
open scoped BigOperators

def ternaryCell (x : SparseCode.F3) : Bool × Bool :=
  (decide (x = 1), decide (x = 2))

abbrev framedSupportProgram : Program 4 2 11 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 2 1 1, .branch 1 2 10, .pop 0 0 1 3,
    .pop 0 2 1 4, .pop 0 2 1 5, .pop 0 3 1 6,
    .bor 0 0 2 7, .branch 0 8 0, .set 3 true 9, .push 1 3 0, .halt]

def framedSupportCfg (pc : Option (Fin 11)) (regs : Fin 4 → Bool)
    (input output : List Bool) : Cfg 4 2 11 :=
  ⟨pc, regs, ![input, output]⟩

def framedSupportRoundRegs (regs : Fin 4 → Bool) (a b : Bool) : Fin 4 → Bool :=
  let r := readRegs (readRegs (readRegs (readRegs (readRegs regs
    2 1 (some true)) 0 1 (some a)) 2 1 (some true)) 2 1 (some b)) 3 1 (some false)
  let r := Function.update r 0 (a || b)
  if a || b then Function.update r 3 true else r

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed encoded modular dot products

Vectors are streams of framed, fixed-width little-endian scalar words. The
loop reads the two streams itself and calls the measured multiply-add routine.
Its finite control is independent of the modulus, width, and vector length.
-/

namespace SubexponentialSAT.Subexp.MatrixProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixScalarProgram

abbrev peekLeft : Cmd 8 16 := .base (.atom (.peek 10 0 1))

end SubexponentialSAT.Subexp.MatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixVectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixScalarProgram MatrixProgram

abbrev popRow : Cmd 8 16 := .base (.atom (.pop 15 0 1))

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixWordEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical prime-field words for the local matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixWordEncoding

open BinaryArithmetic SubexpLiftRing

variable (p : ℕ) [Fact p.Prime]

def width : ℕ := baseWidth p 1

/-- The same fixed-bit encoding as `encodeBase` with exponent one, written
directly over `ZMod p` to avoid casts in the basis-checker interface. -/
def word (a : ZMod p) : List Bool := fixedBits (width p) a.val

omit [Fact p.Prime] in
@[simp] theorem word_length (a : ZMod p) : (word p a).length = width p :=
  fixedBits_length _ _

def modulus : List Bool := fixedBits (width p + 1) p

omit [Fact p.Prime] in
@[simp] theorem modulus_length : (modulus p).length = width p + 1 := fixedBits_length _ _

def zero : List Bool := word p 0

@[simp] theorem zero_length : (zero p).length = width p := word_length p 0

end SubexponentialSAT.Subexp.MatrixWordEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def frames (bits : List Bool) : List Bool := bits.flatMap fun b => Cell.frame b false

abbrev combine : Cmd 8 4 :=
  .ite 7 (.base (.atom (.bxor 4 4 2))) (.base (.atom (.copy 4 4)))

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramSelectFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed framing primitive for the scored-record writer. It consumes the
input bits and prepends the frame of their reversal to the output stack. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev frameAtom (a : StructuredProgram.Atom 3 2) : Cmd 3 2 := .base (.atom a)

abbrev frameBody : Cmd 3 2 :=
  .seq (frameAtom (.push 1 0))
    (.seq (frameAtom (.push 1 2)) (frameAtom (.pop 0 0 1)))

abbrev frameLoop : Cmd 3 2 := .while 1 frameBody

abbrev frameCommand : Cmd 3 2 :=
  .seq (frameAtom (.set 2 false))
    (.seq (frameAtom (.push 1 2))
      (.seq (frameAtom (.set 2 true))
        (.seq (frameAtom (.pop 0 0 1)) frameLoop)))

abbrev frameProgram := compiled frameCommand 0 1

end SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

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

@[simp] theorem update_triple_zero {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_one {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_two {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> simp [triple]

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixGlobal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared-machine port adapter for the concrete postfix interpreter

The shared machine uses code/depth/operand/scratch stacks 26/28/27/29.
A fixed permutation installs the proved interpreter there while accepting
arithmetic service tables already written for the shared 16-register,
128-stack machine. Port renaming adds no machine transitions.
-/

namespace SubexponentialSAT.SubexpPostfixGlobal

open BitProgram

/-- Reindex physical stacks without changing their contents or control state. -/
def reindexCfg {r s l : ℕ} (e : Equiv.Perm (Fin s)) (c : Cfg r s l) : Cfg r s l where
  pc := c.pc
  regs := c.regs
  «stacks» := fun i => c.stacks (e.symm i)

@[simp] theorem reindexCfg_symm {r s l : ℕ} (e : Equiv.Perm (Fin s)) (c : Cfg r s l) :
    reindexCfg e.symm (reindexCfg e c) = c := by
  cases c
  simp [reindexCfg]

end SubexponentialSAT.SubexpPostfixGlobal

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

abbrev registers (v p op : Bool) : Fin 16 → Bool :=
  Fin.addCases (motive := fun _ : Fin (3 + 13) => Bool)
    (triple v p op) (fun _ : Fin 13 => false)

@[simp] theorem registers_zero (v p op : Bool) : registers v p op 0 = v := rfl
@[simp] theorem registers_one (v p op : Bool) : registers v p op 1 = p := rfl
@[simp] theorem registers_two (v p op : Bool) : registers v p op 2 = op := rfl

open SubexpPostfixGlobal

/-! ## Entry from arbitrary caller registers -/

end SubexponentialSAT.SubexpEvaluationProgram

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

def arithmeticPorts (i : Fin 3) : ArithmeticCalls.Ports 64 where
  left := ![18,20,21] i
  right := ![3,14,22] i
  out := ![20,21,23] i
  work := arithmeticWork
  out_ne_left := by fin_cases i <;> decide
  out_ne_right := by fin_cases i <;> decide
  work_ne_left := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_right := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_out := by intro j; fin_cases i <;> fin_cases j <;> decide

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistenceEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable binary indexing for Cayley vertices. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

/-- Explicit radix-two decoding. Both directions are computable; in particular
this does not use `Fintype.equivFin`. -/
def cubeEquiv (r : ℕ) : Fin (2 ^ r) ≃ Cube r :=
  (@finFunctionFinEquiv 2 r).symm

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeConstruct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit sparse parity-check constructor

Every choice below is executable: two finite searches, arithmetic index
equivalences, and restriction to the first input columns. The hypotheses of
the local-code and Walsh existence lemmas are discharged by the parameter
bounds. No code or expander is supplied as an assumption to the final rows.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

def edgeEquiv (r D : ℕ) : Fin (2 ^ r * D) ≃ Cayley.Cube r × Fin D :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (WalshExistence.cubeEquiv r) (Equiv.refl (Fin D)))

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlots
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def index (shifts : Fin D → Cayley.Cube r) (side : Bool) (v : Cayley.Cube r)
    (p : Fin D) : Fin (2^r*D) := (SparseCode.edgeEquiv r D).symm (edge shifts side v p)

def slot (m : ℕ) (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (side : Bool) (v : Cayley.Cube r) (a : Fin t) (p : Fin D) :
    Option (Fin m × SparseCode.F3) :=
  if h : (index shifts side v p).val < m then some (⟨(index shifts side v p).val,h⟩,Q a p)
  else none

def slots (m : ℕ) (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (side : Bool) (v : Cayley.Cube r) (a : Fin t) : List (Fin m × SparseCode.F3) :=
  (List.finRange D).filterMap (slot m shifts Q side v a)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlotSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

def coefficient (ss : List (Fin m × SparseCode.F3)) (c : Fin m) : SparseCode.F3 :=
  (ss.map fun s => if s.1=c then s.2 else 0).sum

def matrixRow (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    (Cayley.Cube r × Fin t) ⊕ (Cayley.Cube r × Fin t) :=
  if side then Sum.inr (v,a) else Sum.inl (v,a)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The precise order emitted by the native vertex/check loops. Each row is
present even when shortening removes every one of its local ports. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

def chronologicalRows (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) : List (List (Fin m × SparseCode.F3)) :=
  (List.finRange (2^r)).flatMap fun i =>
    (List.ofFn fun a => slots m shifts Q false (WalshExistence.cubeEquiv r i) a) ++
    (List.ofFn fun a => slots m shifts Q true (WalshExistence.cubeEquiv r i) a)

def serializedRows (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) : List (List (Fin m × SparseCode.F3)) :=
  (chronologicalRows m shifts Q).reverse

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An eight-label comparison of unary counts. Only stack presence is read;
the count values never occur in the finite instruction table. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram

abbrev unaryLessProgram : Program 4 2 8 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 5, .pop 1 0 2 3,
    .branch 2 0 4, .set 3 false 7, .peek 1 0 2 6, .copy 3 2 7, .halt]

def unaryLessCfg (pc : Option (Fin 8)) (regs : Fin 4 → Bool)
    (left right : List Bool) : Cfg 4 2 8 := ⟨pc, regs, ![left,right]⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed support and unary comparison as framed subroutine calls. The port
maps are fixed finite maps; the lengths being scanned occur only on tapes. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev supportAt (input output : Fin 18) : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram framedSupportProgram scanRegisters
    (scanStacks input output))

abbrev lessAt (left right : Fin 18) : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram unaryLessProgram scanRegisters (scanStacks left right))

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCountTail
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Two physical support counters for a Walsh query. The parity count is kept
on tape9, while register7 reports whether the input character is nonzero. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

abbrev graphCountTail : Cmd 8 18 :=
  .seq (supportAt 8 9) <|
  .seq (supportAt 12 10) <|
  .seq (.base (.atom (.peek 10 0 1))) (.base (.atom (.copy 7 1)))

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistenceParity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Walsh testing using a mod-two matrix product and natural-number counters. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

def parityProducts {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) : Fin D → ZMod 2 :=
  fun i => ∑ j, s i j * a j

def parityWeight {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) : ℕ :=
  (Finset.univ.filter (fun i => parityProducts s a i ≠ 0)).card

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramWordTail
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual decision tail for a proposed low-weight kernel word. It reads
both framed vectors, compares unary support with the runtime threshold, and
sets register 7 precisely on rejection. No semantic predicate is an opcode. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

abbrev wordTailCommand : Cmd 8 18 :=
  .seq (supportAt 8 9) <|
  .seq (.base (.atom (.peek 9 0 1))) <|
  .seq (.base (.atom (.bnot 6 1))) <|
  .seq (supportAt 12 10) <|
  .seq (.base (.atom (.peek 10 0 1))) <|
  .seq (.base (.atom (.band 7 6 1))) <|
  .seq (lessAt 10 16) (.base (.atom (.band 7 7 3)))

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramWord
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A complete fixed-code test of one proposed short nonzero kernel word.
Matrix and word bytes, the row count, and the distance threshold are runtime
inputs. The protected stack 17 survives the call. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

def wordRejects {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) : Prop :=
  SparseCode.IsCodeword Q x ∧ x ≠ 0 ∧ SparseCode.weight x < d

instance instDecidableWordRejects {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) : Decidable (wordRejects Q x d) := by
  unfold wordRejects SparseCode.IsCodeword
  infer_instance

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

def ports (i : Fin 4) : Ports 14 where
  left := ![0,0,1,4] i
  right := ![1,3,5,1] i
  out := ![4,5,6,7] i
  work := work
  out_ne_left := by fin_cases i <;> decide
  out_ne_right := by fin_cases i <;> decide
  work_ne_left := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_right := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_out := by intro j; fin_cases i <;> fin_cases j <;> decide

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Code := Cmd 9 14

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphWord
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One complete Walsh query, executed by a fixed program. The inputs contain
an actual binary matrix, a binary character, and binary words for q and D.
No integer inequality is an instruction: the final comparison invokes the
count/arithmetic/guard routine with its measured bit trace. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

def graphWordRejects {r D : ℕ} (s : Fin D → Cayley.Cube r)
    (a : Cayley.Cube r) (q : ℕ) : Prop :=
  a ≠ 0 ∧ ¬CodeSearchWalshProgram.good q D (WalshExistence.parityWeight s a)

instance instDecidableGraphWordRejects {r D : ℕ} (s : Fin D → Cayley.Cube r) (a : Cayley.Cube r) (q : ℕ) :
    Decidable (graphWordRejects s a q) := by unfold graphWordRejects; infer_instance

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

theorem ordinary_pow {f : ℕ → ℕ} (hf : Ordinary f) (e : ℕ) :
    Ordinary (fun S => (f S)^e) := by
  obtain ⟨C,d,hf⟩ := hf
  refine ⟨C^e,d*e,?_⟩
  intro S
  calc
    _ ≤ (C*(S+1)^d)^e := Nat.pow_le_pow_left (hf S) e
    _ = _ := by rw [mul_pow,pow_mul]

end SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native service for arbitrary-degree coefficient-ring products. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem serviceMulBudget_le (B d : ℕ) :
    serviceMulBudget B d ≤ 40000*(d+1)^3*(B+1)^2 := by
  unfold serviceMulBudget RingTriple.expandBudget
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed four-array Newton machine. Its native services perform full dynamic
vector arithmetic, operand copying, and target replacement. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- All scans, scalar operations, register copies, and call halts are included. -/
def arithmeticBudget (B d : ℕ) : ℕ :=
  max (RingScan.serviceAddBudget B d) (RingScan.serviceMulBudget B d) +
    25*(d*B) + 7*d + 27

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

/-- A fixed polynomial bound for one complete register operation. -/
theorem arithmeticBudget_polynomial (B d : ℕ) :
    arithmeticBudget B d ≤ 41000*(d+1)^3*(B+1)^2 := by
  have hm := RingScan.serviceMulBudget_le B d
  have ha : RingScan.serviceAddBudget B d ≤ 40000*(d+1)^3*(B+1)^2 := by
    unfold RingScan.serviceAddBudget
    ring_nf
    omega
  have hx := max_le ha hm
  unfold arithmeticBudget
  calc
    _ ≤ 40000*(d+1)^3*(B+1)^2 + 25*(d*B) + 7*d + 27 := by omega
    _ ≤ _ := by ring_nf; omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramCompleteCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An explicit polynomial primitive-time envelope for native preparation
and all Newton iterations, as a function of precision and input length. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram

theorem binaryClog_le (t : ℕ) : Nat.clog 2 t ≤ t := by
  have hp : t+1 ≤ 2^t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ]
      omega
  exact (Nat.le_pow_iff_clog_le (by decide)).mp (by omega)

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable arbitrary-degree irreducible search over F₃

Search all monic degree-`d` coefficient vectors and reject each candidate
which is the product of two nonconstant arrays of degree at most `d`.
The test uses explicit convolution. Mathematical finite-field existence
proves that the executable search succeeds for every positive `d`.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

def candidates (d : ℕ) : List (Fin d → F) :=
  QuarticSearch.vectors (QuarticSearch.elements 3) d

@[simp] theorem length_candidates (d : ℕ) : (candidates d).length = 3 ^ d := by
  simp [candidates, QuarticSearch.length_vectors]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpOrderedTupleData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # Exact lexicographic tuple order for the selected quartic search -/

namespace SubexponentialSAT.SubexpOrderedTupleData

open SubexpTupleRefinement

theorem orderedCartesian_eq_reverse (rows alphabet : List (List Bool)) :
    orderedCartesian rows alphabet = (Subexp.TupleProgram.cartesianOutput rows alphabet).reverse := by
  simp [orderedCartesian, Subexp.TupleProgram.cartesianOutput]

@[simp] theorem orderedCartesian_length (rows alphabet : List (List Bool)) :
    (orderedCartesian rows alphabet).length = rows.length * alphabet.length := by
  rw [orderedCartesian_eq_reverse, List.length_reverse, Subexp.TupleProgram.cartesianOutput_length]

end SubexponentialSAT.SubexpOrderedTupleData

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

abbrev Data (S : ℕ) := State 16 S
abbrev Command (S : ℕ) := Cmd 16 S

def copyState {S : ℕ} (src dst : Fin S) (a : Data S) : Data S :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

def copyCmd {S : ℕ} (src dst tmp : Fin S) : Command S :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

@[simp] theorem copyState_stack {S : ℕ} (src dst : Fin S) (a : Data S) :
    (copyState src dst a).stacks = Function.update a.stacks dst (a.stacks src ++ a.stacks dst) := rfl

def copyMany {S : ℕ} (tmp : Fin S) : List (Fin S × Fin S) → Command S
  | [] => .base .skip
  | (src, dst) :: ps => .seq (copyCmd src dst tmp) (copyMany tmp ps)

def copyManyState {S : ℕ} : List (Fin S × Fin S) → Data S → Data S
  | [], a => a
  | (src, dst) :: ps, a => copyManyState ps (copyState src dst a)

abbrev invoke {r s l S : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (stack : Fin s → Fin S) : Command S :=
  .call (ProgramLinking.liftProgram p register stack)

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# One actual product-and-accumulate step for packed jet convolution

The global state has sixteen Boolean registers and 256 Boolean-word stacks.
The multiplier occupies the fixed high bank beginning at 128. Its result is
moved, with order preserved, to the low-bank jet-cell accumulator service.
-/

namespace SubexponentialSAT.SubexpConvolutionPair

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 256

end SubexponentialSAT.SubexpConvolutionPair

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
open BitProgram StructuredCalls

@[simp] theorem mem_workPorts (i : Fin 640) : i∈workPorts ↔ 417 ≤ i.val := by
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    change 417 ≤ 417+j.val
    omega
  · intro hi
    let j : Fin 223 := ⟨i.val-417,by omega⟩
    apply List.mem_map.mpr
    exact ⟨j,by simp,Fin.ext (by dsimp [j]; omega)⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram



namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

def constantsBudget (W B d : ℕ) : ℕ :=
  let b := constantStartPorts.length*(2*W+3)+
    3*(7*B+8+(LeafProgram.Constants.budget B d+1))
  b+constantAliases.length*(9*(W+b+2)+8)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

/-- The final cleanup produces the exact shared scalar and polynomial
contexts consumed by the existing native arithmetic programs. -/
def finalDiscard : List (Fin 640) := (195::privatePorts)++arithmeticCleanPorts

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

def numberEnvelope (S : ℕ) : ℕ :=
  (workPorts++outputPorts).length*(2*S+3)+(serializationEnvelope S+1)+
  5*(7*S+6+32*(S+1)*(S+1))+(7*S+8)+32

def coreEnvelope (S : ℕ) : ℕ :=
  scalarBudget S S+1+(7*(2*S)+8)+32+
  (3*(searchCoefficient*(S+1)^10)+7*(2*S)+S*(28*S+14)+15)+
  (7*(2*S)+8)+208000*(S+1)^5*(S+1)^2

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

theorem numberEnvelope_ordinary : Ordinary numberEnvelope := by
  unfold numberEnvelope serializationEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const (workPorts++outputPorts).length) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 3))) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 3)) (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 5))) (ordinary_mul (ordinary_const 20) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_mul (ordinary_const 20) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 3))) (ordinary_mul (ordinary_const 100) (ordinary_pow (ordinary_add (ordinary_add ordinary_id ordinary_id) (ordinary_const 1)) 2))) (ordinary_const 1))) (ordinary_mul (ordinary_const 5) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 6)) (ordinary_mul (ordinary_mul (ordinary_const 32) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add ordinary_id (ordinary_const 1)))))) (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 8))) (ordinary_const 32))

theorem coreEnvelope_ordinary : Ordinary coreEnvelope := by
  unfold coreEnvelope scalarBudget
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2001) (ordinary_pow (ordinary_add (ordinary_add ordinary_id ordinary_id) (ordinary_const 2)) 2)) (ordinary_mul (ordinary_const 500000) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 3) ordinary_id) ordinary_id) (ordinary_const 1)) 3))) (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 8))) (ordinary_const 32)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 3) (ordinary_mul (ordinary_const searchCoefficient) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 10))) (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 28) ordinary_id) (ordinary_const 14)))) (ordinary_const 15))) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 8))) (ordinary_mul (ordinary_mul (ordinary_const 208000) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 5)) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 2)))

theorem constants_ordinary {f g h : ℕ → ℕ}
    (hf : Ordinary f) (hg : Ordinary g) (hh : Ordinary h) :
    Ordinary (fun S => constantsBudget (f S) (g S) (h S)) := by
  unfold constantsBudget LeafProgram.Constants.budget
  exact (ordinary_add (ordinary_add (ordinary_mul (ordinary_const constantStartPorts.length) (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 3))) (ordinary_mul (ordinary_const 3) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) hg) (ordinary_const 8)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul hh (ordinary_add (ordinary_mul (ordinary_const 22) hg) (ordinary_const 25))) (ordinary_mul (ordinary_const 4) hg)) (ordinary_const 16)) (ordinary_const 1))))) (ordinary_mul (ordinary_const constantAliases.length) (ordinary_add (ordinary_mul (ordinary_const 9) (ordinary_add (ordinary_add hf (ordinary_add (ordinary_mul (ordinary_const constantStartPorts.length) (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 3))) (ordinary_mul (ordinary_const 3) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) hg) (ordinary_const 8)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul hh (ordinary_add (ordinary_mul (ordinary_const 22) hg) (ordinary_const 25))) (ordinary_mul (ordinary_const 4) hg)) (ordinary_const 16)) (ordinary_const 1)))))) (ordinary_const 2))) (ordinary_const 8))))

theorem idempotent_ordinary {f g : ℕ → ℕ}
    (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun S => idempotentEnvelope (f S) (g S)) := by
  unfold idempotentEnvelope IdempotentProgram.polynomialBudget
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const idempotentStartPorts.length) (ordinary_add (ordinary_mul (ordinary_const 2) hg) (ordinary_const 3))) (ordinary_add (ordinary_mul (ordinary_const 7) hg) (ordinary_const 8))) (ordinary_const 32)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 100000000) (ordinary_pow (ordinary_add (ordinary_add hf hg) (ordinary_const 2)) 4)) (ordinary_mul (ordinary_mul (ordinary_const 7) hf) (ordinary_mul (ordinary_mul (ordinary_const 41000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 3) hf) (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 1)) 2)))) (ordinary_mul (ordinary_add hf (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 16) (ordinary_add hg (ordinary_const 1))) (ordinary_const 16)))) (ordinary_const 2))) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 6) (ordinary_pow hf 2))) (ordinary_const 8)))

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyUniform
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform bounds over every input at a fixed size.  The cutoff depends only
on fixed numerical exponents, never on a chosen sequence of formulas. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly
open Filter
open scoped Topology
open Asymptotic

/-- All input-dependent premises are pointwise.  None is hidden in the
threshold used by `eventually_assembledWork_bound`. -/
structure Bounds (qi ql d n : ℕ) (p : Resources) : Prop where
  residual : p.residual ≤ n ∧ n ≤ 2*p.residual
  clauses : p.clauses ≤ n*p.initialOccurrence
  initial : p.initialOccurrence ≤ L n^qi
  occurrence : p.localOccurrence ≤ L p.residual^ql
  factors : p.factors ≤ 4*n+HashSelect.loopCap n p.clauses+2
  branch : (p.branchVars:ℝ) ≤ (n:ℝ)/Real.sqrt (L n:ℝ)
  base : 0 < p.labelBase
  rows : 16*(layoutR p.residual:ℝ)*(L p.residual:ℝ)^2*(p.labelRows:ℝ) ≤ p.residual
  height : Real.log (p.labelBase:ℝ) ≤ 4*(L p.residual:ℝ)^2
  heads : p.heads ≤ n+1
  headSize : (p.headSize:ℝ) ≤ 2*(n:ℝ)/layoutR p.residual
  setup : (p.setup:ℝ) ≤ (2:ℝ)^Statement.runtimeScale n
  ordinary : p.bits*(p.ordinary+1)^8 ≤ (n+1)^d

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed indexed traversal of the actual framed node table. The installed
worker is a real command; its measured, frame-preserving execution remains an
explicit producer obligation. Neither the index nor a jet is semantic advice. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Code := Cmd 40 768

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


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

abbrev copy (src dst : Fin 56) : Cmd 8 56 := .call (copyProgram src dst 47 0 1)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


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

open BitProgram StructuredCalls

abbrev Data := State 16 128

end SubexponentialSAT.SubexpLinearFactorProgram

end OAI.Algorithms
end


