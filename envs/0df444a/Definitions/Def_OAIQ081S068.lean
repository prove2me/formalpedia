-- Prove2me | Definitions.Def_OAIQ081S068
-- name    : OAIQ081S068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:52:28.989571+00:00
-- url     : https://prove2.me/theorems/2b03d098-2c54-450e-8539-e2255a22de6d
-- title:
--   Definitions bundle OAIQ081S068 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 74 declarations of OpenAI's Lean: 50 definitions and 24 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preReverseReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preReverseState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall.native`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.mulCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.nativeMulCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.addLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.addScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.addStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.addVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.addVectorProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.blockBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractCoordinate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractVectorProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.foldTriples`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadX`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.scalarMul`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceAdd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceAddProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceContract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceMul`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceMulProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.tripleBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.tripleLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.tripleProduct`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.tripleScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.tripleScanProgram` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse`, `SubexponentialSAT_SqrtLog_BucketProgramSignature`, `SubexponentialSAT_SqrtLog_DensePolynomialProgram`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramMul`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramPair`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramRingCall`, `SubexponentialSAT_SqrtLog_RingProgramWords`, `SubexponentialSAT_SqrtLog_RingScanAdd`, `SubexponentialSAT_SqrtLog_RingScanAddLoop`, `SubexponentialSAT_SqrtLog_RingScanContract`, `SubexponentialSAT_SqrtLog_RingScanContractLoop`, `SubexponentialSAT_SqrtLog_RingScanCount`, `SubexponentialSAT_SqrtLog_RingScanLoad`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RingScanServiceAdd`, `SubexponentialSAT_SqrtLog_RingScanServiceBasic`, `SubexponentialSAT_SqrtLog_RingScanServiceLifts`, `SubexponentialSAT_SqrtLog_RingScanTriple`, `SubexponentialSAT_SqrtLog_RingScanTripleLoop`, `SubexponentialSAT_SqrtLog_RingTripleBasic`, `SubexponentialSAT_SqrtLog_RingTripleProgram`, `SubexponentialSAT_SqrtLog_RingTripleRowStep`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_SubexpConvolutionControl`, `SubexponentialSAT_SubexpConvolutionStore`, `SubexponentialSAT_SubexpLiftRing`, `SubexponentialSAT_SubexpLocalCRTSetup`, `SubexponentialSAT_SubexpPolynomialServiceControl`, `SubexponentialSAT_SubexpPreparedQuartic`, `SubexponentialSAT_Subexp_PairScoreProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S048` and `OAIQ081S049` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S093` and `OAIQ081S094`; the statement `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run` and `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S048
import Definitions.Def_OAIQ081S049

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed EOF-controlled reversal of a raw list of framed words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev preReverseState (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : PreReverseData := ⟨regs, ![words xs,[],[],out]⟩

abbrev preReverseReady (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : PreReverseData :=
  preReverseState (readRegs regs 0 1 (words xs).head?) xs out

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiftRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform coefficient representations for the growing-parameter argument

Every base residue has an explicit little-endian word of width
`mu * (Nat.log 2 p + 1)`. The polynomial quotient uses one such word per
basis coefficient. These bounds keep p and mu visible. Binary modular
operations below use the existing bit/list algorithms and normalize back
to the prescribed width; their counters are source-level finite events,
not a claimed Turing-machine simulation.
-/

namespace SubexponentialSAT.SubexpLiftRing

open SubexponentialSAT.BinaryArithmetic

def mulBaseRun (B : ℕ) (modulus xs ys : List Bool) : List Bool × ℕ :=
  let out := ModularArithmetic.mulModRun modulus xs ys
  (normalizeBits B out.1, out.2.length + 3 * B)

@[simp] theorem mulBaseRun_length (B : ℕ) (m xs ys : List Bool) :
    (mulBaseRun B m xs ys).1.length = B := by simp [mulBaseRun]

end SubexponentialSAT.SubexpLiftRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSignature
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed nested row scanner.  The input matrix is a raw list of framed
rows, and each row is itself a raw list of framed coefficient words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def rowCall : SignatureCode := .call
  (ProgramLinking.liftProgram canonicalRowProgram id rowCallPorts)

def signatureStep : SignatureCode :=
  .seq (readWord 13 9 11 (by decide))
    (.seq (copy 12 10 11)
      (.seq signatureSeed (.seq rowCall (emitFrame 2 14 11 (by decide)))))

def signatureBody : SignatureCode := .seq signatureStep signaturePeek
def signatureLoop : SignatureCode := .while 1 signatureBody
def signatureCommand : SignatureCode := .seq signaturePeek signatureLoop

def signatureProgram := compiled signatureCommand 13 14

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPreparedQuartic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Quartic operations with a stored modulus

The modulus is input data. None of the operations in this file computes
`p^mu`, its bit expansion, or an irreducible polynomial. Setup is separate.
-/

namespace SubexponentialSAT.SubexpPreparedQuartic

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime]

variable (M : Modulus p μ)

def wordMul (x y : Word (baseWidth p μ)) : Word (baseWidth p μ) × ℕ :=
  let r := mulBaseRun (baseWidth p μ) M.bits x.val y.val
  (⟨r.1, mulBaseRun_length _ _ _ _⟩, r.2)

theorem wordAdd_correct (x y : Word (baseWidth p μ)) :
    wordValue p μ (wordAdd p μ M x y).1 = wordValue p μ x + wordValue p μ y := by
  unfold wordValue wordAdd
  dsimp only
  rw [addBaseRun_value]
  · simp only [M.value, ZMod.natCast_mod, Nat.cast_add]
  · rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos μ
  · rw [M.value]; exact modulus_le_width p μ

theorem wordAdd_canonical (x y : Word (baseWidth p μ)) :
    BinaryArithmetic.toNat (wordAdd p μ M x y).1.val < p^μ := by
  change BinaryArithmetic.toNat (addBaseRun _ _ _ _).1 < _
  rw [addBaseRun_value _ _ _ _ (by
    rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos μ) (by
    rw [M.value]; exact modulus_le_width p μ), M.value]
  exact Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos μ)

end SubexponentialSAT.SubexpPreparedQuartic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-width base-ring words for arbitrary extension degree. The arithmetic
programs below are the audited fixed scalar programs; the degree does not occur
in their instruction tables. Extension-vector scanning is a separate layer. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.ModularRingPrograms SubexponentialSAT.ModularDivisionPrograms

variable (p t : ℕ) [Fact p.Prime]

variable (M : SubexpPreparedQuartic.Modulus p t)

def scalarProgram (cache : ScalarCache p t) : RingProgram (ScalarCode p t) where
  zeroRun := (cache.zero, baseWidth p t)
  oneRun := (cache.one, baseWidth p t)
  addRun := SubexpPreparedQuartic.wordAdd p t M
  mulRun := SubexpPreparedQuartic.wordMul p t M
  negRun x := SubexpPreparedQuartic.wordMul p t M x cache.minusOne

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

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

local infixr:55 " ;; " => seq

/-- At row i, stack 106 has D-i tokens. Its full copy limits the inner loop
to D-i products; the outer copy loses one token for the next row. -/
def outerStep (pair : Code) : Code :=
  copy 106 109 ;; popToken 106 ;; takeCell 100 110 ;; copy 101 108 ;; copy 105 103 ;;
    innerLoop pair ;; clear 108 ;; clear 109 ;; clear 103 ;; clear 110 ;; appendIndex 105

def outerLoop (pair : Code) : Code :=
  test 106 14 ;; .while 14 (outerStep pair ;; test 106 14)

def command (pair : Code) : Code := outerLoop pair ;; clear 105

theorem clear_eval (d : Data) (src : Fin 256) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (afterClear d src) := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks) 2 rfl rfl
  simpa [afterClear, clear, StackRoutines.clearResult, StackRoutines.clearProgram,
    StackRoutines.clearStacks, StructuredProgram.State.withPC, Nat.add_assoc] using h

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

theorem copy_run (src dst : Fin 256) (s : Store)
    (hsd : src ≠ dst) (hst : src ≠ 120) (htd : (120 : Fin 256) ≠ dst)
    (htmp : s 120 = []) :
    ExecutesIn (copy src dst) (7 * (s src).length + 5) s
      (Function.update s dst (s src ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  simpa [copy, afterCopy, StackRoutines.copyStacks] using
    SubexpScanPrimitives.copy_eval (⟨regs, s⟩ : Data) src dst 120 0 1
      hsd hst htd (by decide) htmp

theorem clear_run (src : Fin 256) (s : Store) :
    ExecutesIn (clear src) (2 * (s src).length + 3) s (Function.update s src []) := by
  intro regs
  exact ⟨_, readRegs regs 0 1 none, le_rfl, clear_eval ⟨regs, s⟩ src⟩

end SubexponentialSAT.SubexpConvolutionControl

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

def prepare : Code :=
  .seq (copy 240 100) (.seq (copy 241 101) (.seq (copy 242 102) (copy 243 106)))

def command (multiply : Code) : Code := .seq prepare (.seq multiply finish)

theorem transfer_run (src dst : Fin 256) (s : Store) (hne : src ≠ dst) :
    ExecutesIn (transfer src dst) (3 * (s src).length + 3) s
      (Function.update (Function.update s src []) dst ((s src).reverse ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  simpa [transfer, afterTransfer, StackRoutines.transferStacks] using
    SubexpScanPrimitives.transfer_eval (⟨regs, s⟩ : Data) src dst 0 1 hne (by decide)

end SubexponentialSAT.SubexpPolynomialServiceControl

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

/-- The fixed cached-array wrapper uses 240/241 operands, 242 zero array,
243 unary length, and 244 output. The pair program is fixed independently
of all runtime dimensions. -/
def mulCommand (pair : Code) : Code :=
  SubexponentialSAT.SubexpPolynomialServiceControl.command (SubexponentialSAT.SubexpConvolutionControl.command pair)

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls StackRoutines ArrayPrograms

/-- A genuine fixed-program execution. The width is input data and is restored.
The exact cost includes the halt/return of each of the three subroutines. -/
theorem loadWord_eval (regs : Fin 2 → Bool) (word tail dst width : List Bool)
    (hwidth : width.length = word.length) :
    Eval loadWord (14 * word.length + 11)
      (loadState regs (word ++ tail) dst width [] [])
      (loadState (readRegs regs 0 1 none) tail (word ++ dst) width [] []) := by
  let rr := readRegs regs (0 : Fin 2) 1 none
  have hcopy := copyProgram_trace (2 : Fin 5) 3 4 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    regs (loadTapes (word ++ tail) dst width [] []) (by rfl)
  have hcopy' := halt_after_trace _ hcopy 7 rfl rfl
  have ecopy : Eval (.call (copyProgram (2 : Fin 5) 3 4 (0 : Fin 2) 1))
      (7 * width.length + 5)
      (loadState regs (word ++ tail) dst width [] [])
      (loadState rr (word ++ tail) dst width width []) := by
    apply Eval.call
    simpa only [loadState, StructuredProgram.State.withPC, copyResult, load_copy_stacks, rr,
      show loadTapes (word ++ tail) dst width [] [] 2 = width from rfl, Nat.add_assoc] using hcopy'
  have htake := countedTransferProgram_trace (3 : Fin 5) 0 4 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    word tail width rr (loadTapes (word ++ tail) dst width width [])
    rfl rfl hwidth
  have htake' := halt_after_trace _ htake 4 rfl rfl
  have etake : Eval (.call (countedTransferProgram (3 : Fin 5) 0 4 (0 : Fin 2) 1))
      (4 * word.length + 3)
      (loadState rr (word ++ tail) dst width width [])
      (loadState rr tail dst width [] word.reverse) := by
    apply Eval.call
    simpa [loadState, StructuredProgram.State.withPC, countedTransferProgram,
      countedTransferResult, load_counted_stacks, rr, readRegs_reset, Nat.add_assoc] using htake'
  have hfinish := transferProgram_trace (4 : Fin 5) 1 (0 : Fin 2) 1
    (by decide) (by decide) rr (loadTapes tail dst width [] word.reverse)
  have hfinish' := halt_after_trace _ hfinish 3 rfl rfl
  have efinish : Eval (.call (transferProgram (4 : Fin 5) 1 (0 : Fin 2) 1))
      (3 * word.length + 3)
      (loadState rr tail dst width [] word.reverse)
      (loadState rr tail (word ++ dst) width [] []) := by
    apply Eval.call
    simpa only [loadState, StructuredProgram.State.withPC, transferResult, load_finish_stacks,
      show loadTapes tail dst width [] word.reverse 4 = word.reverse from rfl, List.length_reverse, rr, readRegs_reset,
      Nat.add_assoc] using hfinish'
  have he := ecopy.seq (etake.seq efinish)
  convert he using 1 ; simp only [hwidth] ; omega

theorem loadWordProgram_trace (regs : Fin 2 → Bool) (word tail dst width : List Bool)
    (hwidth : width.length = word.length) :
    Trace loadWordProgram (14 * word.length + 12)
      ((loadState regs (word ++ tail) dst width [] []).withPC (some loadWordProgram.entry))
      ((loadState (readRegs regs 0 1 none) tail (word ++ dst) width [] []).withPC none) := by
  simpa only [Nat.add_assoc] using compiled_halt_trace (loadWord_eval regs word tail dst width hwidth) 0 1

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar addition inside a flat, runtime-sized coefficient scan. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev loadX : Cmd 8 15 := .call (ProgramLinking.liftProgram loadWordProgram loadRegisters loadXStacks)

theorem loadX_eval (regs : Fin 8 → Bool)
    (modulus word tail right ys out count width : List Bool)
    (hwidth : width.length = word.length) :
    Eval loadX (14 * word.length + 12)
      (addState regs modulus [] right (word ++ tail) ys out count width)
      (addState (readRegs regs 1 3 none) modulus word right tail ys out count width) := by
  have ht := loadWordProgram_trace ![regs 1, regs 3] word tail [] width hwidth
  have he := eval_call_lifted loadWordProgram loadRegisters loadXStacks
    (addState regs modulus [] right (word ++ tail) ys out count width)
    loadRegisters_injective loadXStacks_injective ht
  simpa only [reset_two, embed_loadX, List.append_nil, update_self_regs, update_false_regs] using he

theorem loadY_eval (regs : Fin 8 → Bool)
    (modulus left word tail xs out count width : List Bool)
    (hwidth : width.length = word.length) :
    Eval loadY (14 * word.length + 12)
      (addState regs modulus left [] xs (word ++ tail) out count width)
      (addState (readRegs regs 1 3 none) modulus left word xs tail out count width) := by
  have ht := loadWordProgram_trace ![regs 1, regs 3] word tail [] width hwidth
  have he := eval_call_lifted loadWordProgram loadRegisters loadYStacks
    (addState regs modulus left [] xs (word ++ tail) out count width)
    loadRegisters_injective loadYStacks_injective ht
  simpa only [reset_two, embed_loadY, List.append_nil, update_self_regs, update_false_regs] using he

abbrev addStep : Cmd 8 15 := .seq loadX (.seq loadY (.seq scalarAdd emitReverse))

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAddLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The vector length is a unary input, never a generated list of instructions. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev addLoop : Cmd 8 15 := .while 3 (.seq addStep popCount)
abbrev addScan : Cmd 8 15 := .seq popCount addLoop

abbrev addVector : Cmd 8 15 := .seq addScan finishAdd

abbrev addVectorProgram : Program 8 15 (size addVector + 1) := compiled addVector 8 0

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTriple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev scalarMul : Cmd 8 15 := .call (ProgramLinking.liftProgram
  ModularRingPrograms.wordMulProgram id scalarStacks)

theorem loadHead_eval (regs : Fin 8 → Bool)
    (modulus word tail right xs out count width : List Bool)
    (hwidth : width.length = word.length) :
    Eval loadHead (14 * word.length + 12)
      (addState regs modulus [] right xs (word ++ tail) out count width)
      (addState (readRegs regs 1 3 none) modulus word right xs tail out count width) := by
  have ht := loadWordProgram_trace ![regs 1, regs 3] word tail [] width hwidth
  have he := eval_call_lifted loadWordProgram loadRegisters loadHeadStacks
    (addState regs modulus [] right xs (word ++ tail) out count width)
    loadRegisters_injective loadHeadStacks_injective ht
  have hr : readRegs (![regs 1, regs 3] : Fin 2 → Bool) 0 1 none = ![false,false] := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have hu : Function.update (Function.update regs 1 (regs 1)) 3 (regs 3) = regs := by simp
  have hf : Function.update (Function.update regs 1 false) 3 false = readRegs regs 1 3 none := rfl
  simpa only [hr, embed_loadHead, List.append_nil, hu, hf] using he

abbrev tripleStep : Cmd 8 15 :=
  .seq emitReverse (.seq loadHead (.seq loadY (.seq scalarMul
    (.seq loadY (.seq scalarMul (.seq restoreAccumulator scalarAdd))))))

def tripleProduct (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (a b c : Word (baseWidth p t)) : Word (baseWidth p t) :=
  (SubexpPreparedQuartic.wordMul p t M (SubexpPreparedQuartic.wordMul p t M a b).1 c).1

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTripleLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control streaming contraction of arbitrary many scalar triples. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev tripleBits {B : ℕ} : List (WordTriple B) → List Bool
  | [] => []
  | x :: xs => x.1.val ++ (x.2.1.val ++ (x.2.2.val ++ tripleBits xs))

abbrev foldTriples (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t) :
    Word (baseWidth p t) → List (WordTriple (baseWidth p t)) → Word (baseWidth p t)
  | seed, [] => seed
  | seed, x :: xs => foldTriples p t M
      (SubexpPreparedQuartic.wordAdd p t M
        (tripleProduct p t M x.1 x.2.1 x.2.2) seed).1 xs

abbrev tripleLoop : Cmd 8 15 := .while 3 (.seq tripleStep popCount)
abbrev tripleScan : Cmd 8 15 := .seq popCount tripleLoop

abbrev tripleScanProgram : Program 8 15 (size tripleScan + 1) := compiled tripleScan 9 0

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed outer loop contracts a runtime-sized sequence of triple blocks. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev contractCoordinate : Cmd 8 20 := .call
  (ProgramLinking.liftProgram tripleScanProgram id contractLower)

abbrev contractStep : Cmd 8 20 := .seq contractCopyCount
  (.seq contractCopyZero (.seq contractCoordinate contractEmit))

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContractLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native whole-vector contraction, with both dimensions held on data tapes. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev blockBits {B : ℕ} : List (List (WordTriple B)) → List Bool
  | [] => []
  | b :: bs => tripleBits b ++ blockBits bs

abbrev contractBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (seed : Word (baseWidth p t)) : List (List (WordTriple (baseWidth p t))) → List Bool
  | [] => []
  | b :: bs => (foldTriples p t M seed b).val ++ contractBits p t M seed bs

abbrev contractLoop : Cmd 8 20 := .while 3 (.seq contractStep contractPop)
abbrev contractScan : Cmd 8 20 := .seq contractPop contractLoop

abbrev contractVector : Cmd 8 20 := .seq contractScan contractFinish

theorem contractBits_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (seed : Word (baseWidth p t)) (blocks : List (List (WordTriple (baseWidth p t)))) :
    (contractBits p t M seed blocks).length = blocks.length * baseWidth p t := by
  induction blocks with
  | nil => simp [contractBits]
  | cons b bs ih =>
      rw [contractBits, List.length_append, ih, List.length_cons, Nat.add_mul]
      simpa only [Nat.one_mul, Nat.add_comm] using
        congrArg (· + bs.length * baseWidth p t) (foldTriples p t M seed b).property

abbrev contractVectorProgram : Program 8 20 (size contractVector + 1) := compiled contractVector 9 0

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native loop produces a unary square from a unary input. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines

theorem countSquareProgram_trace (regs : Fin 2 → Bool) (source : List Bool) :
    ∃ rf, Trace countSquareProgram (7*source.length^2+14*source.length+8)
      ((countState regs source [] []).withPC (some countSquareProgram.entry))
      ((countState rf source [] (repeatCount source source.length)).withPC none) := by
  obtain ⟨rf, he⟩ := countSquare_eval regs source
  exact ⟨rf, by simpa only [Nat.add_assoc] using compiled_halt_trace he 0 2⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem clear_eval (d : Data) (dst : Fin 16) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 0 1 d.regs d.stacks)

theorem transfer_eval (d : Data) (src dst : Fin 16) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

theorem load_eval (d : Data) (which : Fin 3) (word tail : List Bool)
    (hsrc : d.stacks (loadPorts which 0) = word ++ tail)
    (h14 : d.stacks 14 = []) (h15 : d.stacks 15 = [])
    (hwidth : (d.stacks 13).length = word.length) :
    Eval (load which) (14 * word.length + 12) d (afterLoad d which word tail) := by
  let a := RingScan.loadState d.regs (word ++ tail)
    (d.stacks (loadPorts which 1)) (d.stacks 13) [] []
  let b := RingScan.loadState (readRegs d.regs 0 1 none) tail
    (word ++ d.stacks (loadPorts which 1)) (d.stacks 13) [] []
  have ha : embedState id (loadPorts which) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (loadPorts_injective which)
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      fin_cases i
      · exact hsrc
      · rfl
      · fin_cases which <;> rfl
      · fin_cases which <;> exact h14
      · fin_cases which <;> exact h15
    · intro i hi; rfl
  have hb : embedState id (loadPorts which) d b = afterLoad d which word tail := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (loadPorts_injective which)
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      fin_cases which <;> fin_cases i <;>
        simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, h14, h15]
    · intro i hi
      have hs : i ≠ loadPorts which 0 := fun h => hi ⟨0, h.symm⟩
      have hd : i ≠ loadPorts which 1 := fun h => hi ⟨1, h.symm⟩
      simp [afterLoad, hs, hd]
  have ht := RingScan.loadWordProgram_trace d.regs word tail
    (d.stacks (loadPorts which 1)) (d.stacks 13) hwidth
  have he := eval_call_lifted RingScan.loadWordProgram id (loadPorts which) d
    Function.injective_id (loadPorts_injective which) (a := a) (b := b) ht
  simpa only [ha, hb, load] using he

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem clearHeld_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (clear 6) (2 * s.held.length + 3) (state regs s)
      (state (readRegs regs 0 1 none) {s with held := []}) := by
  have he := clear_eval (state regs s) 6
  convert he using 1
  · simp [state, tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [state, tapes, clearStacks]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem finish_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (transfer 3 4) (3 * s.out.length + 3)
      (state regs {s with xs := []})
      (state (readRegs regs 0 1 none) {s with out := [], xs := s.out.reverse}) := by
  have he := transfer_eval (state regs {s with xs := []}) 3 4 (by decide)
  convert he using 1
  · simp [state, tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [state, tapes, transferStacks]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native coefficient-ring ABI. All service programs have fixed size. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem serviceClear_eval (s : State 8 32) (dst : Fin 32) :
    Eval (serviceClear dst) (2*(s.stacks dst).length+3) s (serviceAfterClear s dst) :=
  .call _ (ListRegisterProgram.clear_run dst 1 3 s.regs s.stacks)

theorem serviceTransfer_eval (s : State 8 32) (src dst : Fin 32) (hne : src ≠ dst) :
    Eval (serviceTransfer src dst) (3*(s.stacks src).length+3) s (serviceAfterTransfer s src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 1 3 hne (by decide) s.regs s.stacks)

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev serviceAdd : Cmd 8 32 := .call (ProgramLinking.liftProgram addVectorProgram id serviceAddPorts)

abbrev serviceAddProgram : Program 8 32 (size serviceAdd+1) := compiled serviceAdd 8 0

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceLifts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev serviceContract : Cmd 8 32 := .call
  (ProgramLinking.liftProgram contractVectorProgram id serviceContractPorts)

theorem serviceCount_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    ∃ rf, Eval serviceCount (7*s.degree.length^2+14*s.degree.length+8)
      (serviceWorkState regs {s with outer := [], inner := []})
      (serviceWorkState rf {s with outer := [], inner := repeatCount s.degree s.degree.length}) := by
  obtain ⟨rf, ht⟩ := countSquareProgram_trace ![regs 1, regs 3] s.degree
  have he := eval_call_lifted countSquareProgram loadRegisters serviceCountPorts
    (serviceWorkState regs {s with outer := [], inner := []})
    loadRegisters_injective serviceCountPorts_injective ht
  refine ⟨Function.update (Function.update regs 1 (rf 0)) 3 (rf 1), ?_⟩
  have hs : Function.update (Function.update regs 1 (regs 1)) 3 (regs 3) = regs := by simp
  simpa only [embed_count_service, Matrix.cons_val_zero, Matrix.cons_val_one, hs] using he


end SubexponentialSAT.SqrtLog.RingScan

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

theorem serviceDegree_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    Eval serviceDegree (3*s.degree.length+3)
      (serviceWorkState regs {s with outer := []})
      (serviceWorkState (readRegs regs 1 3 none) {s with degree := [], outer := s.degree.reverse}) := by
  have he := serviceTransfer_eval (serviceWorkState regs {s with outer := []}) 11 15 (by decide)
  convert he using 1
  · simp [serviceWorkState, serviceTapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [ serviceWorkState, serviceTapes, transferStacks]

abbrev serviceMul : Cmd 8 32 := .seq servicePrepare (.seq serviceExpand
  (.seq serviceRoute (.seq serviceCount (.seq serviceDegree (.seq serviceContract serviceFinish)))))

abbrev serviceMulProgram : Program 8 32 (size serviceMul+1) := compiled serviceMul 8 0

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramRingCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed native extension-ring multiplication for the dense convolution
controller. Its live operands are 198/199, result200, persistent degree204.
The private 32-stack ring workspace is separated from the array controller. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod


def native : Code := .call (ProgramLinking.liftProgram RingScan.serviceMulProgram registers ports)
def command : Code := .seq (copy 204 139) native

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall

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

def command : Code := .seq RingCall.command (.seq moveProduct accumulate)

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair

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

/-- One finite instruction table, independent of all dimensions. -/
def nativeMulCommand : Code := mulCommand Pair.command

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual fixed bit programs for the two logarithmic setup quantities.
Input and output numbers are arbitrary padded little-endian words. -/
namespace SubexponentialSAT.SqrtLog.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

/-- `k` is fixed syntax, not a natural-number machine instruction. -/
def addConst : ℕ → Cmd 3 3
  | 0 => .base .skip
  | k + 1 => .seq (addConst k) increment

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalCRTSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem clearMany_run (slots : List (Fin 256)) (s : Store) (L : ℕ)
    (hsize : ∀ j ∈ slots, (s j).length ≤ L) :
    ExecutesIn (clearMany slots) (slots.length * (2 * L + 3)) s (cleared slots s) := by
  induction slots generalizing s with
  | nil =>
      intro regs
      exact ⟨0, regs, by simp, .base (.skip _)⟩
  | cons i rest ih =>
      have h₁ := (clear_run i s).mono
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hsize i (by simp))) 3)
      have h₂ := ih (Function.update s i []) (by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · simpa [hji] using hsize j (List.mem_cons_of_mem i hj))
      have h := h₁.seq h₂
      convert h using 1 <;>
        first | rfl | omega | simp [Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.SubexpLocalCRTSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Aggregating the actual collision streams of all vertex pairs

The fixed program consumes framed pairs of already selected read plans.
Producing those selected plans from original plans and the remaining-index
table is a separate preparation step.  Every pair invokes the actual tuple
generator and collision machine; a final fixed unary tally produces the score.
-/

namespace SubexponentialSAT.Subexp.PairScoreProgram

open BitProgram StackRoutines StructuredCalls

def readPair (bits : List Bool) : PlanPair :=
  ((do
    let (left, rest) ← Encoding.readFrame bits
    let (right, _) ← Encoding.readFrame rest
    pure (readPlan left, readPlan right)) : Option PlanPair).getD ([], [])

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end


