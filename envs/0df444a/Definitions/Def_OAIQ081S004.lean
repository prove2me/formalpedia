-- Prove2me | Definitions.Def_OAIQ081S004
-- name    : OAIQ081S004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:22:18.06451+00:00
-- url     : https://prove2.me/theorems/85d78850-0bc1-482e-ac29-0fc68ea2c789
-- title:
--   Definitions bundle OAIQ081S004 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 84 declarations of OpenAI's Lean: 70 definitions, 2 inductive types or structures, 1 instance and 11 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse.work`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.differenceValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.hornerValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.includeBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.initializationBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseConstantsBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.inverseValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.preparationBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.binaryPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.AddService.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.addBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.eventBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor.coefficients`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.relocation`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall.port`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall.registers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.mulBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.nativeMulBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.addBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.mulBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.cacheVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.oneVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Regs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter.registers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingBasis.structureConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.tabulateRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ternaryLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.contractLower`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadHeadStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadXStacks` and 32 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_CRTLocalProgramCorrection`, `SubexponentialSAT_SqrtLog_CRTLocalProgramCorrectionAlgebra`, `SubexponentialSAT_SqrtLog_CRTLocalProgramDifference`, `SubexponentialSAT_SqrtLog_CRTLocalProgramExecution`, `SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionInit`, `SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionPrepare`, `SubexponentialSAT_SqrtLog_CRTLocalProgramHorner`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInclude`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInverse`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInverseComplete`, `SubexponentialSAT_SqrtLog_CRTLocalProgramInverseConstants`, `SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse`, `SubexponentialSAT_SqrtLog_CodeParametersProgramUnary`, `SubexponentialSAT_SqrtLog_DensePolynomialProgram`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramAddService`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramCell`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructorSemantics`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramFixed`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramMul`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramPair`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramPorts`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramRingCall`, `SubexponentialSAT_SqrtLog_HornerProgramServices`, `SubexponentialSAT_SqrtLog_IrreducibleSearchCompanion`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBank`, `SubexponentialSAT_SqrtLog_ReconstructionProgramRing`, `SubexponentialSAT_SqrtLog_RingBasis`, `SubexponentialSAT_SqrtLog_RingCore`, `SubexponentialSAT_SqrtLog_RingProgramBasic`, `SubexponentialSAT_SqrtLog_RingProgramModel`, `SubexponentialSAT_SqrtLog_RingScanAdd`, `SubexponentialSAT_SqrtLog_RingScanContract`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RingScanServiceAdd`, `SubexponentialSAT_SqrtLog_RingScanServiceLifts`, `SubexponentialSAT_SqrtLog_RingScanTriple`, `SubexponentialSAT_SqrtLog_RingTripleBasic`, `SubexponentialSAT_SqrtLog_RingTripleProgram`, `SubexponentialSAT_SubexpConvolutionExecution`, `SubexponentialSAT_SubexpConvolutionOuter`, `SubexponentialSAT_SubexpConvolutionPair`, `SubexponentialSAT_SubexpConvolutionStore`, `SubexponentialSAT_SubexpDensePolynomial`, `SubexponentialSAT_SubexpJetCellProgram`, `SubexponentialSAT_SubexpJetInitProgram`, `SubexponentialSAT_SubexpLinearFactorCall`, `SubexponentialSAT_SubexpPolynomialAddService`, `SubexponentialSAT_SubexpSymbolicCost`, `SubexponentialSAT_Subexp_BlockCopyProgram`, `SubexponentialSAT_TruncatedConvolution`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S032`, `OAIQ081S035`, `OAIQ081S039` and `OAIQ081S042`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

namespace Filter

def guardReg : Fin 13 → Fin 16 := Fin.castAdd 3


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TruncatedConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The elementary update schedule implemented by the fixed convolution loop.
This module defines values only; it assigns no execution cost to them. -/

namespace SubexponentialSAT.TruncatedConvolution

variable {C : Type*}

/-- Add one product into one existing coefficient slot. -/
def addProduct (add mul : C → C → C) (i : ℕ) (a b : C) (acc : List C) : List C :=
  acc.modify i (fun c => add (mul a b) c)

/-- A row of the triangular product schedule, beginning at output slot i. -/
def row (add mul : C → C → C) (a : C) : ℕ → List C → List C → List C
  | _, [], acc => acc
  | i, b :: bs, acc => row add mul a (i + 1) bs (addProduct add mul i a b acc)

/-- Fuel is the number of remaining output slots, so a row uses only that
many right-hand coefficients. All writes therefore have degree below D. -/
def rows (add mul : C → C → C) (Q : List C) : ℕ → ℕ → List C → List C → List C
  | _, 0, _, acc => acc
  | _, _ + 1, [], acc => acc
  | i, fuel + 1, a :: rest, acc =>
      rows add mul Q (i + 1) fuel rest (row add mul a i (Q.take (fuel + 1)) acc)

/-- Exactly D output slots; callers supply the actual zero coefficient. -/
def run (zero : C) (add mul : C → C → C) (D : ℕ) (P Q : List C) : List C :=
  rows add mul Q 0 D P (List.replicate D zero)

@[simp] theorem addProduct_length (add mul : C → C → C) (i : ℕ) (a b : C)
    (acc : List C) : (addProduct add mul i a b acc).length = acc.length := by
  simp [addProduct]

@[simp] theorem row_length (add mul : C → C → C) (a : C) (i : ℕ)
    (Q acc : List C) : (row add mul a i Q acc).length = acc.length := by
  induction Q generalizing i acc with
  | nil => rfl
  | cons b bs ih => simpa [row] using ih (i + 1) (addProduct add mul i a b acc)

@[simp] theorem rows_length (add mul : C → C → C) (Q : List C) (i fuel : ℕ)
    (P acc : List C) : (rows add mul Q i fuel P acc).length = acc.length := by
  induction fuel generalizing i P acc with
  | zero => rfl
  | succ fuel ih =>
      cases P with
      | nil => rfl
      | cons a rest => simpa [rows] using ih (i + 1) rest (row add mul a i (Q.take (fuel + 1)) acc)

@[simp] theorem run_length (zero : C) (add mul : C → C → C) (D : ℕ) (P Q : List C) :
    (run zero add mul D P Q).length = D := by
  simp [run]

end SubexponentialSAT.TruncatedConvolution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

abbrev Store := Fin 256 → List Bool

/-- Runtime buffers, in order: left, right, accumulator, output index, row
index, row fuel, right suffix, cell fuel, current coefficient, left operand,
right operand. All other stacks form the scalar-service/caller frame. -/
abbrev Buffers := Fin 11 → List Bool

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_UnaryForPrograms
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

structure Ports (R S : ℕ) where
  counter : Fin S
  bit : Fin R
  flag : Fin R

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSymbolicCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform symbolic list costs for growing parameters

The old canonical-list algorithm has an explicit fixed-degree event bound. This
module retains its interfaces and makes all parameter dependence visible. It also
refines exponent addition to an actual unary bit-string algorithm. Unary is used
only for exponent indices, whose values are O(D), never for ring coefficients.

Counters below are charged operations/bit inspections. A primitive tape-machine
execution certificate is a separate requirement.
-/

namespace SubexponentialSAT.SubexpSymbolicCost

/-- An actual coefficient implementation with a semantic decoder. No ring laws
are postulated on code words. Each operation returns its own measured counter. -/
structure RepresentedRing (C R : Type*) [CommRing R] where
  decode : C → R
  zeroRun : C × ℕ
  oneRun : C × ℕ
  addRun : C → C → C × ℕ
  mulRun : C → C → C × ℕ
  negRun : C → C × ℕ
  zero_correct : decode zeroRun.1 = 0
  one_correct : decode oneRun.1 = 1
  add_correct : ∀ a b, decode (addRun a b).1 = decode a + decode b
  mul_correct : ∀ a b, decode (mulRun a b).1 = decode a * decode b
  neg_correct : ∀ a, decode (negRun a).1 = -decode a

end SubexponentialSAT.SubexpSymbolicCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native fixed-control Horner iteration, shared by scalar nilpotent repair
and the independently truncated local polynomial inverse. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.SubexpConvolutionControl

def hornerValue {C : Type*} (mul add : C → C → C) (z one a : C) : C :=
  add (mul a z) one

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCorrectionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The jet loop runs J times independently of the scalar precision t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open Polynomial
open scoped BigOperators

def correctionValue {S : Type*} (mulOp addOp : S → S → S)
    (zero one negInverse inverse factor jet : S) (J : ℕ) : S :=
  let z := addOp (mulOp factor negInverse) one
  let series := (hornerValue mulOp addOp z one)^[J] zero
  mulOp (mulOp series inverse) jet

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockCopyProgram
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

/-- An encoded table repeated in block order. -/
def copies (n : ℕ) (table : List Bool) : List Bool :=
  (List.replicate n table).flatten

@[simp] theorem copies_zero (table : List Bool) : copies 0 table = [] := rfl

end SubexponentialSAT.Subexp.BlockCopyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetInitProgram
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

def blockRegisters : Fin 3 → Fin 16 := Fin.castAdd 13
def blockStacks : Fin 4 → Fin 128 := ![104, 102, 107, 108]

end SubexponentialSAT.SubexpJetInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLinearFactorCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Invoke the padded-linear constructor in the 256-stack polynomial
workspace, retaining a previously constructed zero coefficient on 104. -/

namespace SubexponentialSAT.SubexpLinearFactorCall

open SubexpConvolutionControl

def ports : Fin 128 ↪ Fin 256 := ⟨Fin.castAdd 128, Fin.castAdd_injective 128 128⟩

end SubexponentialSAT.SubexpLinearFactorCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native residue-power preparation with dynamic extension degree and ring
precision. Stack 209 contains a unary residue-size-minus-two exponent;
stack 212 independently contains the unary ring precision. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.SubexpConvolutionControl

def inverseValue {C : Type*} (mulOp addOp : C → C → C)
    (zero one minusOne a : C) (exponent precision : ℕ) : C :=
  let b := ((fun x => mulOp x a)^[exponent]) one
  let z := addOp (mulOp (mulOp b a) minusOne) one
  mulOp ((hornerValue mulOp addOp z one)^[precision] zero) b

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverseComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete native scalar inversion. The counter on 212 is independent of
the later polynomial-jet counter on 243. The only changed persistent port is
208. No inverse, residue-field enumeration, or ring-element enumeration is
an instruction of the compiled program. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.SubexpConvolutionControl

def inverseBudget (exponent precision Km Ka W : ℕ) : ℕ :=
  (exponent + precision + 1) * (4*Km + 4*Ka + 300*W + 400)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native local Hermite correction once the truncated cofactor and its
constant inverse have been prepared. Only output244 changes. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpConvolutionControl

def correctionBudget (J Km Ka W : ℕ) : ℕ :=
  (J+1)*(4*Km+2*Ka+300*W+400)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical inverse builder for a difference of two supplied nodes. The
residue exponent and nilpotence precision are the independent runtime inputs
209 and 212; no loop enumerates the lifted ring. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpConvolutionControl

def differenceValue {C : Type*} (mulOp addOp : C → C → C) (theta other minusOne : C) : C :=
  addOp theta (mulOp other minusOne)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInverseConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpConvolutionControl

def inverseConstantsBudget (e t J Km Ka W : ℕ) : ℕ :=
  inverseBudget e t Km Ka W + Km+44*W+56+440*(J+1)*(W+1)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInclude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One included-node update of the truncated local cofactor. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpConvolutionControl

def includeBudget (Km Ka Kp W V J : ℕ) : ℕ :=
  Km+Ka+102*W+113+220*(J+1)*(W+1)+(J+1)*(Kp+50*V+50)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionInit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact initialization and scan-state bridges for the native local CRT
controller. Only finite stack programs occur in these statements. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.SubexpConvolutionControl

def initializationBudget (J W nodes index : ℕ) : ℕ :=
  220 * (J + 1) * (W + 1) + 7 * (nodes + index) + 12

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpConvolutionControl

def preparationBudget (e t J Km Ka W V U : ℕ) : ℕ :=
  2 * (2 * U + 3) + (9 * V + 8) + (2 * V + 3) + (21 * W + 9 * V + 19) +
    inverseConstantsBudget e t J Km Ka W + 220 * (J + 1) * (W + 1) + (7 * V + 5)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the native local CRT scan, scalar inversion, and
polynomial correction. Service hypotheses refer to fixed finite commands;
they are instantiated by the concrete scalar and array service modules. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpConvolutionControl

def localBudget (nodes index exponent precision J Km Ka Kp Kap W V : ℕ) : ℕ :=
  initializationBudget J W (nodes * W) index +
  (nodes * (includeBudget Km Ka Kp W V J + 18 * W + 28) + 2) +
  preparationBudget exponent precision J Km Ka W V (index + 1) +
  correctionBudget J Kp Kap V + 5 * (2 * V + 3) + 2

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving CRT adapters for the native arbitrary-degree ring
programs. The adapter is a fixed finite table. Its cost includes three input
copies, the actual native trace, output copying and cleanup. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

open SubexponentialSAT SubexpConvolutionControl

/-- Native arithmetic uses its own bank; the four retained caches are shared
with the local polynomial services. -/
def ports : Fin 32 ↪ Fin 256 := ⟨
  ![128,129,130,131,132,194,134,135,136,137,138,139,202,141,142,143,
    144,203,146,147,148,149,201,151,152,153,154,155,156,157,158,159], by decide⟩

def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective 8 8⟩

end SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Dynamic-degree coefficient arithmetic

These executable callbacks operate on a runtime-sized coefficient vector.
Their counters include all scalar callbacks and one event per vector/list
entry. A separate flat-stack refinement must account for scanning serialized
vectors; callback event counts alone are not claimed to be primitive time.
-/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

/-- Tabulation explicitly charges one event per output coefficient. -/
def tabulateRun {d : ℕ} (f : Fin d → C × ℕ) : (Fin d → C) × ℕ :=
  let stored := List.Vector.ofFn f
  (fun i => (stored.get i).1, (∑ i, (stored.get i).2) + d)

@[simp] theorem tabulateRun_eq {d : ℕ} (f : Fin d → C × ℕ) :
    tabulateRun f = (fun i => (f i).1, (∑ i, (f i).2) + d) := by
  simp only [tabulateRun, List.Vector.get_ofFn]

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar addition inside a flat, runtime-sized coefficient scan. -/
namespace SubexponentialSAT.SqrtLog.RingScan

def loadRegisters : Fin 2 → Fin 8 := ![1, 3]
def loadXStacks : Fin 5 → Fin 15 := ![8, 0, 12, 13, 14]
def loadYStacks : Fin 5 → Fin 15 := ![9, 1, 12, 13, 14]

def scalarStacks : Fin 8 → Fin 15 := Fin.castAdd 7

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native three-scalar product and accumulator step. Triples are serialized
as consecutive fixed-width words; both width and triple count remain data. -/
namespace SubexponentialSAT.SqrtLog.RingScan

def loadHeadStacks : Fin 5 → Fin 15 := ![9, 0, 12, 13, 14]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed outer loop contracts a runtime-sized sequence of triple blocks. -/
namespace SubexponentialSAT.SqrtLog.RingScan

def contractLower : Fin 15 → Fin 20 := Fin.castAdd 5

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port primitives for dynamic Cartesian triple expansion. All loop
bounds and coefficient widths are words on stacks, not generated code. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

/-- 0 loads the next y, 1 the next table coefficient, 2 the next x. -/
def loadPorts (which : Fin 3) : Fin 5 → Fin 16 :=
  if which = 0 then ![5, 7, 13, 14, 15]
  else if which = 1 then ![2, 8, 13, 14, 15]
  else ![4, 6, 13, 14, 15]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

/-- Explicit cubic-in-degree, linear-in-width bound, including all repeated
source copies, each coefficient scan, and the final stream reversal. -/
def expandBudget (B d : ℕ) : ℕ :=
  (7 * d + 5) + (d * (200 * (d + 1)^2 * (B + 1) + 2) + 2) + (9 * B * d^3 + 3)

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan

def serviceAddPorts : Fin 15 → Fin 32 := Fin.castAdd 17

def serviceAddBudget (B d : ℕ) : ℕ := d*(6000*(B+1)^2+34*B+29)+6

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan

def serviceExpandPorts : Fin 16 → Fin 32 :=
  ![8, 9, 20, 21, 23, 24, 25, 26, 27, 11, 28, 29, 30, 12, 13, 14]
def serviceCountPorts : Fin 4 → Fin 32 := ![11, 15, 16, 19]
def serviceContractPorts : Fin 20 → Fin 32 := Fin.castAdd 12


end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanService
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native service for arbitrary-degree coefficient-ring products. -/
namespace SubexponentialSAT.SqrtLog.RingScan

def serviceMulBudget (B d : ℕ) : ℕ :=
  (7*(d^3*B)+5) + (RingTriple.expandBudget B d+1) +
  (4*d*B+18*B*d^3+12) + (7*d^2+14*d+8) + (3*d+3) +
  (d*(d*d*(18000*(B+1)^2+48*B+51)+13*B+18)+6) + (2*d^2+3)

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramServices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT SubexpConvolutionControl

def addBudget (B d : ℕ) : ℕ := RingScan.serviceAddBudget B d + 23 * (d * B) + 7*d + 24
def mulBudget (B d : ℕ) : ℕ := RingScan.serviceMulBudget B d + 23 * (d * B) + 7*d + 24

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Arbitrary-degree ternary unramified counting rings

This semantic model reuses the audited monic-lift construction. The extension
is not restricted to degree four. Its finite coefficient representation and
exact readback are exposed separately from any machine-cost refinement.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingCore

open Polynomial

instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

end SubexponentialSAT.SqrtLog.RingCore

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Finite multiplication tables for any monic polynomial quotient. -/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingBasis

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A] {d : ℕ}
variable (F : A[X]) (hF : F.Monic) (hdegree : F.natDegree = d)

def structureConstant (i j k : Fin d) : A :=
  (X ^ ((i : ℕ) + (j : ℕ)) %ₘ F).coeff (k : ℕ)

end SubexponentialSAT.SqrtLog.RingBasis

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchCompanion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit companion recurrence for the supplied monic polynomial

This module supplies the structure constants needed by the dynamic ring
program. It executes only coefficient-vector operations; polynomial
remainder is used solely to state and prove its meaning.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

def oneVector {R : Type*} [Zero R] [One R] (d : ℕ) : Fin d → R :=
  fun i => if i.val = 0 then 1 else 0

/-- Materialize every coefficient before the next companion step. -/
def cacheVector {R : Type*} {d : ℕ} (a : Fin d → R) : Fin d → R :=
  let stored := List.Vector.ofFn a
  stored.get

@[simp] theorem cacheVector_eq {R : Type*} {d : ℕ} (a : Fin d → R) :
    cacheVector a = a := by
  funext i
  exact List.Vector.get_ofFn a i

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete ternary coefficient input and the executable represented arithmetic
for the supplied-polynomial unramified ring model. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

/-- A ternary residue has a constant-size literal encoding. -/
def ternaryLiteral (a : ZMod 3) : List Bool :=
  if a.val = 0 then [] else if a.val = 1 then [true] else [false, true]

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A standalone native inverse of a node difference. The exponent is the
residue-field cardinality minus two; the separate repair loop has length t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse
open SubexponentialSAT.SubexpConvolutionControl

def work : List (Fin 256) := [205,208,219,220,222,240,241,244,245,246]

end SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

abbrev Regs := Fin 8 → Bool


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open LeafParametersProgram.Bank

def binaryPorts : Fin 7 → Fin 64 := ![9,11,12,15,18,19,21]

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDensePolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Dense univariate arithmetic through represented coefficient callbacks

Code words need no ring structure. Every scalar operation is a call to the
supplied implementation, and the returned counters are added along the actual
execution. These are callback counters, not a primitive-machine runtime theorem.
-/

namespace SubexponentialSAT.SubexpDensePolynomial

variable {C R : Type*} [CommRing R] (ops : SubexpSymbolicCost.RepresentedRing C R)

def decodeList (P : List C) : List R := P.map ops.decode

@[simp] theorem decodeList_length (P : List C) : (decodeList ops P).length = P.length := by
  simp [decodeList]

def addRun : List C → List C → List C × ℕ
  | [], Q => (Q, 0)
  | P, [] => (P, 0)
  | a :: P, b :: Q =>
      let head := ops.addRun a b
      let rest := addRun P Q
      (head.1 :: rest.1, head.2 + rest.2)

end SubexponentialSAT.SubexpDensePolynomial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialAddService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cached dense addition for the local CRT controller. The fixed service
copies operands 240/241, invokes the actual dense-add instruction table, and
moves its output to 244. All native workspace is restored. -/

namespace SubexponentialSAT.SubexpPolynomialAddService

open SubexpConvolutionControl

def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective _ _⟩
def ports : Fin 20 ↪ Fin 256 := ⟨Fin.castAdd 236, Fin.castAdd_injective _ _⟩

end SubexponentialSAT.SubexpPolynomialAddService

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAddService
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The arbitrary-degree native adder relocated into a caller, with all
untouched stacks preserved. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

variable (p t : ℕ)
  [Fact p.Prime]


namespace AddService
open SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpPolynomialAddService

def budget (degree B a b : ℕ) : ℕ :=
  7000 * (degree * (a + b) + 1) * (B + 1)^2 + 1 +
    13 * degree * B * (a + b) + 16

end AddService
end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructorSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The constructor's bit string is precisely a padded coefficient array. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

def coefficients {C : Type*} (zero low high : C) : ℕ → List C
  | 0 => []
  | 1 => [low]
  | n+2 => low :: high :: List.replicate n zero

@[simp] theorem coefficients_length {C : Type*} (zero low high : C) (J : ℕ) :
    (coefficients zero low high J).length = J := by
  cases J with
  | zero => rfl
  | succ J => cases J <;> simp [coefficients]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The outer triangular loop of the fixed convolution controller. Each row
copies the preserved right-hand array, consumes one left coefficient, and
executes only the still-relevant output positions. -/

namespace SubexponentialSAT.SubexpConvolutionControl

variable {C : Type*}

def outerCost (D W pairCost : ℕ) : ℕ :=
  (D + 1) * (pairCost + 100 * (W + 1))

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite-program execution of the padded triangular convolution.
The generic local pair contract is instantiated separately by the concrete
quartic multiplier and persistent-cell update service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

variable {C : Type*}

def convolutionBudget (D W pairCost : ℕ) : ℕ :=
  D * (outerCost D W pairCost + 4) + 5

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetCellProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def arrayPorts : Fin 8 → Fin 128 := ![102, 112, 113, 104, 114, 115, 116, 117]

end SubexponentialSAT.SubexpJetCellProgram
namespace SubexponentialSAT.SubexpJetCellProgram

def scalarPorts : Fin 20 → Fin 128 := Fin.castAdd 108

end SubexponentialSAT.SubexpJetCellProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

attribute [local simp] Fin.coe_ofNat_eq_mod

def lowPort (i : Fin 128) : Fin 256 := ⟨i.val, by omega⟩

end SubexponentialSAT.SubexpConvolutionPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramMul
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
open SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*}

def mulBudget (J W pairCost : ℕ) : ℕ :=
  convolutionBudget J W pairCost + 29 * J * W + 7 * J + 30

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native update of one arbitrary-degree ring coefficient in a persistent
flat polynomial array. Every scan, copy, and scalar addition is paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

open SubexponentialSAT.SubexpJetCellProgram

def addBudget (degree B : ℕ) : ℕ := 7000 * (2 * degree + 1) * (B + 1)^2 + 1

variable (p t : ℕ)
  [Fact p.Prime]
  {degree : ℕ}

def eventBudget (degree B I : ℕ) : ℕ :=
  addBudget degree B + I * (28 * (degree * B) + 34) + 49 * (degree * B) + 62


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native coefficient-ring port allocation. Metadata matches the
scalar CRT services; product operands and output use the convolution ports. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall
def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective _ _⟩
def port (i : Fin 32) : Fin 256 :=
  if i = 0 then 200 else if i = 8 then 198 else if i = 9 then 199 else
  if i = 5 then 194 else if i = 12 then 202 else if i = 17 then 203 else
  if i = 22 then 201 else ⟨128+i.val, by omega⟩

theorem port_injective : Function.Injective port := by decide

def ports : Fin 32 ↪ Fin 256 := ⟨port, port_injective⟩

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramRingCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed native extension-ring multiplication for the dense convolution
controller. Its live operands are 198/199, result200, persistent degree204.
The private 32-stack ring workspace is separated from the array controller. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall
open SubexponentialSAT.SubexpConvolutionControl
attribute [local simp] Fin.coe_ofNat_eq_mod


def budget (B d : ℕ) : ℕ := 7*d+5 + (RingScan.serviceMulBudget B d+1)

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native arbitrary-width coefficient multiply-and-accumulate. The high
workspace computes the ring product; the low workspace updates one encoded
array cell. Its runtime index scans and all transfers are explicitly paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpConvolutionPair

attribute [local simp] Fin.coe_ofNat_eq_mod

def budget (degree B I : ℕ) : ℕ :=
  RingCall.budget B degree + (6*(degree*B)+6) + (Cell.eventBudget degree B I+1)

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dense-polynomial arithmetic with arbitrary runtime ring
coefficient width. Native ring multiplication and every convolution scan are
included in the cost, and the output has the usual polynomial meaning. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.SubexpConvolutionControl

def nativeMulBudget (J degree B : ℕ) : ℕ := mulBudget J (degree*B) (Pair.budget degree B J)

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixed
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
open SubexponentialSAT.SubexpConvolutionControl
attribute [local simp] Fin.coe_ofNat_eq_mod


def relocation : Fin 256 ≃ Fin 256 :=
  (Equiv.swap 242 192).trans (Equiv.swap 243 193)
def ports : Fin 256 ↪ Fin 256 := relocation.toEmbedding

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end


