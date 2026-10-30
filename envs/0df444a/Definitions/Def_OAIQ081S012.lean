-- Prove2me | Definitions.Def_OAIQ081S012
-- name    : OAIQ081S012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:23:43.496057+00:00
-- url     : https://prove2.me/theorems/fb457aa4-3775-4068-b441-f393d751d122
-- title:
--   Definitions bundle OAIQ081S012 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 171 declarations of OpenAI's Lean: 139 definitions, 5 inductive types or structures, 1 instance and 26 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.regs8`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.reversePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.reverseRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowBodyCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScanCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.denominator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.Regs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.Words`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.eight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.erased`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.scratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.sourceWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.two`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.mass`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.blockPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.cleanupOps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.exportOps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.indexPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.integerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.integerRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.lookupPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.lookupRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataIndices`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepareOps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.workPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.denominatorWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.flatCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.flatPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.powerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.powerRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Literal.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.colPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.colRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.rowPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.rowRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore.scanPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore.scanRegisters` and 104 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutMatrixProgramInitialize`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRow`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowScan`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource`, `SubexponentialSAT_SqrtLog_LayoutNumerator`, `SubexponentialSAT_SqrtLog_LayoutOffsetProgram`, `SubexponentialSAT_SqrtLog_LayoutOffsetProgramRun`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramBounds`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore`, `SubexponentialSAT_SqrtLog_LayoutProgramArrays`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBank`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameUncovered`, `SubexponentialSAT_SqrtLog_LayoutProgramFrontend`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache`, `SubexponentialSAT_SqrtLog_LayoutProgramLiteral`, `SubexponentialSAT_SqrtLog_LayoutProgramLookupPair`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator`, `SubexponentialSAT_SqrtLog_LayoutProgramScanRestore`, `SubexponentialSAT_SqrtLog_LayoutProgramStaging`, `SubexponentialSAT_SqrtLog_LayoutProgramTypeCompare`, `SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry`, `SubexponentialSAT_SqrtLog_LayoutScaledMatrices`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic`, `SubexponentialSAT_SqrtLog_PackingAlgorithm`, `SubexponentialSAT_SqrtLog_PackingCallerProgramModel`, `SubexponentialSAT_SqrtLog_PackingHeadIncrementalCounts`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics`, `SubexponentialSAT_SqrtLog_PackingPrefix`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScopeBasic`, `SubexponentialSAT_SqrtLog_PackingProgramScores`, `SubexponentialSAT_SqrtLog_PackingProgramWeights`, `SubexponentialSAT_SubexpAnnihilation`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpSwapMultiplicity`, `SubexponentialSAT_Subexp_AssignmentAlphabetSemantics`, `SubexponentialSAT_Subexp_BucketProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_ConstraintEntryCompare`, `SubexponentialSAT_Subexp_GatherProgram`, `SubexponentialSAT_Subexp_GlobalBasisEntryCore`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_LocalExpectation`, `SubexponentialSAT_Subexp_LocalSpectrum`, `SubexponentialSAT_Subexp_MatrixAnchorGuardProgram`, `SubexponentialSAT_Subexp_MatrixAnchorReadProgram`, `SubexponentialSAT_Subexp_MatrixEntryCore`, `SubexponentialSAT_Subexp_MatrixInputAccess`, `SubexponentialSAT_Subexp_MatrixInputProgram`, `SubexponentialSAT_Subexp_MatrixPositionProgram`, `SubexponentialSAT_Subexp_MatrixScanStepProgram`, `SubexponentialSAT_Subexp_NaturalAssignment`, `SubexponentialSAT_Subexp_OneHotAlphabetProgram`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PackingProgramSupport`, `SubexponentialSAT_Subexp_PackingVertexLabels`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_TensorSpectrum`, `SubexponentialSAT_Subexp_TypeEnumeration`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S040`, `OAIQ081S041`, `OAIQ081S042` and `OAIQ081S043`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and framing adapters for direct construction of all incidence
rows. The adapters expose native instruction counts and exact stack effects. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram

abbrev regs8 : Fin 8 → Fin 16 := Fin.castAdd 8

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocatable finite-bank contract for integer incidence entries, and the
fixed physical storage layout used by the direct all-row matrix builder. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram

structure Store where
  rowIndex : List Bool := []
  columnIndex : List Bool := []
  positive : List Bool := []
  negative : List Bool := []
  remaining : List Bool := []
  reversedIDs : List Bool := []
  todo : List Bool := []
  row : List Bool := []
  matrix : List Bool := []

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid traversal of the explicit original-column identifier records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram

def rowScanCost (T B : ℕ) : List ℕ → ℕ
  | [] => 3
  | v::vs => T+8*B+8*v+29+rowScanCost T B vs

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramInitialize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid preparation of reversed original head-ID records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram

def reverseRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def reversePorts : Fin 4 → Fin 288 := ![283,285,282,286]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical row preparation and output framing for all-D construction. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram

def rowBodyCost (T B n j H h : ℕ) : ℕ :=
  9*j+7*H+h*(T+24*B+8*n+45)+25

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Integer numerators for the actual universal swap matrices

The parity coefficients are the immutable library's coefficients, instantiated
over the integers. Their images are the same coefficients over every
commutative ring. Clearing the projector denominators uses only powers of two.
-/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators

variable {r Q Δ : ℕ}

def denominator (R : ℕ) : ℤ := 2 ^ (R - 1)

theorem pow_two_clear (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (R j : ℕ) (hj : j < R) :
    (2 : K) ^ (R - 1 - j) =
      2 ^ (R - 1) * (2 : K)⁻¹ ^ j := by
  have hle : j ≤ R - 1 := by omega
  have hp : (2 : K) ^ (R - 1) = 2 ^ (R - 1 - j) * 2 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hc : (2 : K) ^ j * (2 : K)⁻¹ ^ j = 1 := by
    rw [← mul_pow]
    simp [h2]
  rw [hp, mul_assoc, hc, mul_one]

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native producer of the signed-bucket offset 2*B*(8*Q)^(2*R).
All arithmetic acts on runtime binary words. This offset is unrelated to
the unary scalar-row width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT
abbrev Words := Fin 15 → List Bool
abbrev Regs := Fin 8 → Bool

def two : List Bool := [false,true]
def eight : List Bool := [false,false,false,true]

def sourceWidth (B Q R : List Bool) : ℕ := B.length+Q.length+R.length+10

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgramRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT

abbrev erased : List (Fin 15) → Words → Words
  | [],w => w
  | i::is,w => erased is (Function.update w i [])

abbrev scratch : List (Fin 15) := [3,4,5,6,7,8]

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_LocalExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform multi-color conditional expectation

All parameters remain visible. The local evaluator enumerates only each pair's
read support, and its total evaluation bound is a fixed polynomial in the
number of chunks and universal types. Natural completion counts also give a
common-denominator representation for the rational conditional scores.
-/

namespace SubexponentialSAT.Subexp.LocalExpectation

open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

/-- Unnormalized finite completion count. Its terminal function can be a local
zero/one collision indicator. -/
def completionCount (alphabet : List W) (f : (I → W) → ℕ) :
    List I → (I → W) → ℕ
  | [], ω => f ω
  | i :: remaining, ω =>
      (alphabet.map (fun w => completionCount alphabet f remaining (Function.update ω i w))).sum

end SubexponentialSAT.Subexp.LocalExpectation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_NaturalAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Conditional assignment by natural-number comparisons

The executable chooser and all of its scores use natural numbers. A rational
common-denominator identity is used only to prove that every comparison,
including ties, agrees with the previously verified conditional-expectation
algorithm. Score execution enumerates only the active local pair support.
-/

namespace SubexponentialSAT.Subexp.NaturalAssignment

open scoped BigOperators

section Search

variable {A : Type*}

/-- Earliest minimum in an explicit nonempty list, using only natural scores. -/
def chooseMinNat (score : A → ℕ) (a : A) : List A → A
  | [] => a
  | b :: bs =>
      let c := chooseMinNat score b bs
      if score a ≤ score c then a else c

/-- Sequential assignment with a natural-number evaluator. -/
def assignNat (a : A) (tail : List A) (evaluate : ℕ → List A → ℕ) :
    ℕ → List A → List A
  | 0, fixed => fixed
  | n + 1, fixed =>
      let next := chooseMinNat (fun x => evaluate n (x :: fixed)) a tail
      assignNat a tail evaluate n (next :: fixed)

end Search

end SubexponentialSAT.Subexp.NaturalAssignment

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ReadPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit local read plans

Read plans are lists of numeric positions in the explicit seed array. The
machine-facing data are fixed-width one-hot word records and unary indices.
Gathering them in head/slot order reproduces the actual type encoding.
-/

namespace SubexponentialSAT.Subexp.ReadPlan

section Encoding

variable {r Q Δ : ℕ}

theorem ofFn_prod {A : Type*} {m n : ℕ} (f : Fin (m * n) → A) :
    List.ofFn f =
      (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n =>
        f (finProdFinEquiv (i, j))).flatten := by
  simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_comm, Nat.mul_comm]
    using List.ofFn_mul f

end Encoding

end SubexponentialSAT.Subexp.ReadPlan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BucketProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for one packing bucket

The input is a framed query followed by framed `(type key, vertex payload)`
records. The routine compares actual bit strings. It consumes all records,
keeps the query on port 2, and prepends matching framed payloads on port 5.
Supplying records in reverse vertex order produces the original bucket order.
-/

namespace SubexponentialSAT.Subexp.BucketProgram

abbrev Record := List Bool × List Bool

section TypedBucket

variable {V U : Type*} [DecidableEq U]

def vertexRecords (vertices : List V) (label : V → U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool) : List Record :=
  vertices.map fun v => (encodeType (label v), encodeVertex v)

end TypedBucket

end SubexponentialSAT.Subexp.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GatherProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program gathering runtime-selected rows

The packed assignment is on stack 0 and its unary row width on stack 3.
Stack 8 contains `ProgramEncoding.encodeRecords` of unary index words.
The program preserves the assignment and width and writes the selected rows,
in plan order, to stack 1. All widths and indices are stack data.
-/

namespace SubexponentialSAT.Subexp.GatherProgram

/-- The existing eight-stack persistent lookup occupies the first eight ports. -/
def lookupPort : Fin 8 → Fin 10 := Fin.castAdd 2

end SubexponentialSAT.Subexp.GatherProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingVertexLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Gathering the actual assignment type at every vertex before packing. -/

namespace SubexponentialSAT.Subexp.PackingVertexLabels

def gatherRegs (i : Fin 3) : Fin 8 := Fin.castAdd 5 i
def gatherPorts (i : Fin 10) : Fin 15 := Fin.castAdd 5 i

def callbackCost (width planBytes index : ℕ) : ℕ :=
  200 * (width + planBytes + index + 1) ^ 2

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber scan primitives. Original ambient IDs are compared as
unary strings; the emitted indices count positions in the actual plan stream. -/
namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT

def status (regs : Fin 5 → Bool) (v p : Bool) : Fin 5 → Bool :=
  Function.update (Function.update regs 0 v) 1 p

@[simp] theorem status_status (regs : Fin 5 → Bool) (v p v' p' : Bool) :
    status (status regs v p) v' p'=status regs v' p' := by
  funext i; fin_cases i <;> simp [status]

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT

def mass (ps : List (ℕ × ℕ)) : ℕ := (ps.map fun p => p.1+p.2).sum

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical access to the two-array integer matrix ABI. Every array entry is a
runtime-width binary word; its signed value is positive minus negative. The
fixed program below preserves both arrays, the index and width. It does not
assume a unit-cost array lookup or add an integer primitive to the machine. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

def positivePorts : Fin 8 ↪ Fin 11 :=
  ⟨![0,5,3,4,7,8,9,10], by decide⟩

def negativePorts : Fin 8 ↪ Fin 11 :=
  ⟨![1,6,3,4,7,8,9,10], by decide⟩

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed collision callback with a persistent output stream

The runtime ABI reserves stack 0 for a packed row table, stack 3 for its unary
word width, stacks 8 and 10 for the two read plans, and stack 11 for the output
stream. Stacks 1 and 12 hold the two gathered type encodings. The remaining
stacks are gathering scratch. All sizes, plans, and encoded words are data.

The equality stage below uses the existing fixed equality program, clears its
possibly unconsumed input suffixes, and pushes one collision bit. In particular,
an early mismatch cannot leave stale type bytes in the next callback's scratch.
-/

namespace SubexponentialSAT.Subexp.CollisionStreamProgram

def equalityPorts : Fin 2 → Fin 13 := fun i => if i = 0 then 1 else 12

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputAccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port array access used to prepare the matrix-entry comparison. -/

namespace SubexponentialSAT.Subexp.MatrixInputAccess

def low : Fin 8 → Fin 29 := Fin.castAdd 21

def eqRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def eqPorts (j : Fin 13) : Fin 29 :=
  if j.val = 0 then 1 else if j.val = 1 then 0 else if j.val = 12 then 28 else Fin.castAdd 16 j

@[simp] theorem eqPorts_one : eqPorts 1 = 0 := rfl
@[simp] theorem eqPorts_eleven : eqPorts 11 = 11 := rfl
@[simp] theorem eqPorts_twelve : eqPorts 12 = 28 := rfl

end SubexponentialSAT.Subexp.MatrixInputAccess

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstraintEntryCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compare the two preserved universal-type byte arrays without changing
the scalar result or any input stack of the matrix-entry service. -/

namespace SubexponentialSAT.Subexp.ConstraintEntryCompare

def registers : Fin 8 → Fin 10 := Fin.castAdd 2
def ports (j : Fin 29) : Fin 46 :=
  if j = 0 then 43 else if j = 28 then 44 else if j = 11 then 45 else j.castAdd 17

end SubexponentialSAT.Subexp.ConstraintEntryCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramTypeCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving comparison of the two type words using scratch0..3. All cache
ports42..48 remain intact. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

open SubexponentialSAT.Subexp

def ports : Fin 46 → Fin 64 :=
  ![42,43,44,45,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,
    25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,0,1,2,3]

end SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical comparison of the two color pairs at one matrix position.
The four color words occupy stacks 13--16. They are preserved. Actual copies,
the existing bit-equality table, and actual cleanup produce the comparison
bits; no semantic equality callback is assumed. -/

namespace SubexponentialSAT.Subexp.MatrixPositionProgram

abbrev smallRegs : Fin 5 → Fin 8 := Fin.castAdd 3
abbrev smallStacks : Fin 13 → Fin 17 := Fin.castAdd 4

def firstSource (swapped : Bool) : Fin 17 := if swapped then 13 else 14
def secondSource (swapped : Bool) : Fin 17 := if swapped then 14 else 13

end SubexponentialSAT.Subexp.MatrixPositionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical scan iteration: read four equal-width color records,
classify their same/swapped relation, and clear the consumed color buffers. -/

namespace SubexponentialSAT.Subexp.MatrixScanStepProgram

def lowPorts : Fin 17 → Fin 23 := Fin.castAdd 6

end SubexponentialSAT.Subexp.MatrixScanStepProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed arithmetic workspace and subroutines of the joint-entry program. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

def lowRegisters : Fin 8 → Fin 9 := Fin.castAdd 1

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Extract head/slot rows and compare the untouched spectator rows. All row
widths and selected-row indices are data; the instruction table is fixed. -/

namespace SubexponentialSAT.Subexp.MatrixInputProgram

open MatrixInputAccess


def sourcePort (second : Bool) : Fin 29 := if second then 24 else 23
def headPort (second : Bool) : Fin 29 := if second then 19 else 17
def slotPort (second : Bool) : Fin 29 := if second then 20 else 18

end SubexponentialSAT.Subexp.MatrixInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorGuardProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Three physical byte comparisons for the selected joint coordinate. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

def eqRegs : Fin 5 → Fin 10 := Fin.castAdd 5
def eqStacks : Fin 13 → Fin 42 := Fin.castAdd 29

def slot : Fin 4 → Fin 42 := ![38, 39, 40, 41]

end SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit mismatch interpolation for the multi-color layout

Section 3.3 of `subexponential-sat.txt`. All inverse data are supplied as
units. The polynomials are finite sums and products, not chosen witnesses.
Their scalar evaluation functions are executable from the supplied ring
operations and units; the semantic polynomial definitions use mathlib's
noncomputable polynomial representation.
-/

namespace SubexponentialSAT.SubexpRowInterpolation

open scoped BigOperators

variable {E I V C : Type*} [CommRing E] [DecidableEq I]

variable {node : I → E}

variable [DecidableEq V]

/-- The initial selector is retained even when its own column gets a correction. -/
noncomputable def rowPath (v : V) (c : V → Polynomial E) : V → Polynomial E :=
  fun y => Polynomial.C ((Pi.single v (1 : E) : V → E) y) + c y

theorem eval_rowPath (v : V) (c : V → Polynomial E) (x : E) :
    (fun y => (rowPath v c y).eval x) =
      Pi.single v (1 : E) + (fun y => (c y).eval x) := by
  funext y
  simp [rowPath]

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpAnnihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Simultaneous row annihilation for the multicolor layout

Section 3.3 of `source/subexponential-sat.txt`.  At a fixed interpolation
position, the same row annihilates every color different from its slot color.
The old two-color modules are preserved and used only for generic finite-sum
lemmas.
-/

namespace SubexponentialSAT.SubexpAnnihilation

open scoped BigOperators
open Matrix

section MatrixExtension

variable {V F E : Type*} [Ring F] [Ring E]

/-- Extend both row and column indices by zero. The membership tests are
explicit data, so this definition does not choose a representative. -/
def zeroExtendMatrix (J : Set V) [DecidablePred (· ∈ J)]
    (M : Matrix J J F) (u y : V) : F :=
  if hu : u ∈ J then
    if hy : y ∈ J then M ⟨u, hu⟩ ⟨y, hy⟩ else 0
  else 0

@[simp] theorem zeroExtendMatrix_of_row_not_mem (J : Set V)
    [DecidablePred (· ∈ J)] (M : Matrix J J F) (u y : V) (hu : u ∉ J) :
    zeroExtendMatrix J M u y = 0 := by
  simp [zeroExtendMatrix, hu]

@[simp] theorem zeroExtendMatrix_of_column_not_mem (J : Set V)
    [DecidablePred (· ∈ J)] (M : Matrix J J F) (u y : V) (hy : y ∉ J) :
    zeroExtendMatrix J M u y = 0 := by
  by_cases hu : u ∈ J <;> simp [zeroExtendMatrix, hu, hy]

/-- Mapping coefficients commutes with the explicit zero extension. -/
theorem zeroExtendMatrix_map (J : Set V) [DecidablePred (· ∈ J)]
    (M : Matrix J J F) (φ : F →+* E) (u y : V) :
    zeroExtendMatrix J (M.map φ) u y = φ (zeroExtendMatrix J M u y) := by
  by_cases hu : u ∈ J <;> by_cases hy : y ∈ J <;>
    simp [zeroExtendMatrix, hu, hy, Matrix.map_apply]

end MatrixExtension

end SubexponentialSAT.SubexpAnnihilation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorReadProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the selected color from each of four preserved word streams. The
position is a unary runtime cursor on stack37; color width is on stack21. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

def low : Fin 8 → Fin 42 := Fin.castAdd 34

def source (i : Fin 4) : Fin 42 := ⟨17 + i.val, by omega⟩
def target (i : Fin 4) : Fin 42 := ⟨38 + i.val, by omega⟩

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

def sumPorts : Fin 16 → Fin 18 :=
  ![16,17,0,1,2,3,4,5,6,7,8,9,10,11,12,15]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

def cacheCellPorts : Fin 3 → Fin 18 := ![0,2,4]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

def initialRecord : List Bool := [true,true,true,false,false]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

def initialBuildPorts (j : Fin 18) : Fin 19 := if j = 17 then 18 else Fin.castAdd 1 j

def cacheBuildPorts : Fin 18 → Fin 19 := Fin.castAdd 1

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

def regs2 : Fin 2 → Fin 9 := Fin.castAdd 7
def regs8 : Fin 8 → Fin 9 := Fin.castAdd 1
def countPorts : Fin 2 → Fin 40 := ![9,7]
def binomialPorts : Fin 20 → Fin 40 :=
  ![12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,8,10,2]
def numeratorPorts : Fin 25 → Fin 40 :=
  ![0,1,12,13,2,3,4,9,14,15,16,17,18,19,20,21,22,23,24,11,25,26,27,37,38]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

def smallRegisters : Fin 2 → Fin 9 := Fin.castAdd 7
def workRegisters : Fin 8 → Fin 9 := Fin.castAdd 1

def readPorts (binomial : Bool) : Fin 11 → Fin 20 :=
  if binomial then ![2,3,9,10,4,11,12,13,14,15,16]
  else ![0,1,8,10,4,11,12,13,14,15,16]

def emitPorts (which : Fin 3) : Fin 7 → Fin 20 :=
  if which = 0 then ![11,12,17,13,14,15,16]
  else if which = 1 then ![12,11,17,13,14,15,16]
  else ![5,6,17,13,14,15,16]

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/

/-! A fixed, paid iteration producing the three real scalar operands. -/

/-! The native unary loop produces all triples in increasing binomial index. -/

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

def parityRegisters : Fin 3 → Fin 9 := ![0,1,8]
def parityPorts : Fin 1 → Fin 20 := fun _ => 19

def finishPorts : Fin 7 → Fin 20 := ![0,1,17,13,14,15,18]

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgram.lean

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete cached scalar call preserves both arrays, the width and the
clearing power. It constructs its operand stream and performs every signed
arithmetic operation on the primitive machine. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open LayoutTriplePreparationProgram

def numeratorPreparePorts : Fin 20 → Fin 25 := Fin.castAdd 5
def numeratorScalarRegisters : Fin 8 → Fin 9 := Fin.castAdd 1
def numeratorScalarPorts : Fin 18 → Fin 25 :=
  ![7,8,9,10,11,12,13,14,15,16,17,19,20,21,22,18,23,24]

def numeratorPrepareCost (N A W P : ℕ) : ℕ :=
  9*N+3*A+N*(N*(28*W+34)+140*W+18*P+222)+3*(N*(8*W+2*P+9))+24

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open LayoutTriplePreparationProgram

def binomialCost (h R W : ℕ) : ℕ :=
  12*R+400*(h+1)*(R+1)*(h+5)+110*(R+1)*(W+(h+1)+4)+32


end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScanRestore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The old classifier parks the unary Q word on33. This wrapper physically
returns that word to22 and exposes only the two new counters and flag. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

open SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.MatrixEntryProgram

def scanRegisters : Fin 9 → Fin 10 := Fin.castAdd 1
def scanPorts : Fin 37 → Fin 64 := Fin.castAdd 27

end SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for one universal integer constraint entry. The concrete
local stages are lifted into one bank; subsequent lemmas compose their traces.
No ring inversion or field-valued matrix is used in this integer procedure. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

open SubexponentialSAT.Subexp

def guardPorts : Fin 42 → Fin 64 := Fin.castAdd 22
def smallRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def scalarRegs : Fin 9 → Fin 10 := Fin.castAdd 1
def scalarPorts : Fin 40 → Fin 64 :=
  ![42,43,44,45,46,47,48,2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
    27,28,29,30,31,32,33,34,35,50,51,36]
def defectPorts : Fin 10 → Fin 64 := ![50,51,45,53,54,0,1,4,5,6]

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

def selectorPort (i : Fin 6) : Fin 12 := ⟨5 + i.val, by omega⟩

def parserReg (i : Fin 2) : Fin 5 := Fin.castAdd 3 i
def parserPort (src dst : Fin 12) : Fin 2 → Fin 12 := ![src, dst]

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgramSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact finite-port framing for the physical packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgramSupport

def registers {r : ℕ} (h : r ≤ 16) : Fin r → Fin 16 := Fin.castLE h

end SubexponentialSAT.Subexp.PackingProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_OneHotAlphabetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Runtime one-hot alphabet generation

The unary input length r is data. Each loop iteration constructs one r-bit
one-hot word using the checked repeated-copy program and prepends its frame.
The final order is the decreasing order of the hot bit's position.
-/

namespace SubexponentialSAT.Subexp.OneHotAlphabetProgram

abbrev zeros (n : ℕ) := List.replicate n false

def word (i n : ℕ) : List Bool := zeros i ++ true :: zeros n

def rows : ℕ → ℕ → List (List Bool)
  | _, 0 => []
  | i, n + 1 => rows (i + 1) n ++ [word i n]

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentAlphabetSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual tuple-generator order is retained in the initializer alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

open OneHotAlphabetProgram

def oneHot {r : ℕ} (c : Fin r) : List Bool :=
  List.ofFn (fun j : Fin r => decide (c = j))

def hotAt (r i : ℕ) : List Bool := zeros i ++ true :: zeros (r - i - 1)

theorem oneHot_eq {r : ℕ} (c : Fin r) : oneHot c = hotAt r c.val := by
  apply List.ext_getElem
  · simp [oneHot, hotAt]
    omega
  · intro i hi hj
    have hir : i < r := by simpa [oneHot] using hi
    by_cases hlt : i < c.val
    · have hne : c.val ≠ i := by omega
      simp [oneHot, hotAt, hlt, Fin.ext_iff, hne]
    · by_cases he : i = c.val
      · subst i
        simp [oneHot, hotAt, Fin.ext_iff]
      · have hpos : 0 < i - c.val := by omega
        have hn : i - c.val ≠ 0 := by omega
        simp [oneHot, hotAt, List.getElem_append, hlt, Fin.ext_iff,
          Ne.symm he, List.getElem_cons, hn]

theorem rows_eq_range (i n : ℕ) :
    rows i n = (List.range' i n).reverse.map (hotAt (i + n)) := by
  induction n generalizing i with
  | zero => simp [rows]
  | succ n ih =>
      rw [rows, ih, List.range'_succ, List.reverse_cons, List.map_append, List.map_singleton]
      have he : i + 1 + n = i + (n + 1) := by omega
      rw [he]
      congr 1
      simp [word, hotAt]

theorem oneHot_injective (r : ℕ) : Function.Injective (@oneHot r) := by
  intro a b h
  have he := congrFun (List.ofFn_injective h) a
  have hba : b = a := by simpa using he.symm
  exact hba.symm

theorem list_lift {A B : Type*} (f : A → B) (bs : List B)
    (h : ∀ b ∈ bs, ∃ a, f a = b) : ∃ as : List A, as.map f = bs := by
  induction bs with
  | nil => exact ⟨[], rfl⟩
  | cons b bs ih =>
      obtain ⟨a, ha⟩ := h b (by simp)
      obtain ⟨as, has⟩ := ih (by intro c hc; exact h c (by simp [hc]))
      exact ⟨a :: as, by simp [ha, has]⟩

end SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual universal-type enumeration

The byte list is the output of the fixed Cartesian-power program.  The
semantic list and its finite equivalences only name that same physical
order; they are not executable inputs to any program.
-/

namespace SubexponentialSAT.Subexp.TypeEnumeration

open AssignmentAlphabetSemantics

theorem list_lift {A B : Type*} (f : A → B) (bs : List B)
    (h : ∀ b ∈ bs, ∃ a, f a = b) : ∃ as : List A, as.map f = bs := by
  induction bs with
  | nil => exact ⟨[], rfl⟩
  | cons b bs ih =>
      obtain ⟨a, ha⟩ := h b (by simp)
      obtain ⟨as, has⟩ := ih (by intro c hc; exact h c (by simp [hc]))
      exact ⟨a :: as, by simp [ha, has]⟩

end SubexponentialSAT.Subexp.TypeEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
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

abbrev unary (n : ℕ) := List.replicate n true
abbrev Records := List (List Bool × List Bool)

def queryRegs : Fin 5 → Fin 8 := Fin.castAdd 3

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLookupPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Two actual metadata lookups with disjoint returned records. Both query
indices and the computed metadata master are preserved. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair

open SubexponentialSAT.Subexp
open GlobalBasisMetadata

def rowRegisters : Fin 5 → Fin 6 := Fin.castAdd 1
def colRegisters : Fin 5 → Fin 6 := ![0,1,2,3,5]
def rowPorts : Fin 12 → Fin 16 := ![0,1,3,4,5,9,10,11,12,13,14,15]
def colPorts : Fin 12 → Fin 16 := ![0,2,6,7,8,9,10,11,12,13,14,15]

end SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramStaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A finite sequence of genuine copy, clear and constant-bit instructions.
The functional result is only a trace specification; execution uses the
fixed primitive instruction tables. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Staging

open SubexponentialSAT.Subexp

variable {r s : ℕ}

inductive Action (s : ℕ) where
  | copy (src dst : Fin s)
  | clear (dst : Fin s)
  | push (dst : Fin s) (bit : Bool)
  deriving DecidableEq

def Action.Valid (tmp : Fin s) : Action s → Prop
  | .copy src dst => src≠dst ∧ src≠tmp ∧ tmp≠dst
  | .clear _ => True
  | .push dst _ => tmp≠dst

end SubexponentialSAT.SqrtLog.LayoutProgram.Staging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisEntryCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete framed-word, comparison, and scalar-cell services for the
global matrix entry callback. Register 6 is the persistent row-kind flag. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntryCore

def smallRegs : Fin 5 ↪ Fin 16 := ⟨Fin.castAdd 11, Fin.castAdd_injective 5 11⟩
def sealPorts : Fin 13 ↪ Fin 32 := ⟨fun i => ⟨16 + i.val, by omega⟩, by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp at this
  omega⟩

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.Subexp

def lookupRegs : Fin 6 → Fin 16 := Fin.castAdd 10
def lookupPorts : Fin 16 → Fin 256 := ![200,252,253,64,65,66,67,68,69,70,71,72,73,74,75,76]
def integerRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def integerPorts : Fin 64 → Fin 256 := Fin.castAdd 192

def blockPorts : Fin 32 → Fin 256 :=
  ![64,67,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
def indexPorts : Fin 32 → Fin 256 :=
  ![252,253,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]

def prepareOps : List (Staging.Action 256) :=
  [.copy 202 42,.copy 203 43,.copy 204 44,.copy 205 45,.copy 206 47,.copy 207 48,
   .copy 208 21,.copy 209 22,.copy 210 37,.copy 211 26,.copy 65 23,.copy 68 24,.push 25 true]

def exportOps : List (Staging.Action 256) := [.copy 53 254,.copy 54 255]

def workPorts : List (Fin 256) := List.ofFn (fun i : Fin 200 => i.castAdd 56)
def cleanupOps : List (Staging.Action 256) := workPorts.map Staging.Action.clear

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameUncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.Subexp

def metadataIndices : Finset (Fin 200) := {64,65,66,67,68,69}

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramFrontend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical label/type frontend for arbitrary runtime incidence plans.
The plans have already been produced by the native incidence scan. This
frontend gathers their actual words and generates the complete type alphabet;
it does not accept label records or block metadata as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

open SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.PackingProgramSupport

structure Params where
  D : ℕ
  Δ : ℕ
  rows : List (List Bool)
  width : List Bool
  alphabet : List (List Bool)
  planList : List (List ℕ)
  plans_count : planList.length = D

namespace Params

@[simp] theorem planList_length (p : Params) : p.planList.length = p.D := p.plans_count

end Params

end SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reusable integer-cache initialization. The runtime parameters A, R
and common width remain on20/21/22. Outputs are H-positive0, H-negative1,
binary clearing denominator2, and retained local width19. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

open LayoutProgramScalar

def flatPorts : Fin 20 → Fin 24 := Fin.castAdd 4
def powerRegs : Fin 2 → Fin 8 := Fin.castAdd 6
def powerPorts : Fin 2 → Fin 24 := ![23,2]

def denominatorWord (R : ℕ) : List Bool := List.replicate (R-1) false ++ [true]

def flatCost (A R W : ℕ) : ℕ :=
  12*R+400*(A+1)*(R+1)*(2*A*R+5)+110*(R+1)*(W+(1+2*A*R)+4)+16

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLiteral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid preserving conversion of one scalar word into a complete forward
postfix literal. This is used for uncovered identity entries and zero branches. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Literal

def ports : Fin 3 → Fin 4 := Fin.castAdd 1

end SubexponentialSAT.SqrtLog.LayoutProgram.Literal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScaledMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cleared integer matrices and exact ring-valued source rows

The rational spectral argument will supply integer numerators `N` and a
power-of-two denominator `d`. Over the target coefficient ring only the
unit representing `d` is inverted. Exact integer equations `d I - N`
therefore imply the fixed-vector equations needed by the original
multicolor row construction, without a map from `ℚ` to the target ring.
-/

namespace SubexponentialSAT.SqrtLog.LayoutScaledMatrices

open scoped BigOperators
open Matrix

section Cleared

variable {J O : Type*} [Fintype J] [DecidableEq J] [CommRing O]

def clearedDefect (d : ℤ) (N : Matrix J J ℤ) : Matrix J J ℤ :=
  fun i j => (if i = j then d else 0) - N i j

def unitScaled (u : Oˣ) (N : Matrix J J ℤ) : Matrix J J O :=
  fun i j => (↑(u⁻¹) : O) * (N i j : O)

theorem fixed_of_clearedDefect (d : ℤ) (u : Oˣ) (hu : (u : O) = (d : O))
    (N : Matrix J J ℤ) (z : J → ℤ)
    (hz : clearedDefect d N *ᵥ z = 0) :
    unitScaled u N *ᵥ (fun j => (z j : O)) = fun j => (z j : O) := by
  funext i
  have hzi := congrFun hz i
  have hN : ∑ j, N i j * z j = d * z i := by
    have hzero : d * z i - ∑ j, N i j * z j = 0 := by
      simpa [clearedDefect, Matrix.mulVec, dotProduct, sub_mul,
        Finset.sum_sub_distrib] using hzi
    exact (sub_eq_zero.mp hzero).symm
  change (∑ j, (↑(u⁻¹) : O) * (N i j : O) * (z j : O)) = (z i : O)
  calc
    _ = (↑(u⁻¹) : O) * ((∑ j, N i j * z j : ℤ) : O) := by
      simp [Finset.mul_sum, mul_assoc]
    _ = (↑(u⁻¹) : O) * ((d * z i : ℤ) : O) := by rw [hN]
    _ = (z i : O) := by
      push_cast
      rw [← hu, ← mul_assoc]
      simp

end Cleared

end SubexponentialSAT.SqrtLog.LayoutScaledMatrices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A deterministic conditional-expectation algorithm with at most four word reads per term. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Algorithm
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

abbrev ScoreTerm (I V : Type*) (Q : ℕ) := (I × I) ⊕ (Fin Q × V × V)

def scoreSupport : ScoreTerm I V Q → Finset (V ⊕ E)
  | .inl (i,j) => [Sum.inl (ivar i), Sum.inr (factor i),
      Sum.inl (ivar j), Sum.inr (factor j)].toFinset
  | .inr (_,v,w) => [Sum.inl v, Sum.inl w].toFinset

end Algorithm
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Denominator-cleared scores for incidence/head conditional expectation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing

structure Weights where
  incidence : ℕ
  head : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Heads-first numbering and the actual reverse-list assignment prefix. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Indices
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def headsFirstIndices (vertices : List V) (factors : List E) : List (V ⊕ E) :=
  vertices.map Sum.inl ++ factors.map Sum.inr

omit [DecidableEq V] [DecidableEq E] in
theorem headsFirst_length (vertices : List V) (factors : List E) :
    (headsFirstIndices vertices factors).length = vertices.length + factors.length := by
  simp [headsFirstIndices]

end Indices

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed original-variable/factor semantics of the native address list. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics
open SubexponentialSAT.Subexp

def seedIndices (n f : ℕ) := Packing.headsFirstIndices (List.finRange n) (List.finRange f)

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSwapMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multiplicities of register-swap eigenvalue labels

The negative local labels are strictly below the diagonal and the positive
labels are on or above it. Counting these labels and their tensor words is
independent of the characteristic of the coefficient field.
-/

namespace SubexponentialSAT.SubexpSwapMultiplicity

open scoped BigOperators

section PredicateWords

variable {ι β υ : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
variable (Neg : β → Prop) [DecidablePred Neg]

def negativeSupport (word : ι → β) : Finset ι :=
  Finset.univ.filter fun l => Neg (word l)

def weight (word : ι → β) : ℕ := (negativeSupport Neg word).card

omit [DecidableEq ι] [Fintype β] in
@[simp] theorem mem_negativeSupport (word : ι → β) (l : ι) :
    l ∈ negativeSupport Neg word ↔ Neg (word l) := by
  simp [negativeSupport]

end PredicateWords

def negativePair {r : ℕ} (x : Fin r × Fin r) : Prop := x.2 < x.1

instance instDecidablePredProdFinNegativePair {r : ℕ} : DecidablePred (@negativePair r) :=
  fun x => inferInstanceAs (Decidable (x.2 < x.1))

abbrev swapWeight {r : ℕ} {ι : Type*} [Fintype ι]
    (word : ι → Fin r × Fin r) := weight negativePair word

/-! ## General binomial second moment and the interval tail -/

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_LocalSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Spectrum of a swap of two finite ordered registers

The alphabet size is unrestricted relative to the characteristic.  The only
field assumption beyond `Field K` is `2 ≠ 0`.  Basis labels on or above the
diagonal are positive; labels strictly below the diagonal are negative.
-/

namespace SubexponentialSAT.Subexp.LocalSpectrum

open scoped BigOperators

abbrev Pair (α : Type*) := α × α

def swapPair {α : Type*} (x : Pair α) : Pair α := (x.2, x.1)

@[simp] theorem swapPair_involutive {α : Type*} (x : Pair α) :
    swapPair (swapPair x) = x := by cases x; rfl

variable (K : Type*) [Field K]
variable {α : Type*}

/-- The actual permutation operator on functions on two registers. -/
def swapMap : Module.End K (Pair α → K) where
  toFun f x := f (swapPair x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem swapMap_apply (f : Pair α → K) (x : Pair α) :
    swapMap K f x = f (swapPair x) := rfl

@[simp] theorem swapMap_involutive (f : Pair α → K) :
    swapMap K (swapMap K f) = f := by
  funext x
  simp

variable [LinearOrder α]

/-- Diagonal entries are fixed; each unordered off-diagonal pair supplies a sum
coordinate and a difference coordinate. -/
def eigenCoordinates (f : Pair α → K) (x : Pair α) : K :=
  if x.1 = x.2 then f x else
  if x.1 < x.2 then (f x + f (swapPair x)) / 2
  else (f (swapPair x) - f x) / 2

def fromEigenCoordinates (c : Pair α → K) (x : Pair α) : K :=
  if x.1 = x.2 then c x else
  if x.1 < x.2 then c x + c (swapPair x)
  else c (swapPair x) - c x

def eigenCoordinateEquiv (h2 : (2 : K) ≠ 0) :
    (Pair α → K) ≃ₗ[K] (Pair α → K) where
  toFun := eigenCoordinates K
  invFun := fromEigenCoordinates K
  left_inv f := by
    funext ⟨a, b⟩
    rcases lt_trichotomy a b with hab | rfl | hba
    · simp only [eigenCoordinates, fromEigenCoordinates, swapPair,
        ne_of_lt hab, Ne.symm (ne_of_lt hab), ite_false, hab, ite_true, if_true,
        not_lt_of_ge (le_of_lt hab)]
      field_simp
      ring
    · simp [eigenCoordinates, fromEigenCoordinates]
    · simp only [eigenCoordinates, fromEigenCoordinates, swapPair,
        ne_of_lt hba, Ne.symm (ne_of_lt hba), ite_false, hba, ite_true, if_true,
        not_lt_of_ge (le_of_lt hba)]
      field_simp
      ring
  right_inv c := by
    funext ⟨a, b⟩
    rcases lt_trichotomy a b with hab | rfl | hba
    · simp only [eigenCoordinates, fromEigenCoordinates, swapPair,
        ne_of_lt hab, Ne.symm (ne_of_lt hab), ite_false, hab, ite_true, if_true,
        not_lt_of_ge (le_of_lt hab)]
      field_simp
      ring
    · simp [eigenCoordinates, fromEigenCoordinates]
    · simp only [eigenCoordinates, fromEigenCoordinates, swapPair,
        ne_of_lt hba, Ne.symm (ne_of_lt hba), ite_false, hba, ite_true, if_true,
        not_lt_of_ge (le_of_lt hba)]
      field_simp
      ring
  map_add' f g := by
    funext x
    simp only [eigenCoordinates, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c f := by
    funext x
    simp only [eigenCoordinates, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

def eigenvalue (i : Pair α) : K := if i.1 ≤ i.2 then 1 else -1

variable [Fintype α]

def localKernel (x i : Pair α) : K :=
  fromEigenCoordinates K (Pi.single i 1) x

def localDualKernel (i x : Pair α) : K :=
  eigenCoordinates K (Pi.single x 1) i

/-- The matrix-entry formula for a finite linear map, used to verify both kernel inverses. -/
theorem linearMap_apply_eq_sum {β γ : Type*} [Fintype β] [DecidableEq β]
    (L : (β → K) →ₗ[K] (γ → K)) (f : β → K) (x : γ) :
    L f x = ∑ i, L (Pi.single i 1) x * f i := by
  have hf : (∑ i, f i • (Pi.single i (1 : K) : β → K)) = f := by
    funext j
    simp [Pi.single_apply]
  calc
    L f x = L (∑ i, f i • (Pi.single i (1 : K) : β → K)) x := by rw [hf]
    _ = ∑ i, L (Pi.single i 1) x * f i := by
      simp [map_sum, map_smul, mul_comm]

theorem localKernel_inverse (h2 : (2 : K) ≠ 0) (x y : Pair α) :
    (∑ i, localKernel K x i * localDualKernel K i y) = if x = y then 1 else 0 := by
  have h := linearMap_apply_eq_sum K (eigenCoordinateEquiv K h2).symm.toLinearMap
    (eigenCoordinateEquiv K h2 (Pi.single y 1)) x
  calc
    _ = (eigenCoordinateEquiv K h2).symm
        (eigenCoordinateEquiv K h2 (Pi.single y 1)) x := h.symm
    _ = (Pi.single y (1 : K) : Pair α → K) x :=
      congrFun ((eigenCoordinateEquiv K h2).symm_apply_apply (Pi.single y 1)) x
    _ = (if x = y then 1 else 0) := by simp [Pi.single_apply ]

theorem localDualKernel_inverse (h2 : (2 : K) ≠ 0) (i j : Pair α) :
    (∑ x, localDualKernel K i x * localKernel K x j) = if i = j then 1 else 0 := by
  have h := linearMap_apply_eq_sum K (eigenCoordinateEquiv K h2).toLinearMap
    ((eigenCoordinateEquiv K h2).symm (Pi.single j 1)) i
  calc
    _ = (eigenCoordinateEquiv K h2)
        ((eigenCoordinateEquiv K h2).symm (Pi.single j 1)) i := h.symm
    _ = (Pi.single j (1 : K) : Pair α → K) i :=
      congrFun ((eigenCoordinateEquiv K h2).apply_symm_apply (Pi.single j 1)) i
    _ = (if i = j then 1 else 0) := by simp [Pi.single_apply ]

end SubexponentialSAT.Subexp.LocalSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TensorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Tensor eigenbases for the multicolor register swap

The finite change of basis is constructed from invertible local kernels. This
module then specializes it to the actual register swap and transports it to the
joint fiber of universal types; multiplicities count those actual basis labels.
-/

namespace SubexponentialSAT.Subexp.TensorSpectrum

open scoped BigOperators

section ProductKernel

variable (K : Type*) [Field K]
variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- Pointwise tensor product of local change-of-basis entries. -/
def productKernel (A : β → β → K) (x y : ι → β) : K :=
  ∏ l, A (x l) (y l)

end ProductKernel

section Multiplicities

open SubexponentialSAT.SubexpSwapMultiplicity

variable {r Q Δ : ℕ}

/-- Integer multiplicity of all untouched registers, including the pinned slot color. -/
def spectatorCard (r Q Δ : ℕ) : ℕ := (r - 1) * r ^ (Q * (Δ - 1))

end Multiplicities

end SubexponentialSAT.Subexp.TensorSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite head sum is exactly the actual numbered completion numerator. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Numbered
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def headTerms (vertices : List V) : List (ScoreTerm I V Q) :=
  (List.finRange Q).flatMap (fun t =>
    (vertices.product vertices).map (fun p => Sum.inr (t, p.1, p.2)))

end Numbered
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit positive denominator and bit bounds for the two rational weights. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram

def Weights.ofFractions (xn xd yn yd : ℕ) (hxd : 0 < xd) (hyd : 0 < yd) : Weights where
  incidence := yn^2 * xd^2
  head := xn^2 * yd^2
  denominator := xd^2 * yd^2
  denominator_pos := Nat.mul_pos (pow_pos hxd _) (pow_pos hyd _)

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScopeBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Retain the final memory invariant of the checked sequential loop. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.Subexp

theorem assign_length {A : Type*} (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (n : ℕ) (fixed : List A) :
    (NaturalAssignment.assignNat a tail evaluate n fixed).length=n+fixed.length := by
  induction n generalizing fixed with
  | zero => simp [NaturalAssignment.assignNat]
  | succ n ih => simp only [NaturalAssignment.assignNat,ih,List.length_cons]; omega

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native-scope specialization of the fixed weighted packing selector. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.Packing

def weights (n s M r q : ℕ) (hs : 0 < s) (hr : 0 < r) (hq : 0 < q) : Weights :=
  Weights.ofFractions M (s*q^2) n (2*r)
    (Nat.mul_pos hs (pow_pos hq 2)) (Nat.mul_pos (by decide) hr)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.Subexp
open PackingIncidenceInput

structure Problem where
  scopes : List (List ℕ)
  n : ℕ
  mask : List Bool
  mask_le : mask.length ≤ n
  r : ℕ
  Q : ℕ
  s : ℕ
  hr : 0 < r
  hQ : 0 < Q
  hs : 0 < s

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end


