-- Prove2me | Definitions.Def_OAIQ081S006
-- name    : OAIQ081S006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:22:55.259261+00:00
-- url     : https://prove2.me/theorems/b1ac047d-043b-4f48-b9c2-c175796720e4
-- title:
--   Definitions bundle OAIQ081S006 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 140 declarations of OpenAI's Lean: 105 definitions, 4 inductive types or structures, 1 instance and 30 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.bit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.cellRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.cellRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.cellStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.arithmeticWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.cellRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.cellStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.coefficientRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.coefficientValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.compareStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.explicitCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.explicitRowCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.frameStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.incrementStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.low3`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.low8`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.paddingStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.shiftStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.zeroVertexStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.binaryCell`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.cellStream`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.cellWeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.flattenMatrix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedCellCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedCellStream`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCheckRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCheckStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountsBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphInputMoves`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphInputSpan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWorkPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWorkRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.inputMoves` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CodeRowsProgramCode`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCost`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCounter`, `SubexponentialSAT_SqrtLog_CodeRowsProgramOffset`, `SubexponentialSAT_SqrtLog_CodeRowsProgramRead`, `SubexponentialSAT_SqrtLog_CodeRowsProgramShift`, `SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic`, `SubexponentialSAT_SqrtLog_CodeSearchProgramBounds`, `SubexponentialSAT_SqrtLog_CodeSearchProgramCallback`, `SubexponentialSAT_SqrtLog_CodeSearchProgramEnumeration`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphBounds`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCallback`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCounts`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphPrepare`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphWord`, `SubexponentialSAT_SqrtLog_CodeSearchProgramParity`, `SubexponentialSAT_SqrtLog_CodeSearchProgramPrepare`, `SubexponentialSAT_SqrtLog_CodeSearchProgramScan`, `SubexponentialSAT_SqrtLog_CodeSearchProgramSupport`, `SubexponentialSAT_SqrtLog_CodeSearchProgramWord`, `SubexponentialSAT_SqrtLog_CodeSearchProgramWordTail`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgram`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramArithmetic`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramCount`, `SubexponentialSAT_SqrtLog_CodeSetupCostNative`, `SubexponentialSAT_SqrtLog_CodeSetupCostPolynomial`, `SubexponentialSAT_SqrtLog_CodeSetupCostScale`, `SubexponentialSAT_SqrtLog_CodeSetupOuterCostStartupBounds`, `SubexponentialSAT_SqrtLog_CostAssemblyFinal`, `SubexponentialSAT_SqrtLog_CostAssemblyParameterValuesBasic`, `SubexponentialSAT_SqrtLog_CostAssemblyPolynomial`, `SubexponentialSAT_SqrtLog_CostAssemblyRingBounds`, `SubexponentialSAT_SqrtLog_HashParametersProgramFinal`, `SubexponentialSAT_SqrtLog_HashSelectTermination`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapCost`, `SubexponentialSAT_SqrtLog_LeafParametersProgram`, `SubexponentialSAT_SqrtLog_LeafParametersProgramCrudeBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_StatementScale`, `SubexponentialSAT_StackEncoding`, `SubexponentialSAT_SubexpEnumerationPayload`, `SubexponentialSAT_SubexpEnumerationProgram`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpGuardProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpPostfixGlobal`, `SubexponentialSAT_SubexpTupleRefinement`, `SubexponentialSAT_Subexp_MatrixCosts`, `SubexponentialSAT_Subexp_MatrixScalarProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S034`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S038`, `OAIQ081S040`, `OAIQ081S042` and `OAIQ081S043`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost.eventually_envelope_with_words`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_inverse_target`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost.eventually_envelope_with_words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_residual_enumeration_ambient_bound`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-width binary encodings of finite stack alphabets

The primary representation has no appended binary sentinel: the tape alphabet
is `Option Bool`, data bits are wrapped in `some`, and `none` is blank. Thus a
Boolean input stack can use width one and needs no initialization scan.

An explicit binary bottom-marker representation is also provided separately.
No theorem in this file assigns a Turing-machine cost to list operations.
-/

namespace SubexponentialSAT.StackEncoding

universe u

/-- An injective, positive, fixed-width code. -/
structure BlockCode (α : Type u) where
  width : ℕ
  width_pos : 0 < width
  block : α → List Bool
  length_block : ∀ a, (block a).length = width
  injective_block : Function.Injective block

/-- A width-one code for an alphabet explicitly equivalent to Boolean bits. -/
def codeOfBoolEquiv {α : Type u} (e : α ≃ Bool) : BlockCode α where
  width := 1
  width_pos := Nat.zero_lt_succ 0
  block a := [e a]
  length_block _ := rfl
  injective_block := by
    intro a b hab
    exact e.injective (by simpa using hab)

/-- Raw Boolean input is already encoded and needs no setup pass. -/
def boolCode : BlockCode Bool := codeOfBoolEquiv (Equiv.refl Bool)

theorem take_block_append {α : Type u} (c : BlockCode α) (a : α) (rest : List Bool) :
    (c.block a ++ rest).take c.width = c.block a :=
  List.take_left' (c.length_block a)

theorem drop_block_append {α : Type u} (c : BlockCode α) (a : α) (rest : List Bool) :
    (c.block a ++ rest).drop c.width = rest :=
  List.drop_left' (c.length_block a)

/-- Top-at-head concatenation of symbol blocks, with blank as the external
end marker. -/
def encodeDataStack {α : Type u} (c : BlockCode α) : List α → List Bool
  | [] => []
  | a :: s => c.block a ++ encodeDataStack c s

@[simp] theorem encodeDataStack_nil {α : Type u} (c : BlockCode α) :
    encodeDataStack c [] = [] := rfl

@[simp] theorem encodeDataStack_cons {α : Type u} (c : BlockCode α) (a : α)
    (s : List α) : encodeDataStack c (a :: s) = c.block a ++ encodeDataStack c s := rfl

@[simp] theorem encodeDataStack_append {α : Type u} (c : BlockCode α)
    (s t : List α) :
    encodeDataStack c (s ++ t) = encodeDataStack c s ++ encodeDataStack c t := by
  induction s with
  | nil => simp
  | cons a s ih => simp [ih, List.append_assoc]

@[simp] theorem length_encodeDataStack {α : Type u} (c : BlockCode α) (s : List α) :
    (encodeDataStack c s).length = s.length * c.width := by
  induction s with
  | nil => simp
  | cons a s ih => simp [c.length_block, ih, Nat.add_mul, Nat.add_comm]

@[simp] theorem take_width_cons {α : Type u} (c : BlockCode α) (a : α) (s : List α) :
    (encodeDataStack c (a :: s)).take c.width = c.block a :=
  take_block_append c a _

@[simp] theorem drop_width_cons {α : Type u} (c : BlockCode α) (a : α) (s : List α) :
    (encodeDataStack c (a :: s)).drop c.width = encodeDataStack c s :=
  drop_block_append c a _

@[simp] theorem boolCode_width : boolCode.width = 1 := rfl
@[simp] theorem boolCode_block (b : Bool) : boolCode.block b = [b] := rfl

@[simp] theorem encodeDataStack_boolCode (s : List Bool) : encodeDataStack boolCode s = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [ih]

@[simp] theorem encodeDataStack_codeOfBoolEquiv {α : Type u} (e : α ≃ Bool) (s : List α) :
    encodeDataStack (codeOfBoolEquiv e) s = s.map e := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      change [e a] ++ encodeDataStack (codeOfBoolEquiv e) s = e a :: s.map e
      rw [ih]
      rfl

end SubexponentialSAT.StackEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationPayload
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

/-- One field coordinate occupies this many binary cells. -/
def scalarWidth (p : ℕ) : ℕ := Nat.log 2 p + 1

end SubexponentialSAT.SubexpEnumerationPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTupleRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Representation and coverage of the fixed tuple program

The tuple program reverses its record order at each Cartesian expansion.
These theorems retain that actual order and show that it is a permutation of
the explicit coefficient-vector enumeration. Fixed-width injective encodings
then give uniqueness, not just coverage.
-/

namespace SubexponentialSAT.SubexpTupleRefinement

def encodeTuple {A : Type*} (code : StackEncoding.BlockCode A)
    {n : ℕ} (v : Fin n → A) : List Bool :=
  StackEncoding.encodeDataStack code (List.ofFn v)

end SubexponentialSAT.SubexpTupleRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control enumeration of the code-construction search spaces

The very same 83-label bit program enumerates all dimensions. Dimension is a
unary input stack, not the size of a generated instruction table. The output
is the actual framed list in the order produced by that program. Theorems
below charge the complete list, including candidates subsequently rejected.
Preparing the input dimension and fixed alphabet, and checking candidates,
are separate stages: this module does not pretend they are free.
-/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.SubexpTupleRefinement
open SubexponentialSAT.SubexpEnumerationPayload

def flattenMatrix {p rows cols : ℕ}
    (M : Fin rows → Fin cols → ZMod p) : Fin (rows * cols) → ZMod p :=
  fun i => M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed eight-label program counts nonzero two-bit cells. The input is
consumed and the count is emitted in unary. This is an actual support counter,
not a unit-cost application of `List.countP`. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open scoped BigOperators

abbrev cellStream : List (Bool × Bool) → List Bool
  | [] => []
  | (a,b) :: xs => a :: b :: cellStream xs

abbrev cellWeight : List (Bool × Bool) → ℕ
  | [] => 0
  | (a,b) :: xs => cellWeight xs + (if a || b then 1 else 0)

/-- The same operation on the five-bit scalar frames emitted by the audited
modular matrix program. Frame markers are physically consumed. -/
abbrev framedCellStream : List (Bool × Bool) → List Bool
  | [] => []
  | (a,b) :: xs => true :: a :: true :: b :: false :: framedCellStream xs

abbrev framedCellCost : List (Bool × Bool) → ℕ
  | [] => 3
  | (a,b) :: xs => (if a || b then 10 else 8) + framedCellCost xs

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numeric budgets for the actual scalar, row, and two-product traces. -/

namespace SubexponentialSAT.Subexp.MatrixProgram

def termBudget (B : ℕ) : ℕ := 12000 * (B + 1) ^ 2 + 30 * B + 26

end SubexponentialSAT.Subexp.MatrixProgram

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

def rowBudget (N B : ℕ) : ℕ :=
  N * (MatrixProgram.termBudget B + 2) + 7 * (N * (2 * B + 1)) + 21 * B + 27

def matrixBudget (m N B : ℕ) : ℕ := m * (rowBudget N B + 6 * B + 5) + 6

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScalarProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Scalar subroutines with the matrix checker's surrounding data preserved

These are calls to the actual finite modular-arithmetic instruction tables.
The eight additional ports carry vector streams, output, and runtime metadata.
-/

namespace SubexponentialSAT.Subexp.MatrixScalarProgram

open BinaryArithmetic

def servicePort (i : Fin 8) : Fin 16 := ⟨i.val, by omega⟩

def scalarStacks (x y modulus acc left right saved output zero input : List Bool) :
    Fin 16 → List Bool :=
  ![x, y, [], [], [], modulus, [], [], acc, [], left, right, saved, output, zero, input]

end SubexponentialSAT.Subexp.MatrixScalarProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native operations for adding a Cayley shift to a vertex word.
The Boolean mode chooses left or right incidence; shift frames are consumed
on both sides so each iteration advances exactly one local port. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

def cellRegisters : Fin 4 → Fin 8 := Fin.castAdd 4
def cellStacks (_ : Fin 1) : Fin 4 := 0

def cellRegs (regs : Fin 8 → Bool) (b : Bool) : Fin 8 → Bool :=
  ![false,true,b,false,regs 4,regs 5,regs 6,regs 7]

def bit (side v shift : Bool) : Bool := if side then v.xor shift else v

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

def result (side : Bool) (pairs : List (Bool × Bool)) : List Bool :=
  pairs.map fun p => bit side p.1 p.2

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixGlobal
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

/-- Four disjoint swaps; all other physical stack indices are unchanged. -/
def ports : Equiv.Perm (Fin 128) :=
  ((Equiv.swap 0 26).trans (Equiv.swap 1 28)).trans
    ((Equiv.swap 2 27).trans (Equiv.swap 3 29))

@[simp] theorem ports_zero : ports 0 = 26 := by decide
@[simp] theorem ports_one : ports 1 = 28 := by decide
@[simp] theorem ports_two : ports 2 = 27 := by decide
@[simp] theorem ports_three : ports 3 = 29 := by decide
@[simp] theorem ports_symm_26 : ports.symm 26 = 0 := by decide
@[simp] theorem ports_symm_28 : ports.symm 28 = 1 := by decide
@[simp] theorem ports_symm_27 : ports.symm 27 = 2 := by decide
@[simp] theorem ports_symm_29 : ports.symm 29 = 3 := by decide

end SubexponentialSAT.SubexpPostfixGlobal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
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

def parserRegister : Fin 2 → Fin 16 := Fin.castAdd 14
def parserStack (i : Fin 2) : Fin 128 := if i = 0 then 27 else 29

open SubexpPostfixGlobal

/-! ## Entry from arbitrary caller registers -/

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite table for sparse code rows. Runtime loops visit vertices,
local checks, and local ports only. The original clause count is used for a
binary comparison, never as the bound of a per-row scan. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

def low8 : Fin 8 → Fin 16 := Fin.castAdd 8
def low3 : Fin 3 → Fin 16 := Fin.castAdd 13

def arithmeticWork : Fin 5 ↪ Fin 64 where
  toFun i := ⟨28+i.val,by omega⟩
  inj' := by intro i j h; apply Fin.ext; have hh := congrArg Fin.val h; dsimp at hh; omega

def cellRegisters : Fin 4 → Fin 16 := ![0,1,8,9]
def cellStacks (_ : Fin 1) : Fin 64 := 0

def shiftStacks : Fin 4 → Fin 64 := ![1,17,19,18]

def compareStacks : Fin 8 → Fin 64 := ![21,4,33,34,35,36,37,38]

def paddingStacks : Fin 3 → Fin 64 := ![25,23,13]

def incrementStacks (src : Fin 64) : Fin 2 → Fin 64 := ![src,41]

def frameStacks : Fin 2 → Fin 64 := ![13,12]

/-- The supplied unary r shape creates the initial zero vertex word. -/
def zeroVertexStacks : Fin 3 → Fin 64 := ![25,26,2]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramOffset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BinaryArithmetic

def coefficientValue (a b : Bool) (m : ℕ) : ℕ := if b then 2*m else if a then m else 0

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

theorem low3_injective_p0 : Function.Injective low3 := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

def coefficientRegs (regs : Fin 16 → Bool) (a b : Bool) : Fin 16 → Bool :=
  Function.update (Function.update (Function.update (Function.update regs 0 false) 1 true) 8 a) 9 b

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

/-- Closed scalar operation count for one local row. -/
def explicitRowCost (r D b Ld Lm : ℕ) : ℕ :=
  7*D+35*(D*r)+D*(2000*(r+Ld+Lm+b+D+4)^2+2)+2*D+4*(D*b)+23

/-- Closed complete program bound, including source copies and final cleanup. -/
def explicitCost (r D t b Ld Lm : ℕ) : ℕ :=
  2^r*(2*(35*(t*D)+7*t+t*(explicitRowCost r D b Ld Lm+2)+13)+8*r+10)+13*r+18

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed support and unary comparison as framed subroutine calls. The port
maps are fixed finite maps; the lengths being scanned occur only on tapes. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

def scanRegisters : Fin 4 → Fin 8 := Fin.castAdd 4
def scanStacks (input output : Fin 18) : Fin 2 → Fin 18 := ![input,output]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramWordTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual decision tail for a proposed low-weight kernel word. It reads
both framed vectors, compares unary support with the runtime threshold, and
sets register 7 precisely on rejection. No semantic predicate is an opcode. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

def wordTailBudget (outputSize inputSize : ℕ) := 10 * outputSize + 14 * inputSize + 18

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A complete fixed-code test of one proposed short nonzero kernel word.
Matrix and word bytes, the row count, and the distance threshold are runtime
inputs. The protected stack 17 survives the call. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.Subexp
open scoped BigOperators

def matrixWordStacks : Fin 16 → Fin 18 := Fin.castAdd 2

def wordBudget (t D : ℕ) :=
  MatrixVectorProgram.matrixBudget t D 2 + wordTailBudget t D

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform bit lengths for every matrix and word, including rejected
candidates. These bounds do not depend on matrix entries or search success. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.Subexp

def wordInputSpan (t D d : ℕ) := 5 * (t * D) + 5 * D + t + d + 5

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpGuardProgram
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

open BinaryArithmetic

/-- The accumulator lives outside the comparator's eight work registers. -/
def workRegister (i : Fin 8) : Fin 9 := Fin.castAdd 1 i

def pairStack (j : Fin 3) (i : Fin 2) : Fin 6 := ⟨2 * j.val + i.val, by omega⟩


end SubexponentialSAT.SubexpGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationProgram
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

/-- Fixed counter ports, independent of all runtime binary values. -/
structure Ports (R S : ℕ) where
  register : Fin 3 ↪ Fin R
  current : Fin S
  remaining : Fin S
  scratch : Fin S
  current_ne_remaining : current ≠ remaining
  current_ne_scratch : current ≠ scratch
  remaining_ne_scratch : remaining ≠ scratch

variable {R S : ℕ}

def target (p : Ports R S) (useCurrent : Bool) : Fin S :=
  if useCurrent then p.current else p.remaining

theorem target_ne_scratch (p : Ports R S) (useCurrent : Bool) :
    target p useCurrent ≠ p.scratch := by
  cases useCurrent
  · exact p.remaining_ne_scratch
  · exact p.current_ne_scratch

def stackPorts (p : Ports R S) (useCurrent : Bool) : Fin 2 ↪ Fin S where
  toFun i := if i = 0 then target p useCurrent else p.scratch
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [target_ne_scratch p useCurrent,
      Ne.symm (target_ne_scratch p useCurrent)]

@[simp] theorem stackPorts_zero (p : Ports R S) (q : Bool) :
    stackPorts p q 0 = target p q := rfl
@[simp] theorem stackPorts_one (p : Ports R S) (q : Bool) :
    stackPorts p q 1 = p.scratch := rfl

end SubexponentialSAT.SubexpEnumerationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical input preparation for the local-code word checker. The
matrix, row count, and threshold are copied from persistent tapes. A parsed
reversed payload is transferred once, restoring the word's forward order. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

def wordRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def wordStacks : Fin 18 → Fin 24 := Fin.castAdd 6

def workPorts : List (Fin 24) := List.ofFn wordStacks

def inputMoves : List (Fin 24 × Fin 24) := [(18,11),(19,15),(20,16)]


end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramCallback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual reusable local-code callback: preparation, the complete word
predicate, then physical cleanup. All surrounding record-parser tapes and
flags are outside the invoked routine's ports. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

def callbackBudget (t D d : ℕ) :=
  (35 * (t * D) + 7 * t + 7 * d + 15 * D + 25) + wordBudget t D + 1 +
    18 * (2 * (wordInputSpan t D d + wordBudget t D) + 3)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The Walsh parity counter uses the same fixed matrix/support code as the
ternary checker. Its output is a physical unary counter, not an abstract sum. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.Subexp
open scoped BigOperators

def binaryCell (x : ZMod 2) : Bool × Bool := (decide (x = 1), false)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed bit-code for one Walsh query up to the scalar inequalities: compute
all dot products mod2, count their support, and recognize the zero character. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.Subexp
open scoped BigOperators

def graphCountsBudget (D r : ℕ) := MatrixVectorProgram.matrixBudget D r 2 + 10 * D + 10 * r + 9

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
def countRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def countStacks : Fin 3 → Fin 14 := ![13,3,12]

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

def work : Fin 5 ↪ Fin 14 where
  toFun i := ⟨i.val + 8, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
def lowRegisters : Fin 8 → Fin 9 := Fin.castAdd 1

def checkStacks : Fin 6 → Fin 14 := ![6,4,7,5,8,9]
def pairPorts (j : Fin 2) (i : Fin 2) : Fin 14 :=
  checkStacks (SubexpGuardProgram.pairStack (Fin.castAdd 1 j) i)

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

def good (q D h : ℕ) : Prop := q * D ≤ D + 2 * q * h ∧ 2 * q * h ≤ q * D + D
instance instDecidableGood (q D h : ℕ) : Decidable (good q D h) := by unfold good; infer_instance

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphWord
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

def graphCountRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def graphCountStacks : Fin 18 → Fin 29 := Fin.castAdd 11
def graphCheckRegisters : Fin 9 → Fin 16 := Fin.castAdd 7
def graphCheckStacks : Fin 14 → Fin 29 :=
  ![16,17,9,18,19,20,21,22,23,24,25,26,27,28]

def graphWordBudget (D r qlen Dlen : ℕ) := graphCountsBudget D r +
  700 * (2 * (qlen + Dlen + D) + 4)^2 + 5

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical input preparation for the Walsh character checker. The
matrix, row count, and two binary scalar words are copied from persistent tapes. A parsed
reversed payload is transferred once, restoring the word's forward order. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

def graphWorkRegisters : Fin 16 → Fin 16 := id
def graphWordStacks : Fin 29 → Fin 36 := Fin.castAdd 7

def graphWorkPorts : List (Fin 36) := List.ofFn graphWordStacks

def graphInputMoves : List (Fin 36 × Fin 36) := [(29,11),(30,15),(31,16),(32,17)]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.Subexp

def graphInputSpan (D r qlen Dlen : ℕ) := 5 * (D * r) + 5 * r + D + qlen + Dlen + 5

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCallback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual reusable local-code callback: preparation, the complete word
predicate, then physical cleanup. All surrounding record-parser tapes and
flags are outside the invoked routine's ports. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

def graphCallbackBudget (D r qlen Dlen : ℕ) :=
  (35 * (D * r) + 7 * D + 7 * qlen + 7 * Dlen + 15 * r + 31) +
    graphWordBudget D r qlen Dlen +
      29 * (2 * (graphInputSpan D r qlen Dlen + graphWordBudget D r qlen Dlen) + 3)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_StatementScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The exact square-root-logarithm runtime scale

These are numerical definitions and elementary lemmas only.  In particular,
this module supplies no SAT algorithm and makes no computational existence claim.
The logarithms in the target are natural logarithms, including at small inputs.
-/

namespace SubexponentialSAT.SqrtLog.Statement

noncomputable section

@[simp] theorem runtimeScale_zero : runtimeScale 0 = 0 := by
  simp [runtimeScale]

end

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectTermination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Entirely integer termination for the finite greedy selector. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

/-- `Nat.size` is binary length, so this cap uses no real logarithm. -/
def loopCap (n m : ℕ) : ℕ := 2 * (n + Nat.size m + 1)

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime parameter semantics. Every definition below uses natural
arithmetic; the executable refinements are separate from these specifications.
The original ambient dimension is retained through high-incidence branching. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

structure Input where
  ambient : ℕ
  freeCount : ℕ
  clauses : ℕ
  width : ℕ
  factors : ℕ
  occurrence : ℕ
  arity : ℕ
  incidences : ℕ
  deriving DecidableEq, Repr

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupCostScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform numerical envelope for the actual finite code searches.
Search dimensions occur only in the exponential factor. Encoded metadata
lengths remain in a separate fixed polynomial factor. -/
namespace SubexponentialSAT.SqrtLog.CodeSetupCost
open Filter
open scoped Topology

def exponent (C H : ℕ) : ℕ := 7*(C+(H+1)^2)+6

def envelope (C H W : ℕ) : ℕ := 3 ^ exponent C H * (W+1)^6

def degreeConstant (C A u : ℕ) : ℕ := 7*(C+(A+1)^2)+6+6*(u+1)

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupCostPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Positive arithmetic normal forms for the exhaustive-search budgets.
The native-budget identities are established separately against25's actual
definitions. Here no machine execution is postulated. -/
namespace SubexponentialSAT.SqrtLog.CodeSetupCost

def generation (alphabet width depth count : ℕ) : ℕ :=
  100*(alphabet+depth+800*(depth+1)*(count+1)*((depth+1)*(2*width+1)+1)+10)

def matrix2 (entries rows : ℕ) : ℕ := 108123*entries+86*rows+6

def localWord (entries rows cols : ℕ) : ℕ :=
  matrix2 entries rows+10*rows+14*cols+18

def localCallback (entries rows cols distance : ℕ) : ℕ :=
  (35*entries+7*rows+7*distance+15*cols+25)+localWord entries rows cols+1+
    18*(2*((5*entries+5*cols+rows+distance+5)+localWord entries rows cols)+3)

def localVerifier (entries rows cols distance words : ℕ) : ℕ :=
  4+words*(30*cols+localCallback entries rows cols distance+7)

def localCandidate (entries rows cols distance words : ℕ) : ℕ :=
  25*entries+9*((10*cols+2)*words+1)+15+
    3*localVerifier entries rows cols distance words

def localNumeric (alphabet width rows cols distance entries words matrices : ℕ) : ℕ :=
  generation alphabet width cols words+generation alphabet width entries matrices+
    (4+matrices*(30*entries+localCandidate entries rows cols distance words+9))+2

def graphWord (entries rows cols qlen Dlen : ℕ) : ℕ :=
  (matrix2 entries rows+10*rows+10*cols+9)+700*(2*(qlen+Dlen+rows)+4)^2+5

def graphCallback (entries rows cols qlen Dlen : ℕ) : ℕ :=
  (35*entries+7*rows+7*qlen+7*Dlen+15*cols+31)+graphWord entries rows cols qlen Dlen+
    29*(2*((5*entries+5*cols+rows+qlen+Dlen+5)+graphWord entries rows cols qlen Dlen)+3)

def graphVerifier (entries rows cols qlen Dlen chars : ℕ) : ℕ :=
  4+chars*(30*cols+graphCallback entries rows cols qlen Dlen+7)

def graphCandidate (entries rows cols qlen Dlen chars : ℕ) : ℕ :=
  25*entries+9*((10*cols+2)*chars+1)+15+
    3*graphVerifier entries rows cols qlen Dlen chars

def graphNumeric (alphabet width rows cols qlen Dlen entries chars tuples : ℕ) : ℕ :=
  generation alphabet width cols chars+generation alphabet width entries tuples+
    (4+tuples*(30*entries+graphCandidate entries rows cols qlen Dlen chars+9))+2

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupCostNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupCost
open Filter
open scoped Topology

def heightCoefficient (q : ℕ) : ℕ := 320000*(q+2)^3+q+4

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production hash-parameter program. The arithmetic, ABI, and cost proofs
are checked together; the former split module paths remain compatibility
imports of this file. -/

/-! Fixed native arithmetic for alphabet size, sparse-code distance parameter,
and selector round cap. Every operation is a proved finite Boolean program. -/


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/


/-! Polynomial step budget for the complete physical parameter setup. -/


/-! Exported fixed program and the selector's actual fourteen-port interface. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

def selectorRegisters : Fin 10 → Fin 16 := Fin.castAdd 6

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCrudeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

def magnitude (x : Input) : ℕ :=
  x.ambient+x.freeCount+x.clauses+x.occurrence+x.arity+x.factors+x.width+x.incidences+16

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BinaryArithmetic

def initialValues (x : Input) (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => x.ambient
  | 1 => x.freeCount
  | 2 => x.clauses
  | 3 => x.occurrence
  | 4 => x.arity
  | 5 => x.factors
  | 6 => x.width
  | 7 => x.incidences
  | _ => 0

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutReady -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupOuterCostStartupBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT

def startupConstant : ℕ := 100000000000000000000

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One closed cost expression with actual jet order, hash candidate count,
high-incidence branch count, and joint-signature/head enumeration. The two
remaining algorithmic interfaces are setup work and ordinary primitive work. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology

structure Resources where
  residual : ℕ
  clauses : ℕ
  initialOccurrence : ℕ
  localOccurrence : ℕ
  factors : ℕ
  branchVars : ℕ
  labelBase : ℕ
  /-- Rank used only to bound the number of attained signatures.  It need
  not be the number of rows stored or processed by the native program. -/
  labelRows : ℕ
  heads : ℕ
  headSize : ℕ
  setup : ℕ
  /-- Primitive coefficient/key costs; these use the actual retained rows. -/
  bits : ℕ
  /-- Includes actual matrix rows and payload dimensions, even when they
  exceed the rank parameter `labelRows`. -/
  ordinary : ℕ

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

/-- A closure predicate used only to certify that the displayed envelope is
a fixed polynomial, independently of the runtime model. -/
def Ordinary (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ S, f S ≤ C*(S+1)^d

theorem ordinary_const (a : ℕ) : Ordinary (fun _ => a) := by
  exact ⟨a,0,by simp⟩

theorem ordinary_id : Ordinary (fun S => S) := by
  exact ⟨1,1,by intro S; simp⟩

theorem ordinary_add {f g : ℕ → ℕ} (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun S => f S+g S) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨K,e,hg⟩ := hg
  refine ⟨C+K,d+e,?_⟩
  intro S
  have hd : (S+1)^d ≤ (S+1)^(d+e) := Nat.pow_le_pow_right (by omega) (by omega)
  have he : (S+1)^e ≤ (S+1)^(d+e) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ C*(S+1)^d+K*(S+1)^e := Nat.add_le_add (hf S) (hg S)
    _ ≤ C*(S+1)^(d+e)+K*(S+1)^(d+e) := by gcongr
    _ = _ := by ring

theorem ordinary_mul {f g : ℕ → ℕ} (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun S => f S*g S) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨K,e,hg⟩ := hg
  refine ⟨C*K,d+e,?_⟩
  intro S
  calc
    _ ≤ (C*(S+1)^d)*(K*(S+1)^e) := Nat.mul_le_mul (hf S) (hg S)
    _ = _ := by rw [pow_add]; ring

end SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameterValuesBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram


/-- A value-only bound: input padding has no effect on this quantity. -/
def grow (B : ℕ) : ℕ := (B+129)^2

def iter : ℕ → ℕ → ℕ
  | 0,B => B
  | n+1,B => iter n (grow B)

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open SubexpEnumerationPayload

def preparationConstant : ℕ := 200000

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/- Component: LeafRingSetupProgramScalar.lean -/

/-! The first concrete stage of ring setup.  Only the runtime binary
precision is supplied.  The generated scalar cache remains exposed while
the extension-ring table and constants are built.  The idempotent producer
later uses a separately framed preparation, with its own charged cost. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def scalarBudget (t inputWidth : ℕ) : ℕ :=
  2001 * (t + inputWidth + 2)^2 + 500000 * (3*t + inputWidth + 1)^3

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/- Component: LeafRingSetupProgramSearch.lean -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/

/-! Physical node generation and record framing at the ring-setup ports. -/

/-! Actual constant-vector and idempotent calls in the setup workspace. -/

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
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def privatePorts : List (Fin 640) :=
  (List.finRange 300).map fun i => ⟨340+i.val, by omega⟩

def outputPorts : List (Fin 640) :=
  [190,191,194,195,201,202,203,204,207,209,211,212,243,
   249,250,251,253,254,256,280,281,295,296,297,298,299,300,306]


end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

@[simp] theorem mem_privatePorts (i : Fin 640) : i∈privatePorts ↔ 340 ≤ i.val := by
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    change 340 ≤ 340+j.val
    omega
  · intro hi
    let j : Fin 300 := ⟨i.val-340,by omega⟩
    apply List.mem_map.mpr
    exact ⟨j,by simp,Fin.ext (by dsimp [j]; omega)⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram



namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def constantAliases : List (Fin 640 × Fin 640) :=
  [(280,190),(280,249),(207,250),(211,251)]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def nodesStartPorts : List (Fin 640) :=
  [256,612,613,614,615,616,617,618,619,620,621,622,623,625,628,639,
   295,297,298,299,306,300]

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

def searchCoefficient : ℕ :=
  IrreducibleSearchBootstrap.preparationConstant*16^4+531441*16^5+1

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

abbrev Word := List Bool

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end


