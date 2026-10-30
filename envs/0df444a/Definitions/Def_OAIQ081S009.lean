-- Prove2me | Definitions.Def_OAIQ081S009
-- name    : OAIQ081S009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:23:14.131094+00:00
-- url     : https://prove2.me/theorems/ab6dafb8-4b6c-4a1f-adca-09dfb4946aa8
-- title:
--   Definitions bundle OAIQ081S009 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 180 declarations of OpenAI's Lean: 150 definitions, 4 inductive types or structures and 26 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.tapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.flags`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.zeroRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.Row`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.acceptedCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.accepts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.best`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.mass`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.survivingCandidates`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.LoopPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.Ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.iter`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable.baseStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable.preparedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.bitFlag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.bitPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.bitRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.bitSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.lookupCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.lowBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.testCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visitBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.wordPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.wordRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.zeros`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.arrayPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.headBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.headIds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.mask`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.scanCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.scatter`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.write`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.zeroStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.assignmentEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.remainingScope` and 114 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawCall`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawTable`, `SubexponentialSAT_SqrtLog_HashSelectArgmin`, `SubexponentialSAT_SqrtLog_HashSelectCore`, `SubexponentialSAT_SqrtLog_HashSelectProgramCore`, `SubexponentialSAT_SqrtLog_HashSelectProgramLoop`, `SubexponentialSAT_SqrtLog_HashSelectSAT`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgram`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramFullTable`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramRun`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramTest`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramVisit`, `SubexponentialSAT_SqrtLog_HeadScatterProgram`, `SubexponentialSAT_SqrtLog_HeadScatterProgramInit`, `SubexponentialSAT_SqrtLog_HeadScatterProgramScan`, `SubexponentialSAT_SqrtLog_HeadScatterProgramSemantics`, `SubexponentialSAT_SqrtLog_HeadScatterProgramTyped`, `SubexponentialSAT_SqrtLog_HighIncidence`, `SubexponentialSAT_SqrtLog_HighIncidenceProgram`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramCutoff`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramMass`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramMassPreserve`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareOps`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramRank`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramRestrictionTotal`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramShift`, `SubexponentialSAT_SqrtLog_HornerProgram`, `SubexponentialSAT_SqrtLog_HornerProgramControl`, `SubexponentialSAT_SqrtLog_HornerProgramLoop`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramAdd`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramBounds`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsCapacity`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsMultiplier`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramCore`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMachine`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramProjection`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalarBasic`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramServices`, `SubexponentialSAT_SqrtLog_IdempotentCore`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramRepeat`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine`, `SubexponentialSAT_SqrtLog_IdempotentProgramAlgebra`, `SubexponentialSAT_SqrtLog_IdempotentProgramOutput`, `SubexponentialSAT_SqrtLog_IdempotentProgramRegisters`, `SubexponentialSAT_SqrtLog_IdempotentProgramTrace`, `SubexponentialSAT_SqrtLog_IdempotentTernary`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramHash`, `SubexponentialSAT_SqrtLog_SquarefreeSparseBounds`, `SubexponentialSAT_SubexpClauseMastersProgram`, `SubexponentialSAT_SubexpFactorCountSetup`, `SubexponentialSAT_SubexpHeadColorProgram`, `SubexponentialSAT_SubexpHornerControl`, `SubexponentialSAT_SubexpIncidencePlanPrimitives`, `SubexponentialSAT_SubexpIncidencePlanScan`, `SubexponentialSAT_SubexpIncidenceSlotProgram`, `SubexponentialSAT_SubexpLayoutFactorBounds`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_SubexpScopeCountSetup`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_SubexpSunflowerProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_SupportSelectionData`, `SubexponentialSAT_Subexp_TypeBitProgram`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S037`, `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S041`, `OAIQ081S042` and `OAIQ081S043`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

structure Algebra (A : Type*) where
  zero : A
  one : A
  add : A → A → A
  mul : A → A → A
  neg : A → A

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiteralChunkProgram
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

/-- A uniform polynomial bound in the literal's unary index and binary width. -/
def budget (width index : ℕ) : ℕ :=
  (9 * index + 9) + (index * (8 * index + 10) + 4) +
  100 * (width + index + 1) ^ 2 + 32 * (index + 1) * (index + 1) +
  (2 * (width + index) + 3) + (3 * (index + 1) + 3) + 8

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native lookup of the optional original marked clause. Local ports49/50
stage original masters705/706; source14 stages original formula700. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

def tapes (width modulus master shape out index flag clause ell pay : List Bool) : Fin 80 → List Bool :=
  fun i => if i=1 then width else if i=7 then modulus else if i=14 then master
    else if i=15 then shape else if i=48 then out else if i=49 then index
    else if i=50 then flag else if i=73 then clause else if i=72 then ell
    else if i=47 then pay else []

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One callback for the actual raw-row table. The original clause master,
word width, modulus and ring shape are persistent; all workspace is cleaned. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

def zeroRegs : Fin 11 → Bool := fun _ => false


end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct table adapter: raw clause-reference rows to deduplicated scope rows.
The original source table and all decoding parameters remain on their tapes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

def flags (rf : Fin 11 → Bool) (v p f : Bool) : Fin 11 → Bool := fun i =>
  if i=8 then v else if i=9 then p else if i=10 then f else rf i

@[simp] theorem flags_idem (rf : Fin 11 → Bool) (v p f : Bool) :
    flags (flags rf v p f) v p f=flags rf v p f := by
  funext i
  by_cases h8 : i=8 <;> by_cases h9 : i=9 <;> by_cases h10 : i=10 <;>
    simp [flags,h8,h9,h10]

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact natural-valued mass for finite sparse-hash selection.
The row semantics are abstract here; no evaluator is assumed computable
from this definition at the target cost. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

variable {X R I : Type*}

def accepts (rowAccept : R → X → Bool) (rows : List R) (x : X) : Bool :=
  rows.all (fun r => rowAccept r x)

@[simp] theorem accepts_nil (rowAccept : R → X → Bool) (x : X) :
    accepts rowAccept [] x = true := rfl

@[simp] theorem accepts_cons (rowAccept : R → X → Bool) (r : R)
    (rows : List R) (x : X) :
    accepts rowAccept (r :: rows) x = (rowAccept r x && accepts rowAccept rows x) := rfl

def mass [Fintype X] (rowAccept : R → X → Bool) (weight : X → ℕ)
    (rows : List R) : ℕ :=
  ∑ x, if accepts rowAccept rows x then weight x else 0

def survivingCandidates [Fintype I] (rowAccept : R → X → Bool)
    (family : I → R) (x : X) : ℕ :=
  ∑ i, if rowAccept (family i) x then 1 else 0

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectArgmin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An executable finite argmin. Scores are natural numbers, not unary
word lengths. The companion trace records both score calls at every scan
step, including repeated calls and all losing candidates. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

variable {R : Type*}

def best (score : R → ℕ) (seed : R) : List R → R
  | [] => seed
  | r :: rs => best score (if score r < score seed then r else seed) rs

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port binary argmin calls and a parser for unevaluated candidate
payloads. The scores are absent from the input encoding. All supplied commands
are actual finite programs; semantic scores are never atomic instructions. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

structure Ports (r s : ℕ) where
  register : Fin 8 → Fin r
  stack : Fin 9 → Fin s
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary-counter controller for K greedy rounds. The round command
must supply a paid actual execution; the counter is runtime stack data. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

structure LoopPorts (r s : ℕ) where
  value : Fin r
  present : Fin r
  counter : Fin s
  value_ne_present : value ≠ present

abbrev iter {α : Type*} (next : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => iter next n (next x)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectSAT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Instantiation of the finite selector with actual clause violations.
This is a conditional composition theorem: exact evaluation and initial
coverage are explicit hypotheses, not an assumed SAT oracle. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

abbrev Row (m : ℕ) := Fin m → ZMod 3

def acceptedCount {X R : Type*} [Fintype X] (rowAccept : R → X → Bool)
    (rows : List R) : ℕ := ∑ x, if accepts rowAccept rows x then 1 else 0

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control candidate scoring

Score records are accumulated as reversed serialized bytes and reversed once
at the end, so output score order agrees with the input candidate order.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreProgram

def resetValues {r : ℕ} (indices : List (Fin r)) (regs : Fin r → Bool) : Fin r → Bool :=
  indices.foldl (fun rs i => Function.update rs i false) regs

theorem resetValues_apply {r : ℕ} (indices : List (Fin r)) (regs : Fin r → Bool)
    (i : Fin r) : resetValues indices regs i = if i ∈ indices then false else regs i := by
  induction indices generalizing regs with
  | nil => simp [resetValues]
  | cons j rest ih =>
      change resetValues rest (Function.update regs j false) i = _
      rw [ih]
      by_cases hi : i = j <;> by_cases hr : i ∈ rest <;>
        simp_all []

def lowRegisters (i : Fin 13) : Fin 16 := Fin.castAdd 3 i

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHeadColorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Read a head color from its physical one-hot type encoding

Ports 0, 1, and 2 hold the flat type bytes, unary position, and unary color
width. The fixed array reader preserves these inputs. A five-label bit loop
counts the false prefix of the selected one-hot word; the remaining suffix is
cleared. Only output port 3 changes, and scratch ports 4--9 are restored.
-/

namespace SubexponentialSAT.SubexpHeadColorProgram

def readPorts : Fin 8 → Fin 10 := ![0,5,4,2,6,7,8,9]

end SubexponentialSAT.SubexpHeadColorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFactorCountSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving setup of a factor-local assignment count

The fixed program copies a unary arity, counts the copy into a binary exponent,
and invokes the actual preserving power routine.  The base and unary arity are
retained verbatim.  The number of bits in either input is runtime data.
-/

namespace SubexponentialSAT.SubexpFactorCountSetup

def lengthRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def lengthPorts : Fin 3 → Fin 13 := ![4, 2, 5]

def countBudget (arity : ℕ) : ℕ :=
  (7 * arity + 6) + (arity * (8 * arity + 10) + 3)

end SubexponentialSAT.SubexpFactorCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSunflowerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs used by sunflower candidate checking

Runtime clause counts and widths remain encoded stack data. The first
primitive counts framed records; it is an actual finite instruction table,
with a trace theorem, rather than a semantic list-length instruction.
-/
namespace SubexponentialSAT.SubexpSunflowerProgram

namespace CountRecords

def loopSteps (records : List (List Bool)) : ℕ :=
  4 * (records.map List.length).sum + 6 * records.length + 5

end CountRecords

end SubexponentialSAT.SubexpSunflowerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

def counterReg (i : Fin 2) : Fin 8 := i.castAdd 6
def counterStack : Fin 2 → Fin 15 := ![14, 2]

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeBitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed seven-label routine reads a runtime-indexed bit and clears its
two inputs. An out-of-range read returns false, as `List.getD` does. -/

namespace SubexponentialSAT.Subexp.TypeBitProgram

def cost : List Bool → List Bool → ℕ
  | [], bits => 2 * bits.tail.length + 6
  | _ :: rest, bits => 3 + cost rest bits.tail

end SubexponentialSAT.Subexp.TypeBitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SupportSelectionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordered support records selected from the actual packing inverse. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

abbrev unary (n : ℕ) : List Bool := List.replicate n true

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical head-identifier selection uses the original ambient word array.
No packing-coverage predicate participates in the scan. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT

abbrev unary (n : ℕ) := List.replicate n true
abbrev zeros (n : ℕ) := List.replicate n false

def wordRegs : Fin 5 → Fin 16 := Fin.castAdd 11
def wordPorts : Fin 10 → Fin 64 := ![33,39,38,16,17,36,18,19,20,21]

def lookupCost (j W : ℕ) := j*(14*W+17)+15*W+22

def bitFlag (low : Bool) : Fin 16 := if low then 6 else 4
def bitSource (low : Bool) : Fin 64 := if low then 13 else 36
def bitRegs (low : Bool) : Fin 3 → Fin 16 := ![0,1,bitFlag low]
def bitPorts (low : Bool) : Fin 2 → Fin 64 := ![12,bitSource low]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT

def testCost (index low bitIndex word : List Bool) (W : ℕ) : ℕ :=
  (7*index.length+5)+(7*low.length+5)+Subexp.TypeBitProgram.cost index low+
    lookupCost index.length W+(7*bitIndex.length+5)+Subexp.TypeBitProgram.cost bitIndex word

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramVisit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT

def visitBound (j W L z : ℕ) := lookupCost j W+22*j+9*L+10*z+2*W+43

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT

def budget (n W L z : ℕ) := n*(visitBound n W L z+2)+7*n+26

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime scatter of head bits into the original ambient coordinate order.
Coordinate identifiers are framed unary words; array replacement is a genuine
runtime scan. No coordinate permutation is compiled into the instruction table. -/
namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

open SubexponentialSAT

abbrev unary (n : ℕ) := List.replicate n true

def arrayPorts : Fin 8 → Fin 13 := ![0,4,3,5,6,7,8,9]

def write (mask : List Bool) (j : ℕ) (bit : Bool) : List Bool :=
  mask.take j ++ bit :: mask.drop (j+1)

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramInit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT

def zeroStacks (n : ℕ) (stk : Fin 13 → List Bool) : Fin 13 → List Bool :=
  Function.update (Function.update stk 3 []) 0 (List.replicate n false ++ stk 0)

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT

/-- Semantic specification of the physically executed sequence of writes. -/
def scatter : List ℕ → List Bool → List Bool → List Bool
  | j::js, b::bs, mask => scatter js bs (write mask j b)
  | _, _, mask => mask

def scanCost : List ℕ → ℕ
  | [] => 1
  | j::js => 30*j+55+scanCost js

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

/-- A full ambient mask. The empty head list still returns n zero bits. -/
def mask (n : ℕ) (js : List ℕ) (bits : List Bool) : List Bool :=
  scatter js bits (List.replicate n false)

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpParameterProgram
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

/-! ## Consume a most-significant zero prefix and the leading one -/

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

theorem extend_equiv {α β γ : Type*} (e : α ≃ β) (f : α → γ) (frame : β → γ) :
    Function.extend e f frame = fun b => f (e.symm b) := by
  funext b
  simp

def logBound (L : ℕ) : ℕ := L * (8 * L + 16) + 12

theorem logBound_eq (L : ℕ) : logBound L = 8 * L ^ 2 + 16 * L + 12 := by
  unfold logBound
  ring

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramTyped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT

variable {n h : ℕ}

def headIds (head : Fin h → Fin n) : List ℕ := List.ofFn (fun i => (head i).val)
def headBits (x : Fin h → Bool) : List Bool := List.ofFn x

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT

def lowBits {n : ℕ} (low : Fin n → Bool) : List Bool := List.ofFn low

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramFullTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable
open SubexponentialSAT

def baseStacks (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Fin 64 → List Bool :=
  fun i => if i=30 then unary n else if i=31 then low else if i=32 then unary z
    else if i=33 then rows.flatten else if i=38 then unary W else []

def preparedStacks (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Fin 64 → List Bool :=
  Function.update (Function.update (baseStacks n rows low W z) 39 (unary n)) 0 [false]

def budget (n totalRows W L z : ℕ) := n*(visitBound totalRows W L z+2)+7*n+26

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer high-incidence cutoff and disjoint branching on original coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def totalScope (scope : E → Finset V) : ℕ := ∑ e, (scope e).card

def remainingScope (H : Finset V) (scope : E → Finset V) (e : E) :
    Finset {v : V // v ∉ H} := Finset.subtype (fun v => v ∉ H) (scope e)

def glue (H : Finset V) (a : H → Bool) (b : {v : V // v ∉ H} → Bool) : V → Bool :=
  fun v => if hv : v ∈ H then a ⟨v, hv⟩ else b ⟨v, hv⟩

def assignmentEquiv (H : Finset V) :
    ((H → Bool) × ({v : V // v ∉ H} → Bool)) ≃ (V → Bool) where
  toFun ab := glue H ab.1 ab.2
  invFun x := (fun v => x v.val, fun v => x v.val)
  left_inv := by
    intro ab
    apply Prod.ext <;> funext v <;> simp [glue, v.property]
  right_inv := by
    intro x
    funext v
    simp [glue]

theorem remaining_variable_count (H : Finset V) :
    Fintype.card {v : V // v ∉ H} = Fintype.card V - H.card := by
  calc
    _ = Fintype.card V - Fintype.card H := Fintype.card_subtype_compl (fun v => v ∈ H)
    _ = _ := by rw [Fintype.card_coe]

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary-counter and record-emission instructions for incidence plans. -/
namespace SubexponentialSAT.SubexpIncidencePlanPrimitives

def emitReg : Fin 3 → Fin 10 := ![0, 1, 4]
def emitStack : Fin 4 → Fin 10 := ![6, 3, 7, 1]

end SubexponentialSAT.SubexpIncidencePlanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete scope-membership subroutine for incidence-plan preparation.
The reversed scope record occupies stack 8 and the reversed query stack 2.
Stacks 0,1,3,4 are empty work ports; all remaining stacks are framed.
-/
namespace SubexponentialSAT.SubexpScopeMembershipProgram

def stackMap : Fin 8 → Fin 10 := ![5, 2, 6, 0, 1, 3, 4, 7]

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite scan of encoded scopes. No slot map is supplied as input:
the local slot order is the encounter order of incident factors. -/
namespace SubexponentialSAT.SubexpIncidencePlanScan

open SubexpIncidencePlanPrimitives

abbrev unary (n : ℕ) : List Bool := List.replicate n true

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

def maskReg (i : Fin 4) : Fin 10 := i.castAdd 6
def maskPort : Fin 4 → Fin 13 := ![4,5,6,7]

def scanPort : Fin 10 → Fin 13 := ![4,5,6,8,9,10,7,11,12,3]

def cleanupPorts : List (Fin 13) := [6,10,11]

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical high-incidence selection from supplied explicit scopes

The input is a framed list of scopes with original natural-number identifiers.
Every query invokes the audited source-preserving record/membership scan. The
cutoff is a supplied unary integer in this module; no arithmetic or translation
from clauses to scopes is silently performed. The fixed program appends the
strict comparison bit and advances the original-coordinate counter.
-/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev unary (n : ℕ) := List.replicate n true

def countPorts : Fin 13 → Fin 16 := Fin.castAdd 3

def compareRegs : Fin 4 → Fin 10 := Fin.castAdd 6
def comparePorts : Fin 2 → Fin 16 := ![3, 4]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime Boolean branch initialization and exhaustive odometer traces.
The only parameter in the enumeration command is its fixed real callback.
The high dimension is data, not finite control. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches
@[simp] theorem update_out (a b c : List Bool) :
    Function.update (![a, b] : Fin 2 → List Bool) 1 c = ![a, c] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))
@[simp] theorem update_input (a b c : List Bool) :
    Function.update (![a, b] : Fin 2 → List Bool) 0 c = ![c, b] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

def prepend : ℕ → List Bool → List Bool
  | 0, out => out
  | h+1, out => true :: true :: false :: false :: prepend h out

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual runtime multiplication and ceiling division for the high-incidence
integer threshold. Inputs are binary S,t,n; the output is binary ceil(S*t/n).
Counting S from scope records and converting the result to unary are separate
physical frontend obligations, not operations hidden in this specification. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff

def work : Fin 5 ↪ Fin 12 where
  toFun i := ⟨7 + i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def ceilingPorts : Fin 8 → Fin 12 := ![4, 7, 8, 9, 10, 2, 3, 5]

def bound (mass scale dimension : List Bool) :=
  100 * (mass.length + scale.length + 1)^2 +
    500 * (mass.length + scale.length + dimension.length + 2)^2 + 1

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual two-level record scan counting explicit scope entries. The ghost
payload decoder occurs only in the loop specification; the executable callback
uses the existing physical record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
def parserRegs (regs : Fin 5 → Bool) (t p f : Bool) :=
  Function.update (Function.update (Function.update regs 2 t) 3 p) 4 f

def registers : Fin 2 → Fin 5 := Fin.castAdd 3
def counterPorts : Fin 2 → Fin 4 := ![3, 2]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseMastersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical preparation of the shared clause-factor masters

Four preserved binary input words supply the declared variable count, chunk
width, field modulus, and chunk count. Copies of the three counts are converted
by the checked binary-to-unary program. The checked full-shape capture then
builds the padded-array shape. No desired shape is an input assumption.

The modulus-width shape is a physical copy of the modulus word: its consumers
use its length, not its bits. The other two copies supply the binary chunk
width and field modulus at the clause-family's own persistent ports.
-/

namespace SubexponentialSAT.SubexpClauseMastersProgram

def unaryPorts (dst : Fin 14) : Fin 3 → Fin 14 := ![11, dst, 12]

end SubexponentialSAT.SubexpClauseMastersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMassPreserve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving wrapper around the actual nested record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve
def regs : Fin 5 → Fin 8 := Fin.castAdd 3
def stackPorts : Fin 4 → Fin 5 := ![4, 1, 2, 3]
def resetRegs (r : Fin 8 → Bool) :=
  Function.update (Function.update (Function.update r 2 false) 3 true) 4 false
def bound (source : List Bool) := 35 * (source.length + 1) + 4

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rank semantics for the native all-visits Boolean odometer. These maps are
proof-level reindexings; the machine changes its physical tuple in place. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank
open scoped BigOperators

def reindex {H : Type*} {h : ℕ} (order : Fin h ≃ H) : (Fin h → Bool) ≃ (H → Bool) where
  toFun a v := a (order.symm v)
  invFun b i := b (order i)
  left_inv := by intro a; funext i; simp
  right_inv := by intro b; funext v; simp

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical merge of high and free Boolean assignments in original order.
This routine never renames a variable or drops an unused coordinate. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

def selected (choice : Bool) : List Bool → List Bool → List Bool
  | b :: bs, x :: xs => if b = choice then x :: selected choice bs xs else selected choice bs xs
  | _, _ => []

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask traverses original coordinates in descending order.
This explicit order, rather than an arbitrary finite-type equivalence,
identifies each odometer position with its actual original variable. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

def coordinates (n : ℕ) : List (Fin n) := (List.finRange n).reverse

def highCoordinates {n : ℕ} (H : Finset (Fin n)) : List (Fin n) :=
  (coordinates n).filter (fun v => decide (v ∈ H))

theorem highCoordinates_nodup {n : ℕ} (H : Finset (Fin n)) :
    (highCoordinates H).Nodup := by
  exact (List.nodup_reverse.mpr (List.nodup_finRange n)).filter _

@[simp] theorem mem_highCoordinates {n : ℕ} (H : Finset (Fin n)) (v : Fin n) :
    v ∈ highCoordinates H ↔ v ∈ H := by
  simp [highCoordinates, coordinates]

def rawOrder {n : ℕ} (H : Finset (Fin n)) : Fin (highCoordinates H).length ≃ H :=
  (List.Nodup.getEquiv (highCoordinates H) (highCoordinates_nodup H)).trans
    (Equiv.subtypeEquivRight (mem_highCoordinates H))

@[simp] theorem highCoordinates_length {n : ℕ} (H : Finset (Fin n)) :
    (highCoordinates H).length = H.card := by
  simpa using Fintype.card_congr (rawOrder H)

def highOrder {n : ℕ} (H : Finset (Fin n)) : Fin H.card ≃ H :=
  (finCongr (highCoordinates_length H).symm).trans (rawOrder H)

theorem coordinates_stream (n : ℕ) (x : Fin n → Bool) :
    (coordinates n).map x = (List.ofFn x).reverse := by
  simp only [coordinates, List.map_reverse, List.ofFn_eq_map]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed ports for the physical high-incidence prefix. Each operation below
is a genuine call to an already verified finite program. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
def reg8 : Fin 8 → Fin 10 := Fin.castAdd 2
def reg3 : Fin 3 → Fin 10 := Fin.castAdd 7

def countPorts : Fin 15 → Fin 32 := ![24, 0, 1, 3, 4, 21, 5, 6, 7, 8, 9, 10, 11, 12, 22]
def massPorts : Fin 5 → Fin 32 := ![0, 21, 18, 22, 23]
def binaryPorts : Fin 13 → Fin 32 := ![24, 18, 19, 25, 21, 22, 3, 4, 5, 6, 7, 8, 9]
def cutoffPorts : Fin 12 → Fin 32 := ![19, 17, 16, 24, 25, 20, 26, 27, 28, 29, 30, 31]
def unaryPorts : Fin 14 → Fin 32 := ![20, 13, 3, 4, 5, 6, 7, 8, 9, 10, 11, 21, 22, 23]
def fuelPorts : Fin 14 → Fin 32 := ![16, 15, 3, 4, 5, 6, 7, 8, 9, 10, 11, 21, 22, 23]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical preparation from explicit scopes and binary n,t.
The input contains neither scope counts, mass, cutoff, nor unary loop fuel.
All are computed by fixed finite programs. The output mask retains all n
original coordinates and is in descending original-coordinate order. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
def mass (scopes : List (List ℕ)) := (scopes.map List.length).sum
def scanPorts : Fin 16 → Fin 32 := Fin.castAdd 16

def unarySized (value size : ℕ) := 7 * size + 5 + 32 * (value + 1) * (size + 1) + 1

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestrictionTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Every correctly sized pair of branch streams is accepted by the actual
merge program, and the resulting original-coordinate assignment is unique. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

def merge : List Bool → List Bool → List Bool → List Bool
  | [], _, _ => []
  | true :: mask, high, low => high.headD false :: merge mask high.tail low
  | false :: mask, high, low => low.headD false :: merge mask high low.tail

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original-coordinate high-value vector. The existing merger reads
false from its empty low stream, so no high-ID producer or zero-padding oracle
is required. It consumes the mask and high bits and emits the reversed vector. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

abbrev zeroMerge (mask high : List Bool) := merge mask high []

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHornerControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed streaming control for dense Horner evaluation. Arithmetic is a
separate actual command, instantiated by the flat quartic machine module. -/

namespace SubexponentialSAT.SubexpHornerControl

def backward {C : Type*} (encode : C → List Bool) (cs : List C) : List Bool :=
  cs.flatMap (fun c => (encode c).reverse)

abbrev fold {C : Type*} (step : C → C → C) : List C → C → C
  | [], a => a
  | c :: cs, a => fold step cs (step a c)

end SubexponentialSAT.SubexpHornerControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native streaming Horner control for arbitrary-width coefficient
representations. Arithmetic callbacks are finite commands with exact framed
traces. No loop bound or ring dimension occurs in the control table. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT

def stepValue {C : Type*} (mulOp addOp : C → C → C) (x a c : C) : C :=
  addOp (mulOp a x) c

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT

abbrev backward := @SubexpHornerControl.backward
abbrev fold := @SubexpHornerControl.fold

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native evaluation of a dynamically sized dense polynomial. Input
coefficients are in increasing degree order. Every other persistent stack is
preserved; the input stream and runtime counter are consumed. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT

def encodePolynomial {C : Type*} (encode : C → List Bool) (P : List C) : List Bool :=
  P.flatMap encode

def budget (n W Km Ka : ℕ) : ℕ := n * (Km + Ka + 59 * W + 49) + 9

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

/-- Used only as a finite counting envelope, never enumerated by the sparse operations. -/
def supportUniverse (vars : Finset V) (J : ℕ) : Finset (Finset V) :=
  vars.powerset.filter (fun s => s.card < J)

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native normalized addition for the persistent polynomial registers used
by the indicator Horner loop. Both operand copies and result storage are paid. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

def binaryResult (high : Fin 40 → List Bool) (result : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (Function.update high 11 []) 5 []) 11 result

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The integral Newton operation for lifting an idempotent through a
nilpotent ideal. No division, characteristic hypothesis, or field structure
is used in the iteration. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

variable {R S : Type*} [CommRing R] [CommRing S]

def newton (e : R) : R := 3 * e ^ 2 - 2 * e ^ 3

def iterate (e : R) : ℕ → R
  | 0 => e
  | n + 1 => newton (iterate e n)

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTernary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The three-residue idempotent coefficient family.  The only coefficient
assumption is a supplied inverse `u` of two. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial

variable {A O K : Type*} [CommRing A] [CommRing O] [CommRing K]

noncomputable def ternaryH : A[X] := X * (X - C 1) * (X - C 2)

def initialValue (u x : A) : A := u * (x - 1) * (x - 2)

@[simp] theorem initialValue_one (u : A) : initialValue u 1 = 0 := by
  simp [initialValue]

@[simp] theorem initialValue_two (u : A) : initialValue u 2 = 0 := by
  simp [initialValue]

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A direct H-adic multiplication table.  Entries are small integers computed
from bounded indices. No polynomial division or choice of a polynomial normal
form occurs in these executable definitions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators

variable {R : Type*} [CommRing R]

def hValue (x : R) : R := x * (x - 1) * (x - 2)

def hadicBasis (t : ℕ) (x : R) (i : Fin (3*t)) : R :=
  x ^ (i.val % 3) * hValue x ^ (i.val / 3)

/-- One explicitly indexed coefficient, omitted automatically past `3*t`. -/
def atomInteger (n : ℕ) (z : ℤ) {t : ℕ} (k : Fin (3*t)) : ℤ :=
  if k.val = n then z else 0

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

/-- The public output is `t` triples, in increasing H-adic order. -/
def digitIndex {t : ℕ} (s : Fin t) (a : Fin 3) : Fin (3*t) :=
  ⟨3*s.val+a.val, by have := s.isLt; have := a.isLt; omega⟩

def digitEquiv (t : ℕ) : Fin t × Fin 3 ≃ Fin (3*t) :=
  (finProdFinEquiv : Fin t × Fin 3 ≃ Fin (t*3)).trans (finCongr (Nat.mul_comm t 3))

@[simp] theorem digitEquiv_apply (t : ℕ) (s : Fin t) (a : Fin 3) :
    digitEquiv t (s,a) = digitIndex s a := by
  apply Fin.ext
  simp [digitEquiv, digitIndex, finProdFinEquiv]
  omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Algebraic invariant for the native descending Horner application. Each
coefficient digit has three entries, and no power is recomputed by expansion. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators

structure Triple (C : Type*) where
  a : C
  b : C
  c : C

variable {C A R : Type*} [CommRing A] [CommRing R]

def tripleValue (decode : C → A) (φ : A →+* R) (h : R) (v : Triple C) : R :=
  φ (decode v.a) + h * (φ (decode v.b) + h * φ (decode v.c))

def hornerValue (decode : C → A) (φ : A →+* R) (h g : R) : List (Triple C) → R
  | [] => 0
  | v::vs => tripleValue decode φ h v + g * hornerValue decode φ h g vs

def descendingValue (decode : C → A) (φ : A →+* R) (h g : R)
    (vs : List (Triple C)) (acc : R) : R :=
  vs.foldl (fun current v => tripleValue decode φ h v + g*current) acc

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Projection invariant for sparse Horner application. It permits the native
product to truncate after every multiplication while retaining exactly the
canonical projection of the complete indicator polynomial. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open LeafProgram

variable {C A R : Type*} [CommRing A] [CommRing R]

def tripleAlgebra (alg : Algebra R) (decode : C → R) (h : R) (v : Triple C) : R :=
  alg.add (alg.mul (alg.add (alg.mul (decode v.c) h) (decode v.b)) h) (decode v.a)

def descendingAlgebra (alg : Algebra R) (decode : C → R) (h g : R)
    (vs : List (Triple C)) (acc : R) : R :=
  vs.foldl (fun current v => alg.add (alg.mul current g) (tripleAlgebra alg decode h v)) acc

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime-sized cell repetition for idempotent preparation. The
source cell and unary count are data; the finite control is independent of
both lengths. Every source bit copied into the destination is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

def repeatRegisters : Fin 3 → Fin 8 := Fin.castAdd 5

def repeatPorts (source target scratch count : Fin 41) : Fin 4 → Fin 41 :=
  ![source, target, scratch, count]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed four-register Newton instruction stream and its exact execution
relation. Registers contain coefficient arrays at the intended instantiation.
This is an arithmetic-register trace, not yet a native Boolean-stack trace. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

abbrev Registers (C : Type*) := Fin 4 → C

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Finite record capacity for the actual normalized stored lists. The finite
universe is used for counting only; the program never enumerates it. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

def capacity {n : ℕ} (vars : Finset (Fin n)) (u J : ℕ) : ℕ :=
  u * J * (Squarefree.Sparse.supportUniverse vars J).card

def byteCapacity (n B d u J N : ℕ) : ℕ := N * (2*(n+u+J)+2*(d*B)+2)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalarBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scalar loading uses only checked stack primitives and constant formatting.
This definition boundary keeps its correctness independent of polynomial arithmetic. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

def injectPermutation : Equiv.Perm (Fin 96) :=
  (Equiv.swap 1 82).trans ((Equiv.swap 2 83).trans ((Equiv.swap 31 80).trans
    ((Equiv.swap 32 81).trans (Equiv.swap 37 39))))

def injectPorts (i : Fin 41) : Fin 96 := injectPermutation (Fin.castAdd 55 i)

def constantPorts (destination : Fin 96) : Fin 6 → Fin 96 :=
  ![89,90,91,81,92,destination]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native refinements for the scalar coefficient reader and injector.
All stacks outside the named outputs are preserved, including the ambient
low-product environment. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar

@[simp] theorem injectPort_1 : injectPorts 1 = 82 := by decide
@[simp] theorem injectPort_2 : injectPorts 2 = 83 := by decide
@[simp] theorem injectPort_17 : injectPorts 17 = 17 := by decide
@[simp] theorem injectPort_31 : injectPorts 31 = 80 := by decide
@[simp] theorem injectPort_32 : injectPorts 32 = 81 := by decide
@[simp] theorem injectPort_37 : injectPorts 37 = 39 := by decide

def injectionCost (dimension zeroLength wordLength : ℕ) : ℕ :=
  7*dimension+6+(dimension-1)*(7*zeroLength+7)+6+(7*wordLength+5)+1

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar


namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar

def scalarWork (destination : Fin 96) : List (Fin 96) :=
  [70,80,81,82,83,89,90,91,92,destination]


def wordCost (B dimension shapeLength : ℕ) : ℕ :=
  20*B+7*dimension+(dimension-1)*(7*B+7)+7*(dimension*B)+15*shapeLength+65

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native control for applying computed idempotent coefficients.
The input and output ABI is documented below. The semantic execution theorem
is a separate obligation; this module supplies concrete instructions only. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

def uKeyPorts : Fin 6 → Fin 96 := ![89,90,91,81,92,93]

def shiftPorts : Fin 15 → Fin 96 :=
  ![67,94,45,46,86,80,81,82,83,84,85,89,90,91,92]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramServices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native sparse arithmetic services shared by multiplier construction and Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

variable {p t n d : ℕ} [Fact p.Prime]

abbrev Data := Fin 40 → List Bool
abbrev Regs := Fin 8 → Bool


end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Native high-register services for the quadratic and Horner steps. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram
namespace Steps

variable {p t n d : ℕ} [Fact p.Prime]

/-- Workspace condition for the native scalar reader, expressed only in high memory. -/
def scalarReady (dst : Fin 40) (high : Data) : Prop :=
  ∀ i ∈ ([14,24,25,26,27,33,34,35,36,dst] : List (Fin 40)), high i=[]

end Steps
end SubexponentialSAT.SqrtLog.IdempotentApplyProgram


/-! Complete native evaluation of one degree-two coefficient digit. -/


/-! The native Horner accumulator update, including every move and cleanup. -/


/-! Measured descending Horner loop over the actual computed coefficient tape. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial envelopes for the concrete degree-two coefficient and
Horner machines. Every byte copy, dictionary scan, product and tape reversal
in the native cost definitions is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def wordEnvelope (B d n : ℕ) : ℕ :=
  20*B+7*d+d*(7*B+7)+7*(d*B)+15*n+65

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierKey. -/

/-! Construction and application of the U monomial by actual native instructions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


def keyPorts : Fin 6 → Fin 96 := ![89,90,91,81,92,93]

def mapPorts : Fin 15 → Fin 96 := ![67,94,45,46,86,80,81,82,83,84,85,89,90,91,92]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierArithmetic. -/

/-! Native construction of the cubic multiplier before its U shift. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def work (high : Data) (operand acc saved : List Bool) : Data :=
  Function.update (Function.update (Function.update high 5 operand) 11 acc) 29 saved

@[simp] theorem work_5 (high : Data) (a b c) : work high a b c 5=a := by simp [work]
@[simp] theorem work_11 (high : Data) (a b c) : work high a b c 11=b := by simp [work]
@[simp] theorem work_29 (high : Data) (a b c) : work high a b c 29=c := by simp [work]
@[simp] theorem work_other (high : Data) (a b c) (i : Fin 40)
    (h5:i≠5) (h11:i≠11) (h29:i≠29) : work high a b c i=high i := by
  simp [work,h5,h11,h29]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplier. -/

/-! Concrete preparation of the stored multiplier used by native Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def ready (high : Data) : Prop :=
  ∀ i ∈ ([5,11,14,24,25,26,27,28,29,30,31,33,34,35,36,37,38,39]:List (Fin 40)),high i=[]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplierSemantics. -/

/-! The multiplier produced by the native preparation is U H(H-1)(H-2). -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The setup charge includes scaling by cached minus one, normalized cubic
arithmetic, construction of the U key, and the physical key-map loop. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open Steps Multiplier

variable {p t n d : ℕ} [Fact p.Prime]

def scaleStepEnvelope (B d n u J : ℕ) : ℕ :=
  40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*(n+u+J)+57

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native production of the ternary modulus from runtime binary precision.
The output bytes themselves instantiate the prepared-modulus structure;
no canonical encoding or precomputed power is supplied to the machine. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

def modulusPorts : Fin 22 → Fin 41 :=
  ![0,31,5,1,2,3,4,6,7,8,9,10,11,13,14,15,16,18,19,20,21,22]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramRegisters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving storage for the fixed Newton register machine. Every
copy, replacement, and clearing operation is an actual finite bit program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

def arrayRegister (i : Fin 4) : Fin 41 := ⟨32+i.val, by omega⟩

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed register language for the twelve scalar cache/temporary words.
Its interpreter is actual finite code, not a unit-cost arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

abbrev Reg := Fin 12

def port : Reg → Fin 41 := ![17,18,19,20,21,23,24,25,27,28,30,31]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def lowRegs (i : Fin 16) : Fin 19 := Fin.castAdd 3 i

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def lowRegs (i : Fin 19) : Fin 22 := Fin.castAdd 3 i
def lowStacks (i : Fin 24) : Fin 28 := Fin.castAdd 4 i

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

def regs : Fin 8 → Fin 9 := Fin.castAdd 1

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLayoutFactorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical bounds for the actual clause-factor calls.  All envelopes are
polynomials in a common bound on the represented sizes and word lengths. -/

namespace SubexponentialSAT.SubexpLayoutConstructionBounds

def literalBound (S : ℕ) := SubexpLiteralChunkProgram.budget S S
def scopeCallbackBound (S : ℕ) := literalBound S + 5 * (S + 1) + 14

end SubexponentialSAT.SubexpLayoutConstructionBounds

end OAI.Algorithms
end


