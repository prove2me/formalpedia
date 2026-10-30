-- Prove2me | Definitions.Def_OAIQ081S032
-- name    : OAIQ081S032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:29:31.146845+00:00
-- url     : https://prove2.me/theorems/5fb25243-a556-4995-90c5-d1745904dfb2
-- title:
--   Definitions bundle OAIQ081S032 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 118 declarations of OpenAI's Lean: 82 definitions, 1 inductive type or structure and 35 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.encode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.payloadCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.scopeRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.update`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.records`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.queryBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scanBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scopeBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.uniformQueryBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.accumulatorEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.addEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.applyEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.arithmeticEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.complementEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.mulEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.normalizeStepEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.prepareEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.quadraticEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.coefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.scalarCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Log.io`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.Op`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.Op.algebra`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.algebra`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.constants`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.finalCoefficients`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.halfStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.operands`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.tableRegister`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.arrayStacks` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_HighIncidenceProgram`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramCutoff`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramMask`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramMass`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramMassBounds`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramRestrictionTotal`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramScan`, `SubexponentialSAT_SqrtLog_HornerProgramServices`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramBounds`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsMultiplier`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrayStage`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramInput`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramLog`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramRepeat`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarSemantics`, `SubexponentialSAT_SqrtLog_IdempotentProgramAlgebra`, `SubexponentialSAT_SqrtLog_IdempotentProgramRegisters`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_SqrtLog_SquarefreeProgramSupport`, `SubexponentialSAT_SqrtLog_SquarefreeSparseProduct`, `SubexponentialSAT_StructuredProgram`, `SubexponentialSAT_SubexpIncidencePlanPrimitives`, `SubexponentialSAT_SubexpIncidencePlanScan`, `SubexponentialSAT_SubexpIncidenceSlotProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_SubexpScopeCountSetup`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_SubexpSunflowerProgram`, `SubexponentialSAT_Subexp_BlockCopyProgram`, `SubexponentialSAT_Subexp_IncidencePlanSpec`, `SubexponentialSAT_Subexp_UnaryCompare`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S004`, `OAIQ081S005`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S008` and `OAIQ081S009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S049`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062`, `OAIQ081S063`, `OAIQ081S064` and `OAIQ081S065`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S004
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008
import Definitions.Def_OAIQ081S009

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StructuredProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Structured programs compiled to finite bit instruction tables

The syntax has no unbounded natural-number registers or semantic-function
instructions. All data operations are the concrete Boolean-register and stack
instructions of BitProgram. Loops inspect a Boolean register, and changing data
never changes the finite generated instruction table.
-/

namespace SubexponentialSAT.StructuredProgram

open SubexponentialSAT.BitProgram

/-- Canonical stack input/output data, including all cleared work registers. -/
abbrev ioState {r s : ℕ} (stack : Fin s) (word : List Bool) : State r s :=
  ⟨fun _ => false, fun i => if i = stack then word else []⟩

end SubexponentialSAT.StructuredProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary-counter and record-emission instructions for incidence plans. -/
namespace SubexponentialSAT.SubexpIncidencePlanPrimitives

open BitProgram StructuredCalls

abbrev increment (dst : Fin 10) : Cmd 10 10 :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push dst 0)))

abbrev copy (src dst tmp : Fin 10) : Cmd 10 10 :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

end SubexponentialSAT.SubexpIncidencePlanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls

abbrev transfer : Cmd 10 10 := .call (StackRoutines.transferProgram 8 0 0 1)

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_IncidencePlanSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Ordered incidence plans from finite scope lists

The numeric producer records incident factors in their input order. The
typed refinement uses the rank in that same list as the local slot.
-/

namespace SubexponentialSAT.Subexp.IncidencePlanSpec

theorem mem_incidenceFrom (v start e : ℕ) (scopes : List (List ℕ)) :
    e ∈ incidenceFrom v start scopes ↔
      ∃ i : Fin scopes.length, start + i.val = e ∧ v ∈ scopes.get i := by
  induction scopes generalizing start with
  | nil => simp [incidenceFrom]
  | cons C Cs ih =>
    by_cases hv : v ∈ C
    · simp [incidenceFrom, hv, ih, Fin.exists_fin_succ,
        Nat.add_comm, Nat.add_left_comm, eq_comm]
    · simp [incidenceFrom, hv, ih, Fin.exists_fin_succ,
        Nat.add_comm, Nat.add_left_comm, eq_comm]

theorem incidenceFrom_bounds (v start e : ℕ) (scopes : List (List ℕ))
    (he : e ∈ incidenceFrom v start scopes) :
    start ≤ e ∧ e < start + scopes.length := by
  obtain ⟨i, hi, _⟩ := (mem_incidenceFrom v start e scopes).mp he
  have := i.isLt
  omega

theorem incidenceFrom_nodup (v start : ℕ) (scopes : List (List ℕ)) :
    (incidenceFrom v start scopes).Nodup := by
  induction scopes generalizing start with
  | nil => simp [incidenceFrom]
  | cons C Cs ih =>
    by_cases hv : v ∈ C
    · simp only [incidenceFrom, ite_eq_left hv, List.nodup_cons]
      refine ⟨?_, ih (start + 1)⟩
      intro h
      have := incidenceFrom_bounds v (start + 1) start Cs h
      omega
    · simpa only [incidenceFrom, ite_eq_right hv] using ih (start + 1)

theorem incidentIndices_nodup (scopes : List (List ℕ)) (v : ℕ) :
    (incidentIndices scopes v).Nodup :=
  incidenceFrom_nodup v 0 scopes

theorem mem_incidentIndices (scopes : List (List ℕ)) (v : ℕ) (e : Fin scopes.length) :
    e.val ∈ incidentIndices scopes v ↔ v ∈ scopes.get e := by
  rw [incidentIndices, mem_incidenceFrom]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨i, hi, hv⟩
    have : i = e := Fin.ext hi
    simpa only [this] using hv
  · intro hv
    exact ⟨e, rfl, hv⟩

theorem incidentIndex_lt (scopes : List (List ℕ)) (v e : ℕ)
    (he : e ∈ incidentIndices scopes v) : e < scopes.length := by
  have h := (incidenceFrom_bounds v 0 e scopes he).2
  simpa only [Nat.zero_add] using h

end SubexponentialSAT.Subexp.IncidencePlanSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite scan of encoded scopes. No slot map is supplied as input:
the local slot order is the encounter order of incident factors. -/
namespace SubexponentialSAT.SubexpIncidencePlanScan

open BitProgram StructuredCalls
open SubexpIncidencePlanPrimitives

abbrev scopeBytes := Encoding.encodeList Encoding.encodeNat

def indexPrefix (js : List ℕ) : List Bool :=
  js.flatMap fun j => true :: Encoding.frame (unary j)

abbrev addDegree : Cmd 10 10 := .ite 4 (increment 9) (.base .skip)

def callbackBound (v j : ℕ) (scope : List ℕ) : ℕ :=
  128 * (v + 2) * ((scopeBytes scope).length + 1) + 16 * (j + 2)

def scanBudget (v : ℕ) : ℕ → List (List ℕ) → ℕ
  | _, [] => 0
  | j, C :: Cs => 6 * (scopeBytes C).length + callbackBound v j C + 7 +
      scanBudget v (j + 1) Cs

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      simp only [List.cons_append, value, List.length_cons, ih, pow_succ]
      ring

theorem value_lt_two_pow_length (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true,
        List.length_cons, pow_succ] <;> omega

theorem trimTail_length_le (xs : List Bool) : (trimTail xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [trimTail]
  | cons b xs ih => cases b <;> simp [trimTail]; omega

/-- A most-significant one followed by `m` bits has binary logarithm `m`. -/
theorem log2_value_append_true (xs : List Bool) :
    Nat.log2 (value (xs ++ [true])) = xs.length := by
  have hbound := value_lt_two_pow_length xs
  have hpow : 0 < 2 ^ xs.length := Nat.two_pow_pos _
  have hval : value (xs ++ [true]) = value xs + 2 ^ xs.length := by
    simp [value_append, value]
  have hpos : value (xs ++ [true]) ≠ 0 := by omega
  apply Nat.le_antisymm
  · have hlt : value (xs ++ [true]) < 2 ^ (xs.length + 1) := by
      rw [pow_succ]
      omega
    have h := (Nat.log2_lt hpos).mpr hlt
    omega
  · exact (Nat.le_log2 hpos).mpr (by omega)

theorem trimTail_reverse_length (xs : List Bool) :
    (trimTail xs.reverse).length = Nat.log2 (value xs) := by
  induction xs using List.reverseRecOn with
  | nil => simp [trimTail, value]
  | append_singleton xs b ih =>
      cases b with
      | false => simpa [List.reverse_append, trimTail, value_append, value] using ih
      | true => simp [List.reverse_append, trimTail, log2_value_append_true]

/-! ## Consume a most-significant zero prefix and the leading one -/

@[simp] theorem update_lengthStacks_one (a b c d : List Bool) :
    Function.update (lengthStacks a b c) 1 d = lengthStacks a d c := by
  funext i
  fin_cases i <;> simp [lengthStacks]

def trimCost : List Bool → ℕ
  | [] => 5
  | false :: xs => trimCost xs + 3
  | true :: _ => 6

theorem trimCost_le (xs : List Bool) : trimCost xs ≤ 3 * xs.length + 6 := by
  induction xs with
  | nil => simp [trimCost]
  | cons a xs ih => cases a <;> simp only [trimCost, List.length_cons] <;> omega

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls

abbrev Code := Cmd 10 13
abbrev scopeBytes := SubexpIncidencePlanScan.scopeBytes
def scopeBits (scopes : List (List ℕ)) := Encoding.encodeList scopeBytes scopes

def indices (scopes : List (List ℕ)) (e v : ℕ) : List Bool :=
  SubexpIncidencePlanScan.indexPrefix
    (Subexp.IncidencePlanSpec.incidenceFrom v 0 (scopes.take e)).reverse

def copy (src dst : Fin 13) : Code := .call (StackRoutines.copyProgram src dst 8 0 1)

def push (dst : Fin 13) (bit : Bool) : Code :=
  .seq (.base (.atom (.set 0 bit))) (.base (.atom (.push dst 0)))

def prepare : Code := .seq (copy 0 4) (copy 1 5)

def makeQuery : Code := .seq (copy 2 6) (push 6 false)

def budget (scopes : List (List ℕ)) (e v : ℕ) : ℕ :=
  20 * (scopeBits scopes).length + 10 * e + 10 * v + 100 +
    SubexpIncidencePlanScan.scanBudget v 0 (scopes.take e) +
    2 * (scopes.take e).length + 2 * (indices scopes e v).length

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UnaryCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for exact conditional-score comparisons

The local conditional scores admit bounded natural numerators. Unary storage
is therefore already polynomial in the growing parameters. This module gives
an actual fixed finite instruction table comparing two stack lengths and
connects its measured execution to those conditional scores.
-/

namespace SubexponentialSAT.Subexp.UnaryCompare

open SubexponentialSAT.BitProgram

/-- Compare stack lengths destructively. Register 3 receives `left ≤ right`.
The four registers, two stacks, and seven labels do not depend on the data. -/
abbrev program : Program 4 2 7 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .pop 1 0 2 2
    | 2 => .branch 1 3 5
    | 3 => .branch 2 0 4
    | 4 => .set 3 false 6
    | 5 => .set 3 true 6
    | _ => .halt

end SubexponentialSAT.Subexp.UnaryCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev scopeBits := SubexpIncidenceSlotProgram.scopeBits

def queryBudget (scopes : List (List ℕ)) (v cut : ℕ) : ℕ :=
  SubexpIncidenceSlotProgram.budget scopes scopes.length v +
    20 * (cut + degree scopes v + 2) + 20

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramCutoff
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def ports : ArithmeticCalls.Ports 12 where
  left := 0
  right := 1
  out := 3
  work := work
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion from descending high mask to forward high mask. The
descending mask is retained for the high-assignment iterator. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 2 4
abbrev state (regs : Fin 2 → Bool) (source work output tmp : List Bool) : Data :=
  ⟨regs, ![source, work, output, tmp]⟩
abbrev command : Cmd 2 4 :=
  .seq (.call (StackRoutines.copyProgram 0 1 3 0 1))
    (.call (StackRoutines.transferProgram 1 2 0 1))
def program := compiled command 0 2

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSunflowerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram

namespace CountRecords

/-- Count records into a canonical unary field. Payload bits are skipped by
following their escape tags. The same thirteen labels handle every count. -/
abbrev program : Program 2 2 13 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .push 1 0 2
    | 2 => .pop 0 0 1 3
    | 3 => .branch 0 4 10
    | 4 => .set 0 true 5
    | 5 => .push 1 0 6
    | 6 => .pop 0 0 1 7
    | 7 => .branch 0 8 2
    | 8 => .pop 0 0 1 9
    | 9 => .goto 6
    | 10 => .set 0 false 11
    | 11 => .set 1 false 12
    | _ => .halt

end CountRecords

end SubexponentialSAT.SubexpSunflowerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

abbrev counterProgram : Program 2 2 13 :=
  { SubexpSunflowerProgram.CountRecords.program with entry := 2 }

def countBudget (records : List (List Bool)) : ℕ :=
  7 * (Encoding.encodeList id records).length + 5 + SubexpSunflowerProgram.CountRecords.loopSteps records

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual two-level record scan counting explicit scope entries. The ghost
payload decoder occurs only in the loop specification; the executable callback
uses the existing physical record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev encode := Encoding.encodeList (id : List Bool → List Bool)

noncomputable def payloadCount (bits : List Bool) : ℕ := by
  classical
  exact if h : ∃ rs, encode rs = bits then (Classical.choose h).length else 0

noncomputable def update (bits acc : List Bool) := List.replicate (payloadCount bits) true ++ acc

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMassBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Serialized scope adapter and complete bit cost for the nested counter.
The counter counts supplied entries; the caller's normalization invariant is
what identifies this with distinct factor-variable incidence mass. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def scopeRecords (scopes : List (List ℕ)) : List (List (List Bool)) :=
  scopes.map (List.map Encoding.encodeNat)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full original-coordinate scan using a runtime unary loop counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local irreducible] SubexpIncidenceSlotProgram.scopeBits Subexp.IncidencePlanSpec.degree

def scanBudget (scopes : List (List ℕ)) (n cut : ℕ) : ℕ :=
  CounterForPrograms.budgetSum (fun i => queryBudget scopes i cut) 0 n + 2 * n + 2


def uniformQueryBudget (scopes : List (List ℕ)) (n cut : ℕ) :=
  1000 * ((scopeBits scopes).length + scopes.length + n + 1)^2 +
    20 * (cut + scopes.length + 2) + 20

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask traverses original coordinates in descending order.
This explicit order, rather than an arbitrary finite-type equivalence,
identifies each odometer position with its actual original variable. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

theorem highPrefix_range (scopes : List (List ℕ)) (cut n : ℕ) :
    highPrefix scopes cut n = (List.range n).reverse.map (fun v => decide (cut < degree scopes v)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [highPrefix, List.range_succ, ih]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockCopyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev Data := StructuredProgram.State 3 4

theorem copies_succ (n : ℕ) (table : List Bool) :
    copies (n + 1) table = copies n table ++ table := by
  simp only [copies, List.replicate_succ', List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil]

@[simp] theorem copies_length (n : ℕ) (table : List Bool) :
    (copies n table).length = n * table.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [copies_succ, List.length_append, ih]; ring

def data (value active : Bool) (table output counter : List Bool) : Data :=
  ⟨![value, false, active], ![table, output, [], counter]⟩

/-- The loop state includes a pending copy when the active flag is true. -/
def loopState (n : ℕ) (table output : List Bool) : Data :=
  match n with
  | 0 => data false false table output []
  | n + 1 => data true true table output (List.replicate n true)

def initialState (n : ℕ) (table output : List Bool) : Data :=
  data false false table output (List.replicate n true)

theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

end SubexponentialSAT.Subexp.BlockCopyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def records (scopes : List (List ℕ)) := (Mass.scopeRecords scopes).map Mass.encode

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestrictionTotal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Every correctly sized pair of branch streams is accepted by the actual
merge program, and the resulting original-coordinate assignment is unique. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev highCount := Subexp.PaddedCompletion.trueCount

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

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

theorem addBudget_polynomial (B d : ℕ) :
    addBudget B d ≤ 50000 * (d+1)^3 * (B+1)^2 := by
  unfold addBudget RingScan.serviceAddBudget
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- Products of `X^a H^s`, with `a < 3`, need only the relations for X^3,X^4. -/
def hadicTable {t : ℕ} (i j k : Fin (3*t)) : ℤ :=
  let s := i.val / 3 + j.val / 3
  let a := i.val % 3 + j.val % 3
  if a < 3 then atomInteger (3*s+a) 1 k
  else if a = 3 then
    atomInteger (3*(s+1)) 1 k + atomInteger (3*s+1) (-2) k +
      atomInteger (3*s+2) 3 k
  else
    atomInteger (3*(s+1)) 3 k + atomInteger (3*(s+1)+1) 1 k +
      atomInteger (3*s+1) (-6) k + atomInteger (3*s+2) 7 k

theorem hValue_pow_eq_zero (x : R) {t s : ℕ} (ht : hValue x ^ t = 0)
    (hs : t ≤ s) : hValue x ^ s = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [pow_add, ht, zero_mul]

theorem atomInteger_eval (t s a : ℕ) (z : ℤ) (x : R)
    (ha : a < 3) (ht : hValue x ^ t = 0) :
    (∑ k : Fin (3*t), (atomInteger (3*s+a) z k : R) * hadicBasis t x k) =
      (z : R) * (x^a * hValue x^s) := by
  by_cases hs : s < t
  · let k : Fin (3*t) := ⟨3*s+a, by omega⟩
    have hkmod : k.val % 3 = a := by dsimp [k]; omega
    have hkdiv : k.val / 3 = s := by dsimp [k]; omega
    calc
      (∑ j : Fin (3*t), (atomInteger (3*s+a) z j : R) * hadicBasis t x j) =
          (atomInteger (3*s+a) z k : R) * hadicBasis t x k := by
        apply Finset.sum_eq_single k
        · intro b _ hbk
          have hb : b.val ≠ 3*s+a := by
            intro hb
            apply hbk
            apply Fin.ext
            exact hb
          simp [atomInteger, hb]
        · simp
      _ = _ := by simp [atomInteger, hadicBasis, k, hkmod, hkdiv]
  · have hz := hValue_pow_eq_zero x ht (by omega : t ≤ s)
    rw [hz, mul_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro k _
    have hk : k.val ≠ 3*s+a := by have := k.isLt; omega
    simp [atomInteger, hk]

theorem hadicBasis_mul (t : ℕ) (x : R) (i j : Fin (3*t)) :
    hadicBasis t x i * hadicBasis t x j =
      x^(i.val%3+j.val%3) * hValue x^(i.val/3+j.val/3) := by
  simp only [hadicBasis, pow_add]
  ring

theorem hadicTable_correct (t : ℕ) (x : R) (ht : hValue x ^ t = 0)
    (i j : Fin (3*t)) :
    hadicBasis t x i * hadicBasis t x j =
      ∑ k : Fin (3*t), (hadicTable i j k : R) * hadicBasis t x k := by
  rw [hadicBasis_mul]
  let s := i.val / 3 + j.val / 3
  let a := i.val % 3 + j.val % 3
  have ha : a ≤ 4 := by dsimp [a]; omega
  change x^a * hValue x^s = _
  by_cases ha3 : a < 3
  · simp only [hadicTable, show i.val/3+j.val/3 = s from rfl,
      show i.val%3+j.val%3 = a from rfl, ha3, ↓reduceIte]
    rw [atomInteger_eval t s a 1 x ha3 ht]
    simp
  · by_cases heq : a = 3
    · simp only [hadicTable, show i.val/3+j.val/3 = s from rfl,
        show i.val%3+j.val%3 = a from rfl, heq, Nat.lt_irrefl, ↓reduceIte,
        Int.cast_add, add_mul, Finset.sum_add_distrib]
      rw [show 3*(s+1) = 3*(s+1)+0 by omega,
        atomInteger_eval t (s+1) 0 1 x (by omega) ht,
        atomInteger_eval t s 1 (-2) x (by omega) ht,
        atomInteger_eval t s 2 3 x (by omega) ht]
      simp only [ Int.cast_one, Int.cast_neg, Int.cast_ofNat, pow_zero, one_mul]
      rw [pow_succ]
      unfold hValue
      ring
    · have heq4 : a = 4 := by omega
      simp only [hadicTable, show i.val/3+j.val/3 = s from rfl,
        show i.val%3+j.val%3 = a from rfl, ha3, heq, ↓reduceIte,
        Int.cast_add, add_mul, Finset.sum_add_distrib]
      rw [show 3*(s+1) = 3*(s+1)+0 by omega,
        atomInteger_eval t (s+1) 0 3 x (by omega) ht,
        atomInteger_eval t (s+1) 1 1 x (by omega) ht,
        atomInteger_eval t s 1 (-6) x (by omega) ht,
        atomInteger_eval t s 2 7 x (by omega) ht]
      simp only [heq4, Int.cast_one, Int.cast_neg, Int.cast_ofNat, pow_zero, one_mul]
      rw [pow_succ]
      unfold hValue
      ring

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramRepeat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime-sized cell repetition for idempotent preparation. The
source cell and unary count are data; the finite control is independent of
both lengths. Every source bit copied into the destination is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

abbrev Data := State 8 41

theorem repeatRegisters_injective : Function.Injective repeatRegisters := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 8 => x.val) h

def resetData (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    d.stacks⟩

def repeated (d : Data) (target count : Fin 41) (n : ℕ) (cell : List Bool) : Data :=
  ⟨(resetData d).regs, Function.update (Function.update d.stacks count []) target
    (Subexp.BlockCopyProgram.copies n cell ++ d.stacks target)⟩

theorem copies_replicate (n width : ℕ) (bit : Bool) :
    Subexp.BlockCopyProgram.copies n (List.replicate width bit) =
      List.replicate (n * width) bit := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Subexp.BlockCopyProgram.copies_succ, ih, ← List.replicate_add]
      congr 1
      ring

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive bit-mask union. Both runtime input words have the same
length. The output is prepended in reverse order; no list operation is atomic
and the instruction table does not depend on the word length. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev MaskData := State 5 3

def maskData (regs : Fin 5 → Bool) (left right output : List Bool) : MaskData :=
  ⟨regs, ![left, right, output]⟩

def maskReady (regs : Fin 5 → Bool) (left right output : List Bool) : MaskData :=
  maskData (readRegs regs 0 2 left.head?) left right output

@[simp] theorem maskReady_guard (regs : Fin 5 → Bool) (left right output : List Bool) :
    (maskReady regs left right output).regs 2 = !left.isEmpty := by
  cases left <;> simp [maskReady, maskData, readRegs]

end SubexponentialSAT.SqrtLog.Squarefree.Program

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



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K C R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

def denoteTable (f : C → R) (entries : List (K × C)) : Squarefree.Sparse.Data K R :=
  entries.map fun a => (a.1,f a.2)

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Index

variable {V : Type*} [DecidableEq V]

def Valid (a : Index V) : Prop := a.vars.card ≤ a.z

end Index

end SubexponentialSAT.SqrtLog.Squarefree

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

/-- Common product idle store: caches and runtime controls only. -/
def idle (modulus width zero table degree uCap zCap : List Bool) : Store :=
  {modulus := modulus, width := width, zero := zero, table := table,
    degree := degree, uCap := uCap, zCap := zCap}

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native refinements for the scalar coefficient reader and injector.
All stacks outside the named outputs are preserved, including the ambient
low-product environment. -/


namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar
open BitProgram StructuredCalls
open HashCircuitProgram.Native
open SubexpQuarticRing

def coefficient (dimension : ℕ) (zero word : List Bool) : List Bool :=
  word ++ Subexp.BlockCopyProgram.copies (dimension-1) zero

def scalarCost (dimension : ℕ) (zero word shape : List Bool) : ℕ :=
  (11*word.length+8) + injectionCost dimension zero.length word.length +
    (2*word.length+3) + (7*shape.length+5) +
    (8*shape.length+7*(coefficient dimension zero word).length+31)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial envelopes for the concrete degree-two coefficient and
Horner machines. Every byte copy, dictionary scan, product and tape reversal
in the native cost definitions is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def mulEnvelope (B d n u J N : ℕ) : ℕ :=
  29*byteCapacity n B d u J N +
    N*(Product.stepEnvelope B d n u J (N*N) N+2)+30

def addEnvelope (B d n u J N : ℕ) : ℕ :=
  36*byteCapacity n B d u J N+9*d+
    N*(220*(2*N+1)*(n+u+J+d*B+1)+MomentsProgram.Dictionary.codeBranchBudget B d+2)+44

def quadraticEnvelope (B d n u J N : ℕ) : ℕ :=
  3*wordEnvelope B d n+2*(7*byteCapacity n B d u J N+5)+
    2*mulEnvelope B d n u J N+2*addEnvelope B d n u J N

def accumulatorEnvelope (B d n u J N : ℕ) : ℕ :=
  43*byteCapacity n B d u J N+37+
    mulEnvelope B d n u J N+addEnvelope B d n u J N

def loopEnvelope (B d n u J N L : ℕ) : ℕ :=
  L*(quadraticEnvelope B d n u J N+accumulatorEnvelope B d n u J N+2)+1

def applyEnvelope (B d n u J N L keyLength : ℕ) : ℕ :=
  30*B*L+11*byteCapacity n B d u J N+2*keyLength+23+
    loopEnvelope B d n u J N L

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramBoundsMultiplier
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The setup charge includes scaling by cached minus one, normalized cubic
arithmetic, construction of the U key, and the physical key-map loop. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps Multiplier

variable {p t n d : ℕ} [Fact p.Prime]

def normalizeStepEnvelope (B d n u J N : ℕ) : ℕ :=
  220*(2*N+1)*(n+u+J+d*B+1)+MomentsProgram.Dictionary.codeBranchBudget B d+2

def complementEnvelope (B d n u J N : ℕ) : ℕ :=
  52*byteCapacity n B d u J N+18*(d*B)+9*d+
    N*scaleStepEnvelope B d n u J+N*normalizeStepEnvelope B d n u J N+80

def arithmeticEnvelope (B d n u J N : ℕ) : ℕ :=
  46*byteCapacity n B d u J N+36+complementEnvelope B d n u J N+
    addEnvelope B d n u J N+2*mulEnvelope B d n u J N

def prepareEnvelope (B d n u J N : ℕ) : ℕ :=
  arithmeticEnvelope B d n u J N+20*n+53+N*(120*(n+u+J+d*B+3)+2)

def totalEnvelope (B d n u J N L : ℕ) : ℕ :=
  prepareEnvelope B d n u J N+applyEnvelope B d n u J N L (n+3)+1

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrayStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

def arrayStacks (s : Fin 41 → List Bool) (t : ℕ) : Fin 41 → List Bool :=
  let v := s 30 ++ s 31 ++ s 27 ++ Subexp.BlockCopyProgram.copies (3*t-3) (s 17)
  let m := s 28 ++ Subexp.BlockCopyProgram.copies (3*t-1) (s 17)
  Function.update (Function.update (Function.update (Function.update (Function.update s
    32 v) 33 v) 34 v) 35 v) 36 m

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

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

abbrev Data := StructuredProgram.State 3 3
abbrev io (xs : List Bool) : Data := StructuredProgram.ioState 0 xs

theorem incrementPorts_injective : Function.Injective incrementPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [incrementPorts]

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramLog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native ceiling-logarithm controller. The positive runtime input
t is changed to t-1; a zero guard handles t=1, otherwise floor-log-plus-one
computes the exact Newton iteration count. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Log

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev io := Setup.io

theorem clog_eq_log_pred (t : ℕ) (ht : 2 ≤ t) :
    Nat.clog 2 t = Nat.log2 (t-1) + 1 := by
  rw [Nat.log2_eq_log_two]
  apply Nat.le_antisymm
  · apply (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
    have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (t-1)
    omega
  · have hp := Nat.pow_log_le_self 2 (show t-1 ≠ 0 by omega)
    have hlt : 2 ^ Nat.log 2 (t-1) < t := by omega
    have hh := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hlt
    omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Log

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unary iteration budget is derived from the runtime binary t word.
This module includes its native conversion trace and preserves the original
word for modulus construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

def metadataStacks (stackData : Fin 41 → List Bool) (logword : List Bool) : Fin 41 → List Bool :=
  Function.update (Function.update (Function.update (Function.update stackData
    29 (List.replicate (CounterPrograms.value (stackData 31)) true))
    12 (List.replicate (2*CounterPrograms.value (stackData 31)) true))
    37 (List.replicate (3*CounterPrograms.value (stackData 31)) true)) 39 logword

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native production of the ternary modulus from runtime binary precision.
The output bytes themselves instantiate the prepared-modulus structure;
no canonical encoding or precomputed power is supplied to the machine. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

theorem modulusPorts_injective : Function.Injective modulusPorts := by decide

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramRegisters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving storage for the fixed Newton register machine. Every
copy, replacement, and clearing operation is an actual finite bit program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls StackRoutines

abbrev RegisterData := State 8 41

def preparedOperands (d : RegisterData) (left right : Fin 41) : RegisterData :=
  ArithmeticCalls.afterCopy 37 11
    (ArithmeticCalls.afterCopy right 9 (ArithmeticCalls.afterCopy left 8 d))

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native, source-preserving scalar operations on the preparation ABI.
Only the selected output changes; all low arithmetic scratch is restored. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 41

def operands (d : Data) (left right : Fin 41) : Data :=
  ArithmeticCalls.afterCopy right 1 (ArithmeticCalls.afterCopy left 0 d)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed register language for the twelve scalar cache/temporary words.
Its interpreter is actual finite code, not a unit-cost arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms

theorem port_injective : Function.Injective port := by decide
@[simp] theorem port_ge (i : Reg) : 8 ≤ (port i).val := by fin_cases i <;> decide
@[simp] theorem port_ne38 (i : Reg) : port i ≠ 38 := by fin_cases i <;> decide
@[simp] theorem port_ne40 (i : Reg) : port i ≠ 40 := by fin_cases i <;> decide

inductive Op where
  | add (out left right : Reg)
  | mul (out left right : Reg)

variable (p t : ℕ) [Fact p.Prime]

/-- Cache registers: 0=zero,1=one,2=-2,3=3,4=-6,5=7,
6,7=temporary,8=half,9=-1,10=twice-half,11=-three-half. -/
def constants : List Op :=
  [.add 6 1 1, .add 3 6 1, .add 2 9 9, .mul 4 2 3,
   .add 5 3 3, .add 5 5 1, .add 8 1 0]

def halfStep : List Op := [.add 6 8 8, .add 7 6 8, .add 8 7 9]

def finalCoefficients : List Op := [.add 10 8 8, .add 6 10 8, .mul 11 6 9]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open SubexpLiftRing SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime]

def Op.algebra {A : Type*} [CommRing A] (v : Reg→A) : Op → Reg→A
  | .add o l r => Function.update v o (v l+v r)
  | .mul o l r => Function.update v o (v l*v r)

def algebra {A : Type*} [CommRing A] : List Op → (Reg→A) → Reg→A
  | [],v=>v
  | op::ops,v=>algebra ops (op.algebra v)

theorem constants_algebra {A : Type*} [CommRing A] (v : Reg→A)
    (h0:v 0=0) (h1:v 1=1) (hn:v 9 = -1) :
    let w:=algebra constants v
    w 0=0 ∧ w 1=1 ∧ w 2 = -2 ∧ w 3=3 ∧ w 4 = -6 ∧ w 5=7 ∧ w 8=1 ∧ w 9 = -1 := by
  simp [algebra,constants,Op.algebra,h0,h1,hn] ; norm_num

theorem halfStep_algebra {A : Type*} [CommRing A] (v : Reg→A) (hn:v 9 = -1) :
    (algebra halfStep v) 8=3*v 8-1 ∧ (algebra halfStep v) 9 = -1 ∧
    (∀ i:Reg, i≠6 → i≠7 → i≠8 → (algebra halfStep v) i=v i) := by
  constructor
  · simp [algebra,halfStep,Op.algebra,hn]; ring
  constructor
  · simp [algebra,halfStep,Op.algebra,hn]
  · intro i hi6 hi7 hi8
    simp [algebra,halfStep,Op.algebra,hi6,hi7,hi8]

theorem final_algebra {A : Type*} [CommRing A] (v : Reg→A) (hn:v 9 = -1) :
    (algebra finalCoefficients v) 10=2*v 8 ∧
    (algebra finalCoefficients v) 11 = -3*v 8 ∧
    (∀ i:Reg, i≠6 → i≠10 → i≠11 → (algebra finalCoefficients v) i=v i) := by
  constructor
  · simp [algebra,finalCoefficients,Op.algebra,hn]; ring
  constructor
  · simp [algebra,finalCoefficients,Op.algebra,hn]; ring
  · intro i hi6 hi10 hi11
    simp [algebra,finalCoefficients,Op.algebra,hi6,hi10,hi11]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime]

def tableRegister : Fin 6→Reg := ![0,1,3,2,4,5]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed fixed-bit F₃ factor checker. The complete command is independent
of the degree. All coefficient addresses and loop bounds are runtime unary
words; source vectors are preserved and scratch stacks are discharged. -/


/-! Coefficient -/

/-! A fixed coefficient kernel: two preserved source arrays, a preserved
unary coefficient address plus one, and an output stack. Every copy, padded
prefix, coefficient reversal, multiply-add and cleanup is an actual call. -/


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/


/-! ProductRun -/


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/


/-! MonicAlgebra -/


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/


/-! PairProduct -/


/-! Candidate -/


/-! ProductCheck -/


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

def pairFlagsAtoms : List (Atom 16 18) :=
  [.pop 12 14 15, .band 3 14 3, .pop 12 14 15, .band 3 3 14, .bnot 3 3]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls

def operator (mul : Bool) : Word := [true, mul]

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end


