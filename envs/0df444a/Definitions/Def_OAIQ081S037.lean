-- Prove2me | Definitions.Def_OAIQ081S037
-- name    : OAIQ081S037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:32:11.653709+00:00
-- url     : https://prove2.me/theorems/2972c055-1480-40ae-b705-5b4a569b62f7
-- title:
--   Definitions bundle OAIQ081S037 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 80 declarations of OpenAI's Lean: 48 definitions, 1 inductive type or structure, 1 instance and 30 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.natRecord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.recordPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.testCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Protected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.cacheBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNative.References.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.QuotientReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard.lower`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard.lowerFor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard.upper`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard.upperFor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout.setupScale`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.LogData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.unaryCopyBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.fieldCard`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.loopCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.produce`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide.blank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide.bytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.reset`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.HashParameters.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.lowPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.afterClear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.afterCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.popCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.alphabet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.Guard.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.pop`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.setFirst`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.transfer` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramTest`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramVisit`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage`, `SubexponentialSAT_SqrtLog_LeafOuterNativeReferences`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient`, `SubexponentialSAT_SqrtLog_LeafParametersProgram`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramCrudeBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramIntervalBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramLog`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafParametersProgramSerializationUnary`, `SubexponentialSAT_SqrtLog_LeafProgramCleanup`, `SubexponentialSAT_SqrtLog_LeafProgramCleanupWide`, `SubexponentialSAT_SqrtLog_LeafProgramHashParameters`, `SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadback`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCore`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsEnumeration`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTotals`, `SubexponentialSAT_SqrtLog_ProducedQueryRankMagnitude`, `SubexponentialSAT_SqrtLog_RingProgramTableBasic`, `SubexponentialSAT_SqrtLog_RingProgramTableLoop`, `SubexponentialSAT_SqrtLog_RowSelectionProgramIndex`, `SubexponentialSAT_SqrtLog_SetupGuard`, `SubexponentialSAT_SubexpClauseMastersProgram`, `SubexponentialSAT_SubexpGuardProgram`, `SubexponentialSAT_SubexpIntervalCoreProgram`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_Subexp_AssignmentRecordViews`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S005`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S008`, `OAIQ081S009`, `OAIQ081S012`, `OAIQ081S014` and `OAIQ081S015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061` and `OAIQ081S064`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_forwardHighMask_guards` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_measured_guards`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_forwardHighMask_guards`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008
import Definitions.Def_OAIQ081S009
import Definitions.Def_OAIQ081S012
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S015

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls

def testCost (A j W : ℕ) (bitIndex word : List Bool) : ℕ :=
  lookupCost (A + j) W + 9 * (A + j) + 7 * bitIndex.length + 18 +
    Subexp.TypeBitProgram.cost bitIndex word

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls

def natRecord (j : ℕ) : List Bool := true :: Encoding.frame (Encoding.encodeNat j)

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls

def recordPrefix (p : ℕ → Bool) (n : ℕ) : List Bool := (chosenIds p n).flatMap natRecord

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem value_eq_toNat (xs : List Bool) : value xs = BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [value, BinaryArithmetic.toNat,
      BinaryArithmetic.bitVal, ih]

/-! ## Consume a most-significant zero prefix and the leading one -/

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- Borrow propagation with implicit high zero bits. -/
def carry (c : Bool) : List Bool → List Bool → Bool
  | [], [] => c
  | a :: xs, [] => carry (ModularArithmetic.borrowBit a false c) xs []
  | [], b :: ys => carry (ModularArithmetic.borrowBit false b c) [] ys
  | a :: xs, b :: ys => carry (ModularArithmetic.borrowBit a b c) xs ys
termination_by xs ys => xs.length + ys.length

/-- The final borrow is the strict comparison, even for unequal word lengths. -/
theorem carry_iff (xs ys : List Bool) (c : Bool) :
    carry c xs ys = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys + bitVal c := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [carry, bitVal]
    | cons b ys ih =>
      rw [carry, ih]
      cases b <;> cases c <;>
        simp [ModularArithmetic.borrowBit, bitVal, BinaryArithmetic.toNat]
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [carry, ih]
      cases a <;> cases c <;>
        simp [ModularArithmetic.borrowBit, bitVal, BinaryArithmetic.toNat]
    | cons b ys =>
      rw [carry, ih]
      cases a <;> cases b <;> cases c <;>
        simp [ModularArithmetic.borrowBit, bitVal, BinaryArithmetic.toNat] <;> omega

abbrev cfg (pc : Option (Fin 12)) (regs : Fin 8 → Bool) (xs ys : List Bool) : Cfg 8 2 12 :=
  ⟨pc, regs, operandStacks xs ys⟩

def read (regs : Fin 8 → Bool) (a b : Option Bool) : Fin 8 → Bool :=
  readRegs (readRegs regs 1 3 a) 2 4 b

def roundRegs (regs : Fin 8 → Bool) (a b : Option Bool) : Fin 8 → Bool :=
  let r := read regs a b
  let r := Function.update r 5 (a.isSome || b.isSome)
  let r := Function.update r 6 (!a.getD false)
  let r := Function.update r 6 ((!a.getD false) && b.getD false)
  let r := Function.update r 7 (a.getD false ^^ b.getD false)
  let r := Function.update r 7 (!(a.getD false ^^ b.getD false))
  let r := Function.update r 7 ((!(a.getD false ^^ b.getD false)) && regs 0)
  Function.update r 0 (((!a.getD false) && b.getD false) ||
    ((!(a.getD false ^^ b.getD false)) && regs 0))

theorem roundRegs_borrow (regs : Fin 8 → Bool) (a b : Option Bool) :
    roundRegs regs a b 0 = ModularArithmetic.borrowBit (a.getD false) (b.getD false) (regs 0) := by
  simp only [roundRegs, Function.update_self]
  cases ha : a.getD false <;> cases hb : b.getD false <;> cases hc : regs 0 <;>
    simp [ ModularArithmetic.borrowBit]

def exitRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (read regs none none) 5 false

@[simp] theorem exitRegs_borrow (regs : Fin 8 → Bool) : exitRegs regs 0 = regs 0 := by
  simp [exitRegs, read, readRegs]

end Compare

open StructuredProgram

/-- Restrict caller data to the fixed ports of a subroutine. This is assertion
notation, not an instruction available to the program. -/
def restrictState {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (a : State R S) : State 8 2 :=
  ⟨fun i => a.regs (register i), fun i => a.stacks (stack i)⟩


end SubexponentialSAT.SubexpGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

abbrev Protected (i : Fin 768) : Prop := (i.val < 340 ∨ 628 ≤ i.val) ∧ i ≠ temporary

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def cacheBound (a r width : List Bool) : ℕ :=
  7*(a.length+r.length+width.length)+LayoutProgram.IntegerCache.flatCost a.length r.length width.length+
    11*r.length+27

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramIndex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime, self-delimiting natural-index alphabet. The range control is the
existing unary loop, with one delimiter inserted in each emitted payload. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Index
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpIncidencePlanPrimitives

def alphabet (s : ℕ) : List (List Bool) := (List.range s).reverse.map Encoding.encodeNat

@[simp] theorem alphabet_length (s : ℕ) : (alphabet s).length = s := by simp [alphabet]

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterNativeReferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked-reference stream is generated by a fixed program from the binary
clause count. Both binary-to-unary expansion and the quadratic framed stream
emission are part of the measured run. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative.References
open SubexponentialSAT BitProgram StructuredCalls

def budget (bits : List Bool) : ℕ :=
  CounterConversions.coreBound bits+CounterPrograms.value bits*(12*CounterPrograms.value bits+32)+8

end SubexponentialSAT.SqrtLog.LeafOuterNative.References

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving floor quotient call using the audited finite binary
long-division program. Operands are runtime padded Boolean words. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

abbrev Data (S : ℕ) := StructuredProgram.State 8 S

def QuotientReady {S : ℕ} (p : QuotientPorts S) (d : Data S) : Prop :=
  d.stacks p.out = [] ∧ ∀ i, d.stacks (p.work i) = []

theorem quotientStackMap_injective {S : ℕ} (p : QuotientPorts S) :
    Function.Injective (quotientStackMap p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [quotientStackMap, p.work.injective.eq_iff, p.work_ne_right,
      p.work_ne_out, p.out_ne_right, Ne.symm p.out_ne_right]

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime parameter semantics. Every definition below uses natural
arithmetic; the executable refinements are separate from these specifications.
The original ambient dimension is retained through high-incidence branching. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

def produce (x : Input) : Parameters :=
  let n := x.freeCount
  let r := Asymptotic.layoutR n
  let Q := Asymptotic.layoutQ n
  let R := Asymptotic.layoutCutoff n x.occurrence
  let t := precision x.ambient x.clauses
  { L := Asymptotic.L n
    w := Asymptotic.w n
    s := Asymptotic.s n
    r := r
    Q := Q
    R := R
    epsilonDen := 32 * x.occurrence * r * Asymptotic.L n ^ 2
    t := t
    d := extensionDegree Q
    N := r ^ (2 * Q)
    J := x.width * R * (2 * x.factors + 3 * (t - 1) + 1) / Q + 1 }

theorem precision_pos (n m : ℕ) : 0 < precision n m := by
  unfold precision
  omega

theorem extensionDegree_pos (Q : ℕ) : 0 < extensionDegree Q := by
  unfold extensionDegree
  omega

theorem extensionDegree_sufficient (Q : ℕ) : Q < 3 ^ extensionDegree Q := by
  calc
    Q < 2 ^ Nat.size Q := Nat.lt_size_self Q
    _ ≤ 3 ^ Nat.size Q := Nat.pow_le_pow_left (by decide) _
    _ ≤ 3 ^ extensionDegree Q := Nat.pow_le_pow_right (by decide) (by unfold extensionDegree; omega)

theorem produce_r_ge_two (x : Input) : 2 ≤ (produce x).r := Asymptotic.layoutR_ge_two _
theorem produce_t_pos (x : Input) : 0 < (produce x).t := precision_pos _ _
theorem produce_d_pos (x : Input) : 0 < (produce x).d := extensionDegree_pos _
theorem produce_J_pos (x : Input) : 0 < (produce x).J := Nat.succ_pos _

theorem produce_epsilonDen_pos (x : Input) (hb : 0 < x.occurrence) :
    0 < (produce x).epsilonDen := by
  have hr := Asymptotic.layoutR_ge_two x.freeCount
  have hL := Asymptotic.L_pos x.freeCount
  dsimp [produce]
  positivity

/-- All runtime guards are integer comparisons. Spectral feasibility follows
from the proved schedule and is never tested by a real-number oracle. -/
def Guard (x : Input) : Prop :=
  0 < x.freeCount ∧ x.freeCount ≤ x.ambient ∧ 0 < x.clauses ∧
  0 < x.occurrence ∧ 0 < x.arity ∧ x.freeCount ≤ x.incidences ∧
  2 ≤ (produce x).Q ∧ 4 * (produce x).R ≤ (produce x).Q ∧
  4 * (x.occurrence + x.arity) * (produce x).N ^ 2 *
      (produce x).epsilonDen ^ 2 ≤ x.incidences ∧
  16 * (produce x).Q * (produce x).r ^ 2 ≤ x.freeCount

instance instDecidableGuard (x : Input) : Decidable (Guard x) := by unfold Guard; infer_instance

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

theorem extensionDegree_card_bound (Q : ℕ) :
    3 ^ extensionDegree Q ≤ 16 * (Q + 1) ^ 2 := by
  have h : 2 ^ extensionDegree Q ≤ 4 * (Q + 1) := by
    rw [extensionDegree, pow_succ]
    have := two_pow_size_le Q
    omega
  calc
    3 ^ extensionDegree Q ≤ 4 ^ extensionDegree Q := Nat.pow_le_pow_left (by decide) _
    _ = (2 ^ extensionDegree Q) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ (4 * (Q + 1)) ^ 2 := Nat.pow_le_pow_left h _
    _ = 16 * (Q + 1) ^ 2 := by ring

def fieldCard (x : Input) : ℕ := 3 ^ (produce x).d

theorem fieldCard_le (x : Input) : fieldCard x ≤ 16 * ((produce x).Q + 1) ^ 2 :=
  extensionDegree_card_bound _

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCrudeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

open Asymptotic

def loopCap (x : Input) : ℕ := 1000000*(magnitude x)^6

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Guard

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 8 12

theorem comparePorts_injective : Function.Injective comparePorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [comparePorts]

end SubexponentialSAT.SqrtLog.Setup.Guard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramLog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev LogData := StructuredProgram.State 3 3

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseMastersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open BitProgram StructuredCalls

def unary (bits : List Bool) : List Bool := List.replicate (CounterPrograms.value bits) true

theorem unaryPorts_injective (dst : Fin 14) (h11 : dst ≠ 11) (h12 : dst ≠ 12) :
    Function.Injective (unaryPorts dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [unaryPorts]

def unaryCopyBound (bits : List Bool) : ℕ :=
  7 * bits.length + 5 + CounterConversions.runtimeBound bits

end SubexponentialSAT.SubexpClauseMastersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramSerializationUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, preserving serialization of parameter words as unary loop counters.
This is the checked bit conversion already used for clause-factor masters. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic

abbrev unaryCopyBound := SubexpClauseMastersProgram.unaryCopyBound

/-- The value-dependent cost is exposed; unary serialization is never free. -/
theorem unaryCopyBound_eq (bits : List Bool) :
    unaryCopyBound bits=7*bits.length+5+32*(BinaryArithmetic.toNat bits+1)*(bits.length+1) := by
  simp only [unaryCopyBound,SubexpClauseMastersProgram.unaryCopyBound,
    CounterConversions.runtimeBound,CounterPrograms.value_eq_toNat]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open BitProgram StructuredCalls StructuredProgram BinaryArithmetic

def upperFor (x : Input) (p : Parameters) (j : Fin 10) : ℕ :=
  match j.val with
  | 0 => x.freeCount
  | 1 => x.ambient
  | 2 => x.clauses
  | 3 => x.occurrence
  | 4 => x.arity
  | 5 => x.incidences
  | 6 | 7 => p.Q
  | 8 => x.incidences
  | _ => x.freeCount

def lowerFor (x : Input) (p : Parameters) (j : Fin 10) : ℕ :=
  match j.val with
  | 0 | 2 | 3 | 4 => 1
  | 1 | 5 => x.freeCount
  | 6 => 2
  | 7 => 4*p.R
  | 8 => 4*(x.occurrence+x.arity)*p.N^2*p.epsilonDen^2
  | _ => 16*p.Q*p.r^2

def upper (x : Input) := upperFor x (produce x)
def lower (x : Input) := lowerFor x (produce x)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

theorem lengthBound_mono (v l l' : Fin 64 → ℕ) (h : ∀ a, l a ≤ l' a) (i : Instr) :
    lengthBound v l i ≤ lengthBound v l' i := by
  cases i <;> simp only [lengthBound]
  all_goals first | exact le_rfl | apply h | (gcongr <;> apply h)

theorem cost_mono (v l l' : Fin 64 → ℕ) (h : ∀ a, l a ≤ l' a) (i : Instr) :
    cost v l i ≤ cost v l' i := by
  cases i <;> simp only [cost]
  all_goals first | exact le_rfl | apply h | (gcongr <;> apply h)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic Asymptotic

def setupScale (x : Input) (l : Fin 8 → ℕ) : ℕ := loopCap x+∑ i, l i

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatchCost -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalCoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The multiplication and predecessor prefix of the actual interval-start
initializer. All widths refer to physical input words, including padding. -/

namespace SubexponentialSAT.SubexpIntervalCoreProgram

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 8 32

end SubexponentialSAT.SubexpIntervalCoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramIntervalBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

/-- The actual centered start is at most the number of evaluation nodes. -/
theorem intervalStart_le_Q (r Q R : ℕ) (hr : 0 < r) :
    Subexp.TailInterval.intervalStart r Q R ≤ Q := by
  rw [← SubexpIntervalStart.value_eq_intervalStart r Q R hr]
  have hd : 0 < 2*r := by omega
  change ((Q-1)*(r-1)-R*r)/(2*r) ≤ Q
  calc
    _ ≤ (Q*(2*r))/(2*r) := Nat.div_le_div_right
      ((Nat.sub_le _ _).trans (Nat.mul_le_mul (Nat.sub_le Q 1) (by omega)))
    _ = Q := Nat.mul_div_cancel Q hd

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid restoration of the isolated count-query worker. The selector's mass
contract requires literal frame preservation, so all 340 worker stacks and all
22 registers are restored by actual instructions after exporting the score. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Cleanup

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def reset {r s : ℕ} : List (Fin r) → Cmd r s
  | [] => .base .skip
  | i::is => .seq (.base (.atom (.set i false))) (reset is)

end SubexponentialSAT.SqrtLog.LeafProgram.Cleanup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCleanupWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full cleanup for the wider leaf worker including setup pockets. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 40 768
def blank : Data := ⟨fun _ => false,fun _ => []⟩
def bytes (a : Data) : ℕ := ((List.finRange 768).map (fun i => (a.stacks i).length)).sum
def budget (a : Data) : ℕ := 2*bytes a+2347

end SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHashParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete placement of the selector's numerical preparation in the full
leaf bank. Formula784 and answer787 are outside this routine;782 contains the
actual binary clause count produced by ClauseCount.caller. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

open SubexponentialSAT BitProgram StructuredCalls

def ports : Execution.HashParameters.Ports 40 896 :=
  ⟨registers,stackMap,Fin.castAdd_injective 16 24,by decide⟩

@[simp] theorem ambient_port : ports.stack 14 = 785 := rfl
@[simp] theorem clauses_port : ports.stack 15 = 782 := rfl
@[simp] theorem occurrence_port : ports.stack 16 = 786 := rfl

end SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Layout/source metadata are parked outside the native arithmetic bank.
CRT and scalar arithmetic use several ports128..141 as scratch; these values
are therefore physically reloaded for each node and cleared before CRT. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

def lowPorts : List (Fin 768) := (List.finRange 14).map low

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete readback/transfer adapter for the marked-query caller. The CRT
result is at261; the exact little-endian integer is delivered at323. The
unread marked-reference stream320 and mass accumulator322 are framed. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 19 330

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Joined per-query core. Mathematical values below describe physical input
words and computed outputs; they are not extra machine inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Query where
  clauses : List (List Bool)
  codes : Fin clauses.length → List ℕ
  rows : HashScopeProgram.RawTable.Rows clauses.length
  mark : Option (Fin clauses.length)
  index : List Bool
  width : List Bool
  modulus : List Bool
  ambient : List Bool

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTotals
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed finite-sum and maximum specifications of the native variable scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

theorem totals_occurrence_le_iff (scopes : List (List ℕ)) (v : ℕ)
    (mask : List Bool) (t : Totals) (B : ℕ) :
    (variableTotals scopes v mask t).occurrence ≤ B ↔
      t.occurrence ≤ B ∧
        ∀ i : Fin mask.length, mask.get i = false → max 1 (degree scopes (v+i.val)) ≤ B := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    rw [variableTotals, ih]
    cases b <;>
      simp [Totals.add, Fin.forall_fin_succ,
        Nat.add_comm, Nat.add_left_comm, and_assoc, and_left_comm, and_comm]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact owner order of the neutral factors emitted by the native scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput

theorem lowOwners_mem (v u : ℕ) (mask : List Bool) :
    u ∈ lowOwners v mask ↔
      ∃ i : Fin mask.length, v+i.val = u ∧ mask.get i = false := by
  induction mask generalizing v with
  | nil => simp [lowOwners]
  | cons b bs ih =>
    constructor
    · intro h
      cases b
      · change u ∈ v :: lowOwners (v+1) bs at h
        rcases List.mem_cons.mp h with h | h
        · refine ⟨⟨0, by simp⟩, ?_, rfl⟩
          simpa only [Fin.val_zero, Nat.add_zero] using h.symm
        · obtain ⟨i, hi, hb⟩ := (ih (v+1)).mp h
          refine ⟨i.succ, ?_, hb⟩
          simp only [Fin.val_succ]
          omega
      · change u ∈ lowOwners (v+1) bs at h
        obtain ⟨i, hi, hb⟩ := (ih (v+1)).mp h
        refine ⟨i.succ, ?_, hb⟩
        simp only [Fin.val_succ]
        omega
    · rintro ⟨i, hi, hb⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have hb' : b = false := hb
        subst b
        change u ∈ v :: lowOwners (v+1) bs
        apply List.mem_cons.mpr
        left
        simpa only [Fin.val_zero, Nat.add_zero] using hi.symm
      · have hj : (v+1)+j.val = u := by
          simp only [Fin.val_succ] at hi
          omega
        have hg : bs.get j = false := hb
        have hm := (ih (v+1)).mpr ⟨j, hj, hg⟩
        cases b
        · exact List.mem_cons_of_mem v hm
        · exact hm

theorem lowOwners_bounds (v u : ℕ) (mask : List Bool) (hu : u ∈ lowOwners v mask) :
    v ≤ u ∧ u < v+mask.length := by
  obtain ⟨i, hi, _⟩ := (lowOwners_mem v u mask).mp hu
  have := i.isLt
  omega

theorem lowOwners_nodup (v : ℕ) (mask : List Bool) : (lowOwners v mask).Nodup := by
  induction mask generalizing v with
  | nil => simp [lowOwners]
  | cons b bs ih =>
    have hn : v ∉ lowOwners (v+1) bs := by
      intro hv
      have := (lowOwners_bounds (v+1) v bs hv).1
      omega
    cases b <;> simp [lowOwners, ih, hn]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

abbrev pop : Cmd 3 3 := .base (.atom (.pop 0 2 1))

abbrev transfer : Cmd 3 3 := .call (StackRoutines.transferProgram 1 2 0 1)

abbrev setFirst : Cmd 3 3 := .base (.atom (.set 0 false))

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankMagnitude
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual raw owner-fiber length controls separately stored signed
components, so the executed shift is bounded without canonical signs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open PackingCallerProgram LeafParametersProgram BucketProgram.ProducedRank

 theorem fiber_length_ofFn {D : ℕ} (ps : Fin D → ℕ × ℕ) (query start : ℕ) :
    (LayoutOwnerFiberProgram.fiberIndices query start (List.ofFn ps)).length=
      ∑ i : Fin D,if (ps i).1=query then 1 else 0 := by
  induction D generalizing start with
  | zero => simp [LayoutOwnerFiberProgram.fiberIndices]
  | succ D ih =>
    rw [List.ofFn_succ,LayoutOwnerFiberProgram.fiberIndices,Fin.sum_univ_succ]
    by_cases h : (ps 0).1=query <;> simp [h,ih,Nat.add_comm]

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native primitives used by the companion-table preparation machine. -/
namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Data := State 8 27

abbrev state (regs : Fin 8 → Bool) (s : Store) : Data := ⟨regs, tapes s⟩

abbrev copy (src dst : Fin 27) : Cmd 8 27 := .call (copyProgram src dst 23 1 3)
abbrev transfer (src dst : Fin 27) : Cmd 8 27 := .call (transferProgram src dst 1 3)

def afterClear (d : Data) (dst : Fin 27) : Data :=
  ⟨readRegs d.regs 1 3 none, clearStacks dst d.stacks⟩
def afterCopy (d : Data) (src dst : Fin 27) : Data :=
  ⟨readRegs d.regs 1 3 none, copyStacks src dst d.stacks⟩

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev popCount : Cmd 8 27 := .base (.atom (.pop 11 1 3))

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end


