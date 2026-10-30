-- Prove2me | Definitions.Def_OAIQ081S038
-- name    : OAIQ081S038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:32:29.876355+00:00
-- url     : https://prove2.me/theorems/856dcded-e788-4b88-bc9b-f1adf26e55f5
-- title:
--   Definitions bundle OAIQ081S038 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 105 declarations of OpenAI's Lean: 55 definitions, 1 instance and 49 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds.expansionBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds.markedServiceBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds.tableBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch.copyID`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch.readFlag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorID.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorID.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorID.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters.parkPairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.LocalState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.descendingMask`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.castRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Width.arithmeticEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.ringAlgebra`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeResetAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.decoded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.padded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.peek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.takeTwo`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.digits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.prepareRadix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.stream`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.Machine.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.Machine.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.popRound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.afterClear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.afterCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.afterPop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.afterRead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.afterTransfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.pop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.startBlock` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramFactorBase`, `SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsPolynomial`, `SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsServices`, `SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch`, `SubexponentialSAT_SqrtLog_LeafProgramFactorID`, `SubexponentialSAT_SqrtLog_LeafProgramHash`, `SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters`, `SubexponentialSAT_SqrtLog_LeafProgramMass`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedSpec`, `SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup`, `SubexponentialSAT_SqrtLog_LeafProgramQueryWidthArithmetic`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendConstants`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope`, `SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram`, `SubexponentialSAT_SqrtLog_RingNodeProgram`, `SubexponentialSAT_SqrtLog_RingNodeProgramModel`, `SubexponentialSAT_SqrtLog_RingNodeProgramPrepare`, `SubexponentialSAT_SqrtLog_RingProgramTableBasic`, `SubexponentialSAT_SqrtLog_RingProgramTableMachine`, `SubexponentialSAT_SqrtLog_RingProgramTablePowers`, `SubexponentialSAT_SqrtLog_RingProgramTableStep`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramRowStep`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramRows`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramSemantics`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep`, `SubexponentialSAT_SubexpBasePUnranking`, `SubexponentialSAT_SubexpFactorProgram`, `SubexponentialSAT_SubexpFieldRowPreparation`, `SubexponentialSAT_SubexpKeyPadProgram`, `SubexponentialSAT_SubexpTaylorFrames`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S008`, `OAIQ081S009`, `OAIQ081S011`, `OAIQ081S015`, `OAIQ081S016` and `OAIQ081S017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S059` and `OAIQ081S060`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008
import Definitions.Def_OAIQ081S009
import Definitions.Def_OAIQ081S011
import Definitions.Def_OAIQ081S015
import Definitions.Def_OAIQ081S016
import Definitions.Def_OAIQ081S017

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Wide native factor arithmetic and paid tape movement. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

abbrev Code := Cmd 40 768

def copy (src dst : Fin 768) : Code :=
  .call (StackRoutines.copyProgram src dst 159 0 1)


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

variable {V C A : Type*}

def ringAlgebra (R : Type*) [CommRing R] : Algebra R :=
  ⟨0, 1, (· + ·), (· * ·), Neg.neg⟩

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFactorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete factor-row evaluation primitives

Programs in this module have fixed Boolean registers and fixed finite control.
Inputs are working copies on stacks. All costs below are actual instruction
traces; neither arithmetic comparisons nor semantic predicates are instructions.
-/

namespace SubexponentialSAT.SubexpFactorProgram

open SubexponentialSAT.BitProgram

theorem allZero_iff_toNat_zero (bs : List Bool) :
    allZero bs = true ↔ BinaryArithmetic.toNat bs = 0 := by
  induction bs with
  | nil => simp [allZero]
  | cons b bs ih => cases b <;> simp [allZero, BinaryArithmetic.toNat, ih]

theorem toNat_append (low high : List Bool) :
    BinaryArithmetic.toNat (low ++ high) =
      BinaryArithmetic.toNat low + 2 ^ low.length * BinaryArithmetic.toNat high := by
  induction low with
  | nil => simp
  | cons b low ih => simp only [List.cons_append, BinaryArithmetic.toNat_cons,
      List.length_cons, ih, pow_succ]; ring

theorem toNat_lt_pow_length (bs : List Bool) :
    BinaryArithmetic.toNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases b <;> simp only [BinaryArithmetic.toNat_cons, BinaryArithmetic.bitVal_false,
      BinaryArithmetic.bitVal_true, List.length_cons, pow_succ] <;> omega

/-- A padded little-endian label is below `2^b` exactly when all bits beyond
its `b` low bits are zero. No comparison is being assigned unit cost. -/
theorem unary_validity_iff (low high : List Bool) :
    allZero high = true ↔ BinaryArithmetic.toNat (low ++ high) < 2 ^ low.length := by
  rw [allZero_iff_toNat_zero, toNat_append]
  have hl := toNat_lt_pow_length low
  have hp : 0 < 2 ^ low.length := pow_pos (by decide) _
  constructor
  · intro h; simp [h, hl]
  · intro h
    by_contra hz
    have hge : 1 ≤ BinaryArithmetic.toNat high := by omega
    have hm := Nat.mul_le_mul_left (2 ^ low.length) hge
    omega

end SubexponentialSAT.SubexpFactorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls

abbrev copyID : Cmd 40 768 := .call (StackRoutines.copyProgram 149 152 359 0 1)
abbrev readFlag : Cmd 40 768 := .base (.atom (.peek 706 7 0))

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorID
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Retain the parsed factor ID and prepare the bare unary counter expected
by the isolated source-row/incidence worker.  Zero is represented by the
empty unary tape; it is not confused with a missing source record. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorID

open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768
abbrev command : Cmd 40 768 :=
  .seq (.call (StackRoutines.copyProgram 149 556 359 0 1))
    (.base (.atom (.pop 556 0 1)))

def output (a : Data) (factor : ℕ) : Data :=
  ⟨readRegs (readRegs a.regs 0 1 none) 0 1 (some false),
    Function.update a.stacks 556 (List.replicate factor true)⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorID

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBasePUnranking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual base-p digit extraction

A digit is obtained by the checked binary long-division program. Its remainder
is copied to the fixed width of the modulus, while the padded high bits are
removed. Repeated extraction uses the quotient as the next rank. The modulus,
arity, and all widths are data; the instruction table is fixed.
-/

namespace SubexponentialSAT.SubexpBasePUnranking

open BitProgram StructuredCalls StackRoutines
open BinaryArithmetic

@[simp] theorem tapes_update_0 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 0 word =
      tapes word modulus rank quotient arity width scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_6 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 6 word =
      tapes rem modulus word quotient arity width scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_7 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 7 word =
      tapes rem modulus rank word arity width scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_8 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 8 word =
      tapes rem modulus rank quotient word width scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_9 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 9 word =
      tapes rem modulus rank quotient arity word scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_10 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 10 word =
      tapes rem modulus rank quotient arity width word rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_11 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 11 word =
      tapes rem modulus rank quotient arity width scratch word output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_12 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 12 word =
      tapes rem modulus rank quotient arity width scratch rev word := by
  funext j; fin_cases j <;> simp [tapes]

def state (regs : Fin 8 → Bool) (modulus rank arity rev output : List Bool) : State 8 13 :=
  ⟨regs, tapes [] modulus rank [] arity [] [] rev output⟩

abbrev popArity : Cmd 8 13 := .base (.atom (.pop 8 1 3))

def afterRead (regs : Fin 8 → Bool) (modulus rank arity rev output : List Bool) : State 8 13 :=
  state (readRegs regs 1 3 arity.head?) modulus rank arity.tail rev output

end SubexponentialSAT.SubexpBasePUnranking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFieldRowPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving preparation of a local field-label row

Copy the enumerator's rank and the factor's unary arity into the checked
unranking routine, produce the fixed-width digit stream, and clear the padded
final quotient. The modulus, rank master, and arity master are preserved.
-/

namespace SubexponentialSAT.SubexpFieldRowPreparation

open BitProgram StructuredCalls StackRoutines

theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

def data (regs : Fin 8 → Bool)
    (modulus rankMaster arityMaster rank arity output : List Bool) : State 8 15 :=
  ⟨regs, tapes modulus rankMaster arityMaster rank arity output⟩

theorem stackPort_injective : Function.Injective stackPort := by
  intro i j h
  apply Fin.ext
  simpa [stackPort] using congrArg (fun x : Fin 15 => x.val) h

end SubexponentialSAT.SubexpFieldRowPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical program generating all nonzero radix nodes up to a runtime
bound. The bound counts down, so prepending each row gives ascending order. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation SubexpBasePUnranking SubexpEnumerationProgram
open BinaryArithmetic SubexpLiftRing

/-- Canonical padded radix digits, least significant coefficient first. -/
def digits (B p : ℕ) : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => fixedBits B (n % p) ++ digits B p k (n / p)

@[simp] theorem digits_length (B p k n : ℕ) : (digits B p k n).length = k * B := by
  induction k generalizing n with
  | zero => simp [digits]
  | succ k ih => simp [digits, ih, Nat.add_mul, Nat.add_comm]

/-- Nodes 1 through Q in order. This is a specification, not an instruction. -/
def stream (B p d : ℕ) : ℕ → List Bool
  | 0 => []
  | Q + 1 => stream B p d Q ++ digits B p d (Q + 1)

@[simp] theorem stream_length (B p d Q : ℕ) :
    (stream B p d Q).length = Q * (d * B) := by
  induction Q with
  | zero => simp [stream]
  | succ Q ih => simp [stream, ih, Nat.add_mul]

theorem value_eq_toNat (xs : List Bool) : value xs = BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp_all [value, BinaryArithmetic.toNat, bitVal]

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical radix generator emits precisely the coefficient encoding of
nodes in the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BinaryArithmetic SubexpLiftRing SubexpQuarticRing

theorem digits_eq_ofFn (B p d n : ℕ) :
    digits B p d n =
      (List.ofFn fun j : Fin d => fixedBits B (n / p^j.val % p)).flatten := by
  induction d generalizing n with
  | zero => simp [digits]
  | succ d ih =>
    simp only [digits, List.ofFn_succ, List.flatten_cons, Fin.val_zero, pow_zero,
      Nat.div_one, Fin.val_succ]
    rw [ih]
    simp_rw [pow_succ', Nat.div_div_eq_div_mul]

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bounds for the measured native factor services and their paid cleanup.
The retained-key capacity remains an explicit argument of every envelope. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps

def tableBound (B d n u J N : ℕ) : ℕ :=
  n*(2*n+2*Cost.bytesBound B d n u J N+2)

def markedServiceBound (B d n u J N k : ℕ) : ℕ :=
  k*(6*(2*n+1)+Cost.literalBound B d n u J N+7)+
    63*Cost.bytesBound B d n u J N+2*tableBound B d n u J N+
    Cost.productBound B d n u J N+66

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform numerical bounds. Z bounds encoded sizes and retained capacity,
not merely the bit length of the original formula. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open HashCircuitProgram

def expansionBound (b ml m sourceLength weightLength count : ℕ) : ℕ :=
  3+count*(HashInputProgram.Loop.termBudget b ml m sourceLength weightLength sourceLength+4)

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

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

def parkPairs : List (Fin 768 × Fin 768) := (List.finRange 14).map fun i => (low i,high i)

theorem park_valid : ∀ p ∈ parkPairs, p.1 ≠ p.2 ∧ p.1 ≠ 684 ∧ (684 : Fin 768) ≠ p.2 := by
  intro p hp
  simp only [parkPairs,List.mem_map,List.mem_finRange,true_and] at hp
  obtain ⟨i,rfl⟩ := hp
  constructor
  · intro h; have hv := congrArg Fin.val h; change 128+i.val=730+i.val at hv; omega
  constructor
  · intro h; have hv := congrArg Fin.val h; change 128+i.val=684 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change 684=730+i.val at hv; omega

theorem park_nodup : (parkPairs.map Prod.snd).Nodup := by
  simpa only [parkPairs,List.map_map,Function.comp_def] using
    (List.nodup_finRange 14).map high_injective
theorem park_sep : ∀ p ∈ parkPairs, ∀ q ∈ parkPairs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [parkPairs,List.mem_map,List.mem_finRange,true_and] at hp hq
  obtain ⟨i,rfl⟩ := hp
  obtain ⟨j,rfl⟩ := hq
  intro h
  have hv := congrArg Fin.val h
  change 128+i.val=730+j.val at hv
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev LocalState := State 8 3

def data (regs : Fin 8 → Bool) (acc next : List Bool) : LocalState :=
  ⟨regs, BinaryPrograms.Add.stackState acc next []⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-coordinate interpretation of the physical high tuple.
The order is descending original ID, and every rank including the unique
empty tuple participates in the count. No coordinate compaction is used. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount
open HighIncidenceProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def descendingMask (H : Finset (Fin n)) : List Bool :=
  (Order.coordinates n).map (fun v=>decide (v∈H))

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

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

theorem loadRegisters_injective : Function.Injective loadRegisters := by decide

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem triplePorts_injective : Function.Injective triplePorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 27 => x.val) h)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKeyPadProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed five-instruction routine copies a forward key for exactly the
number of bits in a unary width counter. Empty input reads as false, so the
same routine truncates long keys and zero-pads short keys. -/

namespace SubexponentialSAT.SubexpKeyPadProgram

open BitProgram SubexpExponentProgram

abbrev program : Program 2 3 5 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.pop 1 0 1 1, .branch 1 2 4, .pop 0 0 1 3, .push 2 0 0, .halt]

abbrev cfg (pc : Option (Fin 5)) (regs : Fin 2 → Bool)
    (input counter output : List Bool) : Cfg 2 3 5 :=
  ⟨pc, regs, storage input counter output⟩

theorem exit_trace (regs : Fin 2 → Bool) (input output : List Bool) :
    Trace program 3 (cfg (some 0) regs input [] output)
      (cfg none (readRegs regs 0 1 none) input [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg, storage,
    readRegs, Function.update_apply]

end SubexponentialSAT.SubexpKeyPadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTaylorFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control conversion of a flat coefficient stream into an ordered
list of framed coefficients. Runtime counters determine the coefficient
width and requested count. Missing high coefficients are actually read as
zero by the existing padded-reader program. -/

namespace SubexponentialSAT.SubexpTaylorFrames

open BitProgram StructuredCalls
open SubexpExponentProgram

theorem padRegs_injective : Function.Injective padRegs := by decide

abbrev paddedRead : Cmd 5 9 :=
  .call (ProgramLinking.liftProgram SubexpKeyPadProgram.program padRegs padStacks)

def recordBytes (bits : List Bool) : List Bool := true :: Encoding.frame bits

abbrev guard : Cmd 5 9 := .base (.atom (.peek 3 0 1))
abbrev popCount : Cmd 5 9 := .base (.atom (.pop 3 0 1))
abbrev finish : Cmd 5 9 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 6 0)))
      (.call (StackRoutines.transferProgram 6 8 (0 : Fin 5) 1)))

def framedBytes (B n : ℕ) (input : List Bool) : List Bool :=
  (chunks B n input).flatMap recordBytes

theorem framedBytes_length (B n : ℕ) (input : List Bool) :
    (framedBytes B n input).length = n * (2 * B + 2) := by
  induction n generalizing input with
  | zero => simp [framedBytes, chunks]
  | succ n ih =>
      change (recordBytes (padTake B input) ++ framedBytes B n (input.drop B)).length = _
      rw [List.length_append, ih]
      simp only [recordBytes, List.length_cons, Encoding.length_frame, padTake_length,
        Nat.add_mul, Nat.one_mul]
      omega

theorem encode_chunks (B n : ℕ) (input : List Bool) :
    Encoding.encodeList id (chunks B n input) = framedBytes B n input ++ [false] := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih => simp [chunks, framedBytes, recordBytes, Encoding.encodeList, ih, List.append_assoc]

end SubexponentialSAT.SubexpTaylorFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical layout for native ring preparation.

The local setup has 32 registers and 640 stacks.  It can be lifted into the
40-register/768-stack leaf caller.  The collector's stacks 320--339 are never
used.  Arithmetic metadata is written directly to its native consumer port;
temporary search, scalar, table, and node data have disjoint workspaces.
-/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls

theorem parameters_injective : Function.Injective parameters := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [parameters] at this
  omega

theorem constant_one_injective : Function.Injective (constant 207) := by decide
theorem constant_minusOne_injective : Function.Injective (constant 211) := by decide
theorem constant_zero_injective : Function.Injective (constant 280) := by decide
theorem nodes_injective : Function.Injective nodes := by decide

theorem idempotent_injective : Function.Injective idempotent := by
  intro i j hij
  apply Fin.ext
  have h := congrArg (fun x : Fin 640 => x.val) hij
  simp only [idempotent] at h
  omega

theorem wideRegisters_injective : Function.Injective wideRegisters := by decide

theorem wideStacks_injective : Function.Injective wideStacks := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Fin 768 => x.val) hij

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid word movement and binary-to-unary conversion used by ring setup.
The helpers update actual tapes; a state equality is never used as a free
copy, clear, or counter conversion. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls StackRoutines

theorem unaryRegisters_injective : Function.Injective unaryRegisters := by decide

theorem unaryPorts_injective (src dst : Fin 640) (hs : src.val < 625)
    (hd : dst.val < 625) (hne : src ≠ dst) :
    Function.Injective (unaryPorts src dst) := by
  intro i j hij
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · exact hj0.symm
    by_cases hj1 : j = 1
    · subst j
      exfalso
      apply hne
      simpa [unaryPorts] using hij
    · have hh := congrArg Fin.val hij
      simp [unaryPorts, hj0, hj1] at hh
      omega
  by_cases hi1 : i = 1
  · subst i
    by_cases hj0 : j = 0
    · subst j; simp [unaryPorts, Ne.symm hne] at hij
    by_cases hj1 : j = 1
    · exact hj1.symm
    · have hh := congrArg Fin.val hij
      simp [unaryPorts, hj0, hj1] at hh
      omega
  by_cases hj0 : j = 0
  · subst j
    have hh := congrArg Fin.val hij
    simp [unaryPorts, hi0, hi1] at hh
    omega
  by_cases hj1 : j = 1
  · subst j
    have hh := congrArg Fin.val hij
    simp [unaryPorts, hi0, hi1] at hh
    omega
  apply Fin.ext
  have hh := congrArg Fin.val hij
  simp [unaryPorts, hi0, hi1, hj0, hj1] at hh
  omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed scanner widens consecutive two-bit coefficients using a runtime
width tape. The original width is preserved, and all bit movement is paid. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularPrograms
abbrev Code := Cmd 8 7

def takeTwo : Code := .seq (.base (.atom (.pop 0 0 6)))
  (.seq (.base (.atom (.pop 0 1 6)))
    (.seq (.base (.atom (.push 3 1))) (.base (.atom (.push 3 0)))))

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The word list is a specification value; the machine scans its flat tape. -/
def padded (width : List Bool) (words : List (List Bool)) : List Bool :=
  (words.map (ModularArithmetic.padTo width)).flatten

@[simp] theorem padded_nil (width : List Bool) : padded width []=[] := rfl
@[simp] theorem padded_cons (width word : List Bool) (words : List (List Bool)) :
    padded width (word::words)=ModularArithmetic.padTo width word++padded width words := rfl
@[simp] theorem padded_length (width : List Bool) (words : List (List Bool)) :
    (padded width words).length=words.length*width.length := by
  induction words with
  | nil => simp
  | cons w ws ih => simp [ih,Nat.add_mul,Nat.add_comm,ModularArithmetic.padTo_length]

def peek : Code := .base (.atom (.peek 0 0 7))

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


/-! Exact byte bridge from canonical F3 coefficients to the supplied-polynomial
ring model. The program itself has no degree or width parameter. -/


/-! Search-to-table ABI. The search has 22 registers and 28 stacks. In particular,
stack24 may contain unread candidates and is outside this adapter's ports. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Constant-control preparation of the padded radix and the final node stream.
The only supplied words are zero padding, binary Q, and unary d. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation BinaryArithmetic SubexpLiftRing

/-- The second successful pop leaves `present = true`, reused for both pushes. -/
abbrev prepareRadix : Cmd 8 15 := .base <|
  .seq (.atom (.pop 5 1 3)) <|
    .seq (.atom (.pop 5 1 3)) <|
      .seq (.atom (.push 5 3)) (.atom (.push 5 3))

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTablePowers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev popRound : Cmd 8 27 := .base (.atom (.pop 26 1 3))

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control primitives for laying out a stored power table.  All indices,
dimensions, and scalar widths are data on unary tapes. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 2 18

def state (regs : Fin 2 → Bool) (s : Store) : Data := ⟨regs, tapes s⟩

abbrev copy (src dst : Fin 18) : Cmd 2 18 := .call (copyProgram src dst 10 0 1)
abbrev transfer (src dst : Fin 18) : Cmd 2 18 := .call (transferProgram src dst 0 1)

def afterClear (d : Data) (dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks dst d.stacks⟩
def afterCopy (d : Data) (src dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩
def afterTransfer (d : Data) (src dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

def afterRead (d : Data) (word : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 5 []) 4 (word ++ d.stacks 4)⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem wordAt_length (rows : List (List Bool)) (i B : ℕ)
    (hi : i < rows.length) (hw : ∀ row ∈ rows, row.length = B) :
    (wordAt rows i).length = B := by
  simpa [wordAt, getElem!_pos, hi] using hw rows[i] (List.getElem_mem hi)

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev pop (port : Fin 18) : Cmd 2 18 := .base (.atom (.pop port 0 1))
def afterPop (d : Data) (port : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks port).head?,
    Function.update d.stacks port (d.stacks port).tail⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev startRow : Cmd 2 18 := .seq (copy 15 16) (copy 1 13)

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev startBlock : Cmd 2 18 := .seq (copy 14 15) (copy 1 12)

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

theorem matrixBits_eq_ofFn (rows : List (List Bool)) (d n start : ℕ) :
    matrixBits rows d start n =
      (List.ofFn fun i : Fin n =>
        (List.ofFn fun j : Fin d => wordAt rows (start+i.val*d+j.val*d)).flatten).flatten := by
  induction n generalizing start with
  | zero => simp [matrixBits]
  | succ n ih =>
      simp [matrixBits, List.ofFn_succ, ih, rowBits_eq_ofFn, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The exact public order: k first, then i, with j varying fastest. -/
theorem layoutBits_eq_ofFn (rows : List (List Bool)) (d n start : ℕ) :
    layoutBits rows d start n =
      (List.ofFn fun k : Fin n => (List.ofFn fun i : Fin d =>
        (List.ofFn fun j : Fin d => wordAt rows (start+k.val+i.val*d+j.val*d)).flatten).flatten).flatten := by
  induction n generalizing start with
  | zero => simp [layoutBits]
  | succ n ih =>
      simp [layoutBits, List.ofFn_succ, ih, matrixBits_eq_ofFn,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem flatten_ofFn_length {n B : ℕ} (f : Fin n → List Bool)
    (h : ∀ i, (f i).length = B) : (List.ofFn f).flatten.length = n*B := by
  have hh := ArrayUpdatePrograms.uniform_flatten_length (List.ofFn f) B (by
    intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact h i)
  simpa using hh

theorem layoutBits_length (rows : List (List Bool)) (d n start B : ℕ)
    (h : ∀ k < n, ∀ i < d, ∀ j < d,
      (wordAt rows (start+k+i*d+j*d)).length = B) :
    (layoutBits rows d start n).length = n*(d*(d*B)) := by
  rw [layoutBits_eq_ofFn]
  apply flatten_ofFn_length
  intro k
  apply flatten_ofFn_length
  intro i
  apply flatten_ofFn_length
  intro j
  exact h k.val k.isLt i.val i.isLt j.val j.isLt

theorem full_layout_length (rows : List (List Bool)) (d B : ℕ)
    (hw : ∀ row ∈ rows, row.length = B)
    (hn : d*(2*d-1) ≤ rows.length) :
    (layoutBits rows d 0 d).length = d^3*B := by
  have h := layoutBits_length rows d d 0 B (by
    intro k hk i hi j hj
    apply wordAt_length rows _ B
    · simpa using (table_index_lt d k i j hk hi hj).trans_le hn
    · exact hw)
  convert h using 1 <;> first | rfl | ring

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable.Machine

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Data := State 8 42

def state (regs : Fin 8 → Bool) (s : Store) (table : List Bool) : Data :=
  ⟨regs, fun i => if h : i.val < 27 then tapes s ⟨i.val, h⟩
    else if i.val = 27 then table else []⟩

end SubexponentialSAT.SqrtLog.RingProgramTable.Machine

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reclamation after one marked or accepted query. The port list is part
of the fixed program syntax. Only the collector, immutable formula/row inputs,
and the outer caller's high ports survive. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

instance instDecidableProtected (i : Fin 768) : Decidable (Protected i) := inferInstanceAs (Decidable
  (i=320 ∨ i=322 ∨ i=323 ∨ i=700 ∨ i=701 ∨ i=707 ∨ i=708 ∨ i=709 ∨ 744 ≤ i.val))

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count precisely the unpinned identifiers in an explicit scope. The mask is
in original coordinate order and the framed natural identifiers are read at
runtime. No arity or other statistic is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

noncomputable def decoded (bits : List Bool) : ℕ := by
  classical
  exact if h : ∃ v, Encoding.encodeNat v = bits then Classical.choose h else 0
@[simp] theorem decoded_encode (v : ℕ) : decoded (Encoding.encodeNat v) = v := by
  classical
  unfold decoded
  split
  · rename_i h
    exact Encoding.encodeNat_injective (Classical.choose_spec h)
  · rename_i h
    exact (h ⟨v,rfl⟩).elim

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def scopeResetAtoms : List (StructuredProgram.Atom 40 768) :=
  [.set 0 false,.set 1 false,.set 2 false,.set 3 false,.set 4 false,
   .set 5 false,.set 6 false,.set 7 false,.set 8 false,.set 9 false,.set 10 false]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A typed factor specification using the original query's row stream and
marked-clause selector. Finite-index transports do not alter stored bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
noncomputable section

def castRows {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m) :
    HashScopeProgram.RawTable.Rows m' :=
  rows.map (List.map (fun a => (Fin.cast h a.1,a.2)))

@[simp] theorem castRows_length {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m) :
    (castRows h rows).length=rows.length := by simp [castRows]

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryWidthArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed ordinary polynomial bounds the literal ring, interpolation and
layout-denominator setup budgets, including their staging copies. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT LeafParametersProgram SubexpLiftRing CostAssembly.Polynomial

def arithmeticEnvelope (C e S : ℕ) : ℕ :=
  ringEnvelope C e S + LayoutDenominatorProgram.polynomialBudget S (2*S) S +
    600*(S+ringEnvelope C e S+3)

theorem interpolationEnvelope_ordinary : Ordinary interpolationEnvelope := by
  refine ⟨7000000000,9,?_⟩
  intro S
  let T := S+1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hS : S ≤ T := by dsimp [T]; omega
  have hS2 : 2*S+1 ≤ 2*T := by dsimp [T]; omega
  have ht2 : T ≤ T^2 := by simpa using Nat.pow_le_pow_right hT (show 1 ≤ 2 by decide)
  have ht0 : 1 ≤ T^5 := Nat.one_le_pow _ _ hT
  have ht25 : T^2 ≤ T^5 := Nat.pow_le_pow_right hT (by decide)
  have hleft : 16*(S+1)^2+S+1 ≤ 17*T^2 := by dsimp [T] at *; nlinarith
  have hright : 100000*(S+1)^3*(2*S+1)^2+2*S*S+1 ≤ 400003*T^5 := by
    have hmain : 100000*(S+1)^3*(2*S+1)^2 ≤ 400000*T^5 := by
      calc
        _ ≤ 100000*T^3*(2*T)^2 := by dsimp [T]; gcongr
        _ = _ := by ring
    have hsquare : 2*S*S ≤ 2*T^2 := by nlinarith
    nlinarith only [hmain,hsquare,ht25,ht0]
  unfold interpolationEnvelope
  calc
    _ ≤ 1000*T^2*(17*T^2)*(400003*T^5) := by gcongr
    _ ≤ 7000000000*(S+1)^9 := by dsimp [T]; nlinarith [Nat.zero_le ((S+1)^9)]

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
end


