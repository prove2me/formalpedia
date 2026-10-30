-- Prove2me | Definitions.Def_OAIQ081S011
-- name    : OAIQ081S011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:23:39.07059+00:00
-- url     : https://prove2.me/theorems/ac557cb9-9618-4e3d-a4ed-10e4d39d6e3f
-- title:
--   Definitions bundle OAIQ081S011 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 69 definitions, 2 inductive types or structures, 1 instance and 27 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter.registers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.replaceThree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.replaceTwo`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.addPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.basePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.buildFinalPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatFinalPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.initial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.initialBuildPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.natScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.negativePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.normalizePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.positivePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.scanPrior`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.zeroRecord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.scanDouble`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.scanPrior`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.shift`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram.polynomialBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram.powerBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram.powerValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.bank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.pairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.port`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.registers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.KillsIntegerKernel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.RationalRowSpan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.signature`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.bodyBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.ownerRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.ownerStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutHeadPullback.headOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.bankPort` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramLift`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramMath`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramSemantics`, `SubexponentialSAT_SqrtLog_LayoutCoefficientRecurrence`, `SubexponentialSAT_SqrtLog_LayoutCoefficientRecurrenceScan`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgram`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryReplay`, `SubexponentialSAT_SqrtLog_LayoutExactBuckets`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove`, `SubexponentialSAT_SqrtLog_LayoutHeadPullback`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCompare`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramVisit`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarStep`, `SubexponentialSAT_SqrtLog_LayoutPullback`, `SubexponentialSAT_SqrtLog_LayoutScalarEmitter`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramOuterCarried`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts`, `SubexponentialSAT_SqrtLog_PackingProgramArithmetic`, `SubexponentialSAT_SqrtLog_RowSelectionProgramAdd`, `SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic`, `SubexponentialSAT_SqrtLog_RowSelectionProgramEntriesEmit`, `SubexponentialSAT_SqrtLog_RowSelectionProgramStream`, `SubexponentialSAT_SubexpNodeIndexProgram`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_Subexp_BlockSearchProgram`, `SubexponentialSAT_Subexp_MatrixScanProgram`, `SubexponentialSAT_Subexp_MatrixScanSemantics`, `SubexponentialSAT_Subexp_PackingFrontendData`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S033`, `OAIQ081S034`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S040` and `OAIQ081S042`; the statements `OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_ProductCallback_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Multiplier_prepareMultiplier_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete execution of the fixed F₃ dot product, including initialization,
serialization of its output, the final halt, and primitive simulation. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

theorem zipWith_ofFn {A B C : Type*} (f : A → B → C) (n : ℕ) :
    ∀ (a : Fin n → A) (b : Fin n → B),
      List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
      intro a b
      simp only [List.ofFn_succ, List.zipWith_cons_cons]
      rw [ih]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed invocation of the fixed three-stack prefix and dot programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

def replaceThree {S : ℕ} (ports : Fin 3 ↪ Fin S) (a b c : List Bool)
    (stk : Fin S → List Bool) : Fin S → List Bool :=
  Function.update (Function.update (Function.update stk (ports 0) a) (ports 1) b) (ports 2) c

theorem replaceThree_at {S : ℕ} (ports : Fin 3 ↪ Fin S) (a b c : List Bool)
    (stk : Fin S → List Bool) (i : Fin 3) :
    replaceThree ports a b c stk (ports i) = ![a, b, c] i := by
  fin_cases i <;> simp [replaceThree, ports.injective.eq_iff]

theorem replaceThree_frame {S : ℕ} (ports : Fin 3 ↪ Fin S) (a b c : List Bool)
    (stk : Fin S → List Bool) (i : Fin S) (hi : ¬∃ j, ports j = i) :
    replaceThree ports a b c stk i = stk i := by
  have h0 : i ≠ ports 0 := fun h => hi ⟨0, h.symm⟩
  have h1 : i ≠ ports 1 := fun h => hi ⟨1, h.symm⟩
  have h2 : i ≠ ports 2 := fun h => hi ⟨2, h.symm⟩
  simp [replaceThree, h0, h1, h2]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical split of a concatenated pair of coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

open IrreducibleSearchProgram

def registers : Fin 6 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩,
    by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
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
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

def replaceTwo {S : ℕ} (ports : Fin 2 ↪ Fin S) (a b : List Bool)
    (stk : Fin S → List Bool) : Fin S → List Bool :=
  Function.update (Function.update stk (ports 0) a) (ports 1) b

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! PairProduct -/


/-! Candidate -/


/-! ProductCheck -/


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Pascal's recurrence on actual little-endian words. The old row, rather
than the growing new row, supplies the carry at each position. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

def initial (R : ℕ) : List (List Bool) :=
  List.ofFn fun i : Fin R => if i.val = 0 then [true] else []

@[simp] theorem initial_length (R : ℕ) : (initial R).length = R := by simp [initial]

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical Pascal scan computes the exact binomial row, in increasing
column order, including columns above the row index. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

def natScan (prior : ℕ) : List ℕ → List ℕ
  | [] => []
  | old :: rest => (prior + old) :: natScan old rest

def scanPrior (h : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => h.choose k

@[simp] theorem initial_zero : initial 0 = [] := by simp [initial]

@[simp] theorem initial_succ (R : ℕ) :
    initial (R+1) = [true] :: List.replicate R [] := by
  simp [initial,List.ofFn_succ]

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive Pascal-prefix cache for the original parity coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

open scoped BigOperators
open Matrix

/-- Unsigned coefficients, indexed by translation and distance from the top. -/
def H : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | A + 1, m + 1 => H A (m + 1) + 2 * H (A + 1) m
termination_by A m => (A, m)

@[simp] theorem H_zero (m : ℕ) : H 0 m = 1 := by rw [H]
@[simp] theorem H_zero_right (A : ℕ) : H A 0 = 1 := by cases A <;> rw [H]

def shift (R : ℕ) : Matrix (Fin R) (Fin R) ℤ :=
  fun j k => if j.val + 1 = k.val then 1 else 0

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientRecurrenceScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A left-to-right add/shift scan constructs each unsigned cache row. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

def scanDouble (prior : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let y := 2 * prior + x
    y :: scanDouble y xs

@[simp] theorem scanDouble_length (prior : ℕ) (xs : List ℕ) :
    (scanDouble prior xs).length = xs.length := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp only [scanDouble, List.length_cons, ih]

def scanPrior (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => H (A + 1) n

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed binary machine combines the two collision counts. Its instruction
count and every output length are charged in terms of actual input bit lengths. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram

def arithmeticWork : Fin 5 ↪ Fin 12 where
  toFun i := ⟨i.val + 7, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact signed arithmetic for minor enumeration. Integers are represented as
pairs of natural binary words. No modular arithmetic, integer oracle, or
parameter-dependent instruction table is used. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

def positivePorts : Fin 12 → Fin 15 := ![0, 2, 1, 3, 4, 5, 6, 10, 11, 12, 13, 14]
def negativePorts : Fin 12 → Fin 15 := ![0, 3, 1, 2, 7, 8, 9, 10, 11, 12, 13, 14]

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control addition for integer difference-pair words. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

def addWork : Fin 5 ↪ Fin 15 where
  toFun i := ⟨i.val+10, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic callbacks on a fixed stream ABI. The remaining record stream is
preserved byte-for-byte across each real signed-arithmetic call. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

def streamPorts : Fin 15 → Fin 16 := Fin.castAdd 1

end SubexponentialSAT.SqrtLog.RowSelectionProgram

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

open SubexponentialSAT.SqrtLog.RowSelectionProgram

def workPorts : Fin 16 → Fin 18 := Fin.castAdd 2

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramEntriesEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual signed-pair framing, with every unrelated stack preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries

def emitPorts (negative : Bool) : Fin 4 → Fin 6 :=
  if negative then ![3,4,2,1] else ![3,4,2,0]

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScalarEmitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving signed-pair emission into a reverse buffer. The existing exact
pair serializer is called on paid copies, and its output is transferred once.
All source words survive; the four work stacks are restored to empty. -/
namespace SubexponentialSAT.SqrtLog.LayoutScalarEmitter

def pairRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def pairPorts : Fin 6 → Fin 7 := ![3,4,6,0,1,2]

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

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

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheEmitPorts : Fin 7 → Fin 18 := ![0,1,16,5,6,7,8]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheFinishPorts : Fin 7 → Fin 18 := ![0,1,16,5,6,7,15]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

def addPorts : Fin 3 → Fin 18 := ![0,2,4]

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

def zeroRecord : List Bool := [true,false,false]

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

def initialBuildPorts (j : Fin 18) : Fin 19 := if j = 17 then 18 else Fin.castAdd 1 j

def cacheBuildPorts : Fin 18 → Fin 19 := Fin.castAdd 1

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def normalizePorts : Fin 8 ↪ Fin 9 :=
  ⟨![0,4,5,6,7,2,8,3],by decide⟩

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def basePorts : Fin 18 → Fin 19 := Fin.castAdd 1

def positivePorts : Fin 9 → Fin 19 := ![2,18,16,4,5,6,7,8,9]
def negativePorts : Fin 9 → Fin 19 := ![3,18,17,4,5,6,7,8,9]

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.SqrtLog.RowSelectionProgram

def buildFinalPorts : Fin 19 → Fin 20 := Fin.castAdd 1

def flatFinalPorts (j : Fin 19) : Fin 20 :=
  if j=18 then 19 else Fin.castAdd 1 j

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native exponentiation for the common layout denominator. The unary
row parameter is retained at239; the represented half starts at255 and one at250.
The output252 is computed by exactly `R-1` native multiplications. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

open SubexponentialSAT

def powerValue {C : Type*} (mul : C → C → C) (half one : C) (R : ℕ) : C :=
  (fun x => mul x half)^[R-1] one

def powerBudget (R K W : ℕ) : ℕ :=
  (R-1)*(K+8*W+11)+7*R+27*W+32

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extension-ring denominator program. It first lifts the actual
scalar-half word, then runs the paid native multiplication loop. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram
open SubexponentialSAT

def polynomialBudget (R B d : ℕ) : ℕ :=
  B*(100000*(d+1)^3*(B+1)^2+80*d*B+110) +
    200000*(d+1)^3*(B+1)^2+203*d*B+251 +
    R*(50000*(d+1)^3*(B+1)^2+8*d*B+11)+7*R+27*d*B+32

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The per-query denominator is computed in a disjoint 256-stack bank. The
only persistent output is stack 728; the runtime exponent is read from 740. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT

def port (i : Fin 256) : Fin 768 := ⟨340+i.val, by omega⟩
theorem port_injective : Function.Injective port := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [port] using this

def bank : List (Fin 768) := (List.finRange 256).map port

theorem mem_bank (i : Fin 768) : i∈bank ↔ 340 ≤ i.val ∧ i.val < 596 := by
  simp only [bank,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,rfl⟩; simp only [port]; omega
  · intro h
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

def pairs : List (Fin 768 × Fin 768) :=
  [(194,534),(201,541),(202,542),(203,543),(204,544),
   (280,589),(207,590),(211,591),(740,579),(253,593)]

theorem pairs_valid : ∀p∈pairs,p.1≠p.2 ∧ p.1≠460 ∧ (460:Fin 768)≠p.2 := by simp [pairs]
theorem pairs_separated : ∀p∈pairs,∀q∈pairs,p.1≠q.2 := by simp [pairs]
theorem pairs_distinct : (pairs.map Prod.snd).Nodup := by decide
theorem pairs_destination : ∀p∈pairs,p.2∈bank := by
  intro p hp
  rw [mem_bank]
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def registers (i : Fin 16) : Fin 40 := ⟨i.val,by omega⟩
theorem registers_injective : Function.Injective registers := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 40 => k.val) h

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramOuterCarried
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried

/-- Outer marked-branch and residual accumulators are not node-worker inputs. -/
def hidden (i : Fin 768) : Prop := i ∈ ([320, 322, 332] : List (Fin 768))

instance instDecidablePredFinOfNatNatHidden : DecidablePred hidden := fun i => inferInstanceAs (Decidable (i ∈ ([320, 322, 332] : List (Fin 768))))

end SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay of the complete denominator call. The three opaque
outer accumulators are never inspected, including by storage subroutines. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT

theorem not_hidden_of_high (i : Fin 768) (hi : 340 ≤ i.val) : ¬ LeafProgram.OuterCarried.hidden i := by
  simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.mem_nil_iff,or_false]
  intro h
  rcases h with rfl|rfl|rfl <;> norm_num [Fin.coe_ofNat_eq_mod] at hi

theorem port_not_hidden (i : Fin 256) : ¬ LeafProgram.OuterCarried.hidden (port i) :=
  not_hidden_of_high _ (by dsimp [port]; omega)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal incidence pullback

An incidence is sent to its original variable by `owner`. The pullback
duplicates a variable value; the dual operation adds row coefficients on
each fiber. No inverse matrix or new basis is used in these definitions.
-/

namespace SubexponentialSAT.SqrtLog.LayoutPullback

open scoped BigOperators

variable {I V R : Type*} [Fintype I] [Fintype V] [DecidableEq V]

def duplicate (owner : I → V) (x : V → R) : I → R := x ∘ owner

end SubexponentialSAT.SqrtLog.LayoutPullback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutExactBuckets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact integer signatures survive every coefficient-ring reduction

The assignments in this module are integer vectors. In the counting
application they are Boolean vectors or differences of Boolean vectors.
Equality of signatures is an equality in `ℤ`, before any reduction.
No claim about the kernel of a matrix reduced modulo a prime is used.
-/

namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators
open LayoutPullback

variable {V J R : Type*} [Fintype V] [CommRing R]

def signature (A : J → V → ℤ) (x : V → ℤ) (j : J) : ℤ :=
  ∑ v, A j v * x v

def value (a : V → R) (x : V → ℤ) : R :=
  ∑ v, a v * (x v : R)

def KillsIntegerKernel (a : V → R) (A : J → V → ℤ) : Prop :=
  ∀ z : V → ℤ, (∀ j, signature A z j = 0) → value a z = 0

section RationalRowReduction

variable {J' : Type*} [Fintype J']

/-- The selected rows rationally span every original integer row. This
condition can be verified over `ℚ`; it is never asserted after reduction. -/
def RationalRowSpan (C : J → V → ℤ) (A : J' → V → ℤ) : Prop :=
  ∀ j, ∃ c : J' → ℚ, ∀ v, (C j v : ℚ) = ∑ k, c k * (A k v : ℚ)

end RationalRowReduction

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber summation helpers. The remaining fiber is a stream of
actual unary index fields, never an array of precomputed matrix entries. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open RowSelectionProgram

def unary (i : ℕ) : List Bool := List.replicate i true

def addRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def addStacks : Fin 16 → Fin 256 := ![212,213,254,255,0,1,2,3,4,5,6,7,8,9,10,214]

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open RowSelectionProgram

def bodyBudget (T B i L : ℕ) : ℕ := T+5*i+8+25000*(L+B+3)^2

def cost (T B : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 3
  | i::is, L => bodyBudget T B i L+cost T B is (L+B+2)+4

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeIndexProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical lookup of the current field node

The fixed program copies the framed node table, parses its records in order,
compares their actual bits with the current node, and counts rejected records.
Its only visible stack change is the unary first matching index at port 116.
The source table at 125 and query at 78 are preserved.
-/

namespace SubexponentialSAT.SubexpNodeIndexProgram

namespace Internal

def comparePorts : Fin 2 → Fin 7 := ![3,4]

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

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

abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT

def compareSlots : Fin 7 → Fin 11 := ![0,1,2,3,5,6,7]

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramVisit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT

def callbackCost (query index : ℕ) (p : ℕ × ℕ) : ℕ :=
  47*p.1+34*p.2+9*query+7*index+138

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

def ownerRegisters : Fin 5 → Fin 16 := Fin.castAdd 11
def ownerStacks : Fin 11 → Fin 256 := ![216,201,217,218,219,220,221,222,223,215,214]

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

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

/-- Actual invertible elements for every denominator used in interpolation. -/
structure NodeUnits (node : I → E) where
  nodeUnit : I → Eˣ
  nodeUnit_val : ∀ i, (nodeUnit i : E) = node i
  differenceUnit : (i j : I) → i ≠ j → Eˣ
  differenceUnit_val : ∀ i j hij, (differenceUnit i j hij : E) = node i - node j

namespace NodeUnits

variable {node : I → E}

/-- The supplied inverse of a nonzero interpolation node. -/
def nodeInverse (u : NodeUnits node) (i : I) : E := ↑((u.nodeUnit i)⁻¹)

/-- The diagonal branch is unused by products over `erase i`. -/
def differenceInverse (u : NodeUnits node) (i j : I) : E :=
  if hij : i ≠ j then ↑((u.differenceUnit i j hij)⁻¹) else 0

omit [DecidableEq I] in
theorem nodeInverse_mul (u : NodeUnits node) (i : I) :
    u.nodeInverse i * node i = 1 := by
  rw [nodeInverse, ← u.nodeUnit_val i]
  exact Units.inv_mul (u.nodeUnit i)

end NodeUnits

variable {node : I → E}

/-- A normalized linear factor vanishing at node `j` and equal to one at `i`. -/
noncomputable def basisDivisor (u : NodeUnits node) (i j : I) : Polynomial E :=
  Polynomial.C (u.differenceInverse i j) * (Polynomial.X - Polynomial.C (node j))

@[simp] theorem basisDivisor_eval_right (u : NodeUnits node) (i j : I) :
    (basisDivisor u i j).eval (node j) = 0 := by
  simp [basisDivisor]

/-- The source's `T / λ_i` times the Lagrange product. -/
noncomputable def basis (u : NodeUnits node) (s : Finset I) (i : I) : Polynomial E :=
  (Polynomial.C (u.nodeInverse i) * Polynomial.X) *
    ∏ j ∈ s.erase i, basisDivisor u i j

@[simp] theorem basis_eval_zero (u : NodeUnits node) (s : Finset I) (i : I) :
    (basis u s i).eval 0 = 0 := by
  simp [basis]

variable [DecidableEq V]

section Mismatches

variable [Fintype I] [Fintype V] [DecidableEq C]

/-- A column needs a prescribed value exactly when its head differs from the factor color. -/
def mismatchPositions (head : V → I → C) (σ : I → C) (y : V) : Finset I :=
  Finset.univ.filter (fun t => head y t ≠ σ t)

omit [DecidableEq I] [DecidableEq V] [Fintype V] in
@[simp] theorem mem_mismatchPositions (head : V → I → C) (σ : I → C) (y : V) (t : I) :
    t ∈ mismatchPositions head σ y ↔ head y t ≠ σ t := by
  simp [mismatchPositions]

/-- The actual `Y` in Section 3.3, defined by a mismatch-count bound. -/
def correctionColumns (head : V → I → C) (σ : I → C) (R : ℕ) : Finset V :=
  Finset.univ.filter (fun y => (mismatchPositions head σ y).card ≤ R)

omit [DecidableEq I] [DecidableEq V] in
@[simp] theorem mem_correctionColumns (head : V → I → C) (σ : I → C) (R : ℕ) (y : V) :
    y ∈ correctionColumns head σ R ↔ (mismatchPositions head σ y).card ≤ R := by
  simp [correctionColumns]

end Mismatches

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutHeadPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Pullback of a head-coherent incidence layout to the original variables. -/

namespace SubexponentialSAT.SqrtLog.LayoutHeadPullback

open scoped BigOperators
open LayoutPullback LayoutExactBuckets

variable {I V F G O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable [Fintype G] [DecidableEq G] [CommRing O]

/-- The owner map restricted to one original-variable head. -/
def headOwner (owner : I → V) (copyHead : I → G) (head : V → G)
    (hhead : ∀ i, copyHead i = head (owner i)) (g : G) :
    {i : I // copyHead i = g} → {v : V // head v = g} :=
  fun i => ⟨owner i.val, (hhead i.val).symm.trans i.property⟩

theorem sum_subtype_ite {A M : Type*} [Fintype A] [AddCommMonoid M]
    (p : A → Prop) [DecidablePred p] (f : A → M) :
    (∑ a : {a // p a}, f a.val) = ∑ a, if p a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)]
  exact Finset.sum_filter _ _

end SubexponentialSAT.SqrtLog.LayoutHeadPullback

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

def bankPort (i : Fin 256) : Fin 288 := ⟨i.val+25,by omega⟩

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single cached scalar term: three parsed operands, three real signed
multiplications, and one real signed addition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.SqrtLog.RowSelectionProgram

def termGrowth (B : ℕ) : ℕ := 14*B+52

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/

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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

def registers : Fin 8 → Fin 9 := Fin.castAdd 1

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitBudget -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts
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

def wideStacks (i : Fin 640) : Fin 768 := i.castLE (by decide)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockSearchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed control for the universal-block finite search

The commands in this file scan runtime framed lists. Their finite control
depends on the supplied finite predicate program and fixed ports, never on
the block dimension, field size, or list lengths. Predicate specifications
are measured `StructuredCalls.Eval` contracts for actual finite code.
-/

namespace SubexponentialSAT.Subexp.BlockSearchProgram

theorem not_any_not (records : List (List Bool)) (test : List Bool → Bool) :
    (!(records.any (fun bits => !(test bits)))) = records.all test := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
      cases ht : test bits <;> simp [ht, ih]

/-! A full-dimensional candidate needs only universal scalar tests. -/

open scoped BigOperators

end SubexponentialSAT.Subexp.BlockSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite loop that scans the four color streams. Its loop count and
color width are runtime stacks. The result is specified by a finite fold of
the already proved physical scan step. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

abbrev ColorRow := Fin 4 → List Bool

def streams (rows : List ColorRow) (i : Fin 4) : List Bool :=
  (rows.map (fun w => w i)).flatten

@[simp] theorem streams_nil (i : Fin 4) : streams [] i = [] := rfl
@[simp] theorem streams_cons (w : ColorRow) (ws : List ColorRow) (i : Fin 4) :
    streams (w :: ws) i = w i ++ streams ws i := rfl

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

def encodeColor {r : ℕ} (c : Fin r) : List Bool :=
  List.ofFn fun d : Fin r => decide (c = d)

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrontendData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime input data and explicit budgets for the physical packing frontend. -/
namespace SubexponentialSAT.Subexp.PackingFrontend

structure Params where
  D : ℕ
  Δ : ℕ
  scopes : List (List ℕ)
  rows : List (List Bool)
  width : List Bool
  alphabet : List (List Bool)

end SubexponentialSAT.Subexp.PackingFrontend

end OAI.Algorithms
end


