-- Prove2me | Definitions.Def_OAIQ081S010
-- name    : OAIQ081S010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:23:27.862327+00:00
-- url     : https://prove2.me/theorems/b7ec66dc-6141-40fa-afb4-57157c8a42e2
-- title:
--   Definitions bundle OAIQ081S010 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 121 declarations of OpenAI's Lean: 76 definitions, 1 inductive type or structure and 44 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.low`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.smallInteger`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.cells`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.tableCells`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.bootStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.cachedEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.entrySource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.logPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.preparationDiscard`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.selectorPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.unaryPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.ArithmeticInstruction`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.halfValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.liftCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.newtonCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.servicePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.afterI`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.afterJ`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.afterSub`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.codeBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.codeValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.coefficientsAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.entryCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.outputPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.remainderRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.scanIPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.scanIRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.scanJPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.scanJRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.setOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.subPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.subRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.naturalBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.naturalValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.scaledBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.scaledValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.signedBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.signedValue` and 37 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramBoot`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramCleanup`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoded`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntry`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramInput`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarBase`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTableRun`, `SubexponentialSAT_SqrtLog_IdempotentProgramFinal`, `SubexponentialSAT_SqrtLog_IdempotentProgramHalf`, `SubexponentialSAT_SqrtLog_IdempotentProgramService`, `SubexponentialSAT_SqrtLog_IdempotentProgramTrace`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramFrame`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramValue`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgram`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramNatural`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramScale`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramSigned`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgram`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramCounts`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramFrame`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramPass`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramRows`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation`, `SubexponentialSAT_SqrtLog_IrreducibleSearchCompanionList`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpOrderedTupleStep`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpTupleRefinement`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S033`, `OAIQ081S035` and `OAIQ081S040`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

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

namespace Mask

def regPort : Fin 4 → Fin 8 := Fin.castAdd 4

end Mask

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unary iteration budget is derived from the runtime binary t word.
This module includes its native conversion trace and preserves the original
word for modulus construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

def unaryPorts : Fin 3 → Fin 41 := ![28,29,30]

theorem unaryPorts_injective : Function.Injective unaryPorts := by decide

def logPorts : Fin 3 → Fin 41 := ![39,40,0]

theorem logPorts_injective : Function.Injective logPorts := by decide

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramBoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

def bootStacks (t : ℕ) (bits modulus logword : List Bool) : Fin 41 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => []) 31 bits) 29 (List.replicate t true))
    12 (List.replicate (2*t) true)) 37 (List.replicate (3*t) true)) 39 logword) 5 modulus

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

/-- Private preparation ports are discarded before entering the Newton ABI.
The modulus, width, scalar zero, table, five arrays and two counters survive. -/
def preparationDiscard : List (Fin 41) :=
  [0,1,2,3,4,6,7,8,9,10,11,13,14,15,16,18,19,20,21,23,24,25,26,27,28,29,30,31,38,40]

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

inductive ArithmeticInstruction where
  | add (dst left right : Fin 4)
  | mul (dst left right : Fin 4)
  | neg (dst src : Fin 4)
  deriving DecidableEq, Repr

variable {C R : Type*} [CommRing R]

def newtonCode : List ArithmeticInstruction :=
  [.mul 1 0 0, .mul 2 1 0, .add 3 1 1, .add 3 3 1,
   .add 2 2 2, .neg 2 2, .add 0 3 2]

@[simp] theorem newtonCode_length : newtonCode.length = 7 := rfl

/-- Only the constant seven-instruction block is copied; expressions do not
expand recursively with the Newton iteration count. -/
def liftCode : ℕ → List ArithmeticInstruction
  | 0 => []
  | n+1 => liftCode n ++ newtonCode

@[simp] theorem liftCode_length (n : ℕ) : (liftCode n).length = 7*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [liftCode, ih]; omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native, source-preserving scalar operations on the preparation ABI.
Only the selected output changes; all low arithmetic scratch is restored. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

def low : Fin 8 → Fin 41 := Fin.castAdd 33

theorem low_injective : Function.Injective low := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 41 => x.val) h)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
local instance instFactPrimeOfNatNat_solutions : Fact (Nat.Prime 3) := ⟨by decide⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
local instance instFactPrimeOfNatNat_solutions_1 : Fact (Nat.Prime 3) := ⟨by decide⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramHalf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

variable {C A : Type*} [CommRing A]

/-- Integral half recurrence: h_0=1, h_(s+1)=3h_s-1. Thus 2h_s=3^s+1. -/
def halfValue : ℕ → A
  | 0 => 1
  | n+1 => 3*halfValue n-1

theorem twice_halfValue (n : ℕ) : (2 : A)*halfValue n = 3^n+1 := by
  induction n with
  | zero => simp [halfValue]; ring
  | succ n ih =>
      rw [halfValue, pow_succ]
      linear_combination 3*ih

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary scanner. Each complete triple contributes three tokens
to the accumulator; the two output flags encode the remainder modulo three.
No runtime integer arithmetic is an instruction of this machine. -/
namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

def remainderRegs (n : ℕ) : Fin 4 → Bool :=
  ![false, false, decide (n = 1), decide (n = 2)]

theorem scan_cost (n : ℕ) : 10*(n/3)+2*(n%3)+5 ≤ 4*n+5 := by omega

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

/-- The code alphabet is 0,1,3,-2,-6,7 in that order. -/
def codeValue (c : Fin 6) : ℤ := ![0,1,3,-2,-6,7] c
def codeBits (c : Fin 6) : Fin 3 → Bool :=
  ![decide (c.val % 2 = 1), decide (c.val / 2 % 2 = 1), decide (c.val / 4 = 1)]

def outputPort (b : Fin 3) : Fin 8 := ⟨5+b.val,by omega⟩

def setOutput (r : Fin 8 → Bool) (c : Fin 6) : Fin 8 → Bool :=
  ![r 0,r 1,r 2,r 3,r 4,codeBits c 0,codeBits c 1,codeBits c 2]

def coefficientsAt : ℕ → List (Fin 6)
  | 0 => [1,0,0,0,0]
  | 1 => [0,1,0,0,0]
  | 2 => [0,0,1,0,0]
  | 3 => [0,3,2,1,0]
  | _ => [0,4,5,2,1]

theorem coefficientsAt_length (a : ℕ) : (coefficientsAt a).length = 5 := by
  rcases a with _ | _ | _ | _ | a <;> rfl

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
local instance instFactPrimeOfNatNat_solutions_2 : Fact (Nat.Prime 3) := ⟨by decide⟩

variable (p t : ℕ) [Fact p.Prime]

def smallInteger : Fin 6→ℤ := ![0,1,-2,3,-6,7]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

def scanIRegs : Fin 4 → Fin 8 := ![0,1,3,4]
def scanJRegs : Fin 4 → Fin 8 := ![0,1,5,6]
def scanIPorts : Fin 2 → Fin 4 := ![0,3]
def scanJPorts : Fin 2 → Fin 4 := ![1,3]
def subRegs : Fin 4 → Fin 8 := ![0,1,2,7]
def subPorts : Fin 2 → Fin 4 := ![3,2]

def afterI (r : Fin 8 → Bool) (i : ℕ) : Fin 8 → Bool :=
  ![false,false,r 2,decide (i%3=1),decide (i%3=2),r 5,r 6,r 7]
def afterJ (r : Fin 8 → Bool) (j : ℕ) : Fin 8 → Bool :=
  ![false,false,r 2,r 3,r 4,decide (j%3=1),decide (j%3=2),r 7]
def afterSub (r : Fin 8 → Bool) (rf : Fin 4 → Bool) : Fin 8 → Bool :=
  ![rf 0,rf 1,rf 2,r 3,r 4,r 5,r 6,rf 3]

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open IdempotentProgram

def entryCode (i j k : ℕ) : Fin 6 :=
  if k < 3*(i/3+j/3) then 0
  else ((coefficientsAt (i%3+j%3))[k-3*(i/3+j/3)]?).getD 0

theorem coefficientsAt_value (a : ℕ) (ha : a ≤ 4) (n : ℕ) :
    codeValue (((coefficientsAt a)[n]?).getD 0) =
      if a < 3 then (if n = a then 1 else 0)
      else if a = 3 then
        (if n = 3 then 1 else 0) + (if n = 1 then -2 else 0) +
          (if n = 2 then 3 else 0)
      else
        (if n = 3 then 3 else 0) + (if n = 4 then 1 else 0) +
          (if n = 1 then -6 else 0) + (if n = 2 then 7 else 0) := by
  by_cases hn : n < 5
  · interval_cases a <;> interval_cases n <;> norm_num [coefficientsAt,codeValue] <;> first | rfl | decide | simp
  · have hnone : (coefficientsAt a)[n]? = none :=
      List.getElem?_eq_none (by rw [coefficientsAt_length]; omega)
    rw [hnone]
    interval_cases a <;> simp [codeValue,show n ≠ 0 by omega,
      show n ≠ 1 by omega,show n ≠ 2 by omega,show n ≠ 3 by omega,
      show n ≠ 4 by omega]

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A table entry is selected by a fixed unary bit program and copied from
one of six scalar cache words. The table itself is constructed at runtime. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open IdempotentTableEntryProgram (codeBits outputPort entryCode)

def entrySource (c : Fin 6) : Fin 41 := ![17,18,20,19,21,23] c

def selectorPorts : Fin 4 → Fin 41 := Fin.castAdd 37

theorem selectorPorts_injective : Function.Injective selectorPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 41 => x.val) h)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native descending-index traversal. The remaining unary counter is the
runtime index passed to the callback. Prefixing each generated word therefore
materializes the final array in increasing index order, without a precomputed
array or a value-dependent control table. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

abbrev Store := Fin 41 → List Bool

abbrev cells (f : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => cells f n ++ f n

def tableCells (f : ℕ → ℕ → ℕ → List Bool) (n : ℕ) : List Bool :=
  cells (fun k => cells (fun i => cells (fun j => f i j k) n) n) n

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTableRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open IdempotentTableEntryProgram (entryCode)

def cachedEntry (base : Fin 41 → List Bool) (i j k : ℕ) : List Bool :=
  base (entrySource (entryCode i j k))

namespace Scan

theorem cells_eq_ofFn (f : ℕ → List Bool) (n : ℕ) :
    cells f n = (List.ofFn (fun i : Fin n => f i.val)).flatten := by
  induction n with
  | zero => simp [cells]
  | succ n ih =>
      rw [cells,List.ofFn_succ']
      simp only [List.concat_eq_append,List.flatten_append,List.flatten_cons,
        List.flatten_nil,List.append_nil,Fin.val_castSucc,Fin.val_last]
      rw [ih]

end Scan

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramService
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the common 32-stack arithmetic ABI into the Newton machine and prove
that the source-preserving register wrapper has the exact specified effect. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

/-- The nine added stacks hold four arrays, negative one, degree, copy scratch,
and the binary loop counter plus its scratch. -/
def servicePorts : Fin 32 → Fin 41 := Fin.castAdd 9

theorem servicePorts_injective : Function.Injective servicePorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 41 => x.val) h)

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

local instance instFactPrimeOfNatNat_solutions_2 : Fact (Nat.Prime 3) := ⟨by decide⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete native Newton lift and the exact degree-three coefficient output.
The input-state contract includes prepared scalar constants and the cached
H-adic table; native preparation is a separate remaining construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators

local instance ternaryPrimeFinal : Fact (Nat.Prime 3) := ⟨by decide⟩

end SubexponentialSAT.SqrtLog.IdempotentProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed little-endian binary-to-ring scanner.  No natural-number value is
used by the program: each input bit conditionally adds the current place and
then doubles that place.  Arithmetic is supplied by finite native commands;
the concrete RingModel instantiation is in IntegerRingLiftProgramModel. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

open SubexponentialSAT

def scan {C : Type*} (add : C → C → C) : List Bool → C → C → C × C
  | [], a, p => (a, p)
  | b :: bs, a, p => scan add bs (if b then add a p else a) (add p p)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramNatural
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT

def naturalValue {C : Type*} (add : C → C → C) (zero one : C) (bits : List Bool) : C :=
  (scan add bits zero one).1

def naturalBudget (bits K W : ℕ) : ℕ :=
  bits * (2 * (K + 40 * W + 50) + 3) + 16 * W + 15

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramSigned
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT

def signedValue {C : Type*} (mul add : C → C → C) (zero one minusOne : C)
    (positive negative : List Bool) : C :=
  add (naturalValue add zero one positive) (mul (naturalValue add zero one negative) minusOne)

def signedBudget (bits Km Ka W : ℕ) : ℕ :=
  bits * (2 * (Ka + 40 * W + 50) + 10) + Km + Ka + 123 * W + 151

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT

def scaledValue {C : Type*} (mul add : C → C → C) (zero one minusOne invDenom : C)
    (positive negative : List Bool) : C :=
  mul (mul (signedValue mul add zero one minusOne positive negative) invDenom) minusOne

def scaledBudget (bits Km Ka W : ℕ) : ℕ := signedBudget bits Km Ka W + 2*(Km+40*W+50)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed local cache-producer instructions and framed native service calls.
The lower256 ports are the existing arithmetic ABI; controller streams and
copy scratch occupy disjoint higher ports. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT

abbrev Store := Fin 320 → List Bool

def low (i : Fin 256) : Fin 320 := i.castAdd 64

theorem low_injective : Function.Injective low := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid materialization of canonical unary word and table lengths. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

def countRegisters (i : Fin 3) : Fin 16 := i.castAdd 13

def countPorts (src dst : Fin 320) : Fin 2 → Fin 320 := ![src,dst]

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The controller's changing ports and the preserved arithmetic context. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

def controllerPorts : List (Fin 320) := [208,213,218,257,258,259,260,261,262,263]

def Frame (base s : Store) : Prop := ∀i,i∉controllerPorts → s i=base i

theorem Frame.refl (s : Store) : Frame s s := fun _ _ => rfl

theorem Frame.update {base s : Store} (h : Frame base s) (i : Fin 320) (v : List Bool)
    (hi : i∈controllerPorts) : Frame base (Function.update s i v) := by
  intro j hj
  rw [Function.update_of_ne (by intro he; subst j; exact hj hi)]
  exact h j hj

theorem controllerPorts_lower {i : Fin 320} (hi : i∈controllerPorts) : 208 ≤ i.val := by
  simp only [controllerPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def scratchPorts : List (Fin 320) := [205,219,220,222,240,241,244,245,246,270,271]

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed-width physical map scan. The service is an ordinary finite
subprogram, and its output is transferred into the actual packed table. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

def MapPorts (src dst arg : Fin 320) : Prop :=
  Function.Injective (![104,270,271,src,dst,arg,208] : Fin 7 → Fin 320)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramPass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packed scans starting from a preserved node master. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

theorem flatMap_length {C : Type*} (encode : C → List Bool) (W : ℕ)
    (hwidth : ∀x,(encode x).length=W) (xs : List C) :
    (xs.flatMap encode).length=xs.length*W := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,hwidth,Nat.add_mul,Nat.add_comm]

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scans for inverse nodes, negative nodes, and a complete row of
pairwise difference inverses. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

def nodeScanBudget (K W Q : ℕ) := Q*(K+26*W+19)+7

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single fixed native interpolation-cache producer. The only data
inputs are the actual node stream and already prepared ring constants.
No inverse, negative, or pairwise table is supplied to this program. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

def inputEmpty : List (Fin 320) := [208,213,218,257,258,259,260,261,262,263,272]

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

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

def tuplePayload {n : ℕ} (v : Fin n → List Bool) : List Bool :=
  (List.ofFn v).flatten

@[simp] theorem tuplePayload_zero (v : Fin 0 → List Bool) : tuplePayload v = [] := rfl

@[simp] theorem tuplePayload_cons {n : ℕ} (a : List Bool) (v : Fin n → List Bool) :
    tuplePayload (Fin.cons a v) = a ++ tuplePayload v := by
  simp [tuplePayload, List.ofFn_succ]

end SubexponentialSAT.SubexpTupleRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
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

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

/-- Escaped data without the final false delimiter. -/
def escapeBits : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: escapeBits bs

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

def emitIfSelectedSteps (selected : Bool) (bits : List Bool) : ℕ :=
  if selected then 5 * bits.length + 11 else 2 * bits.length + 7

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpOrderedTupleStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # A fixed Cartesian expansion in exact enumeration order -/

namespace SubexponentialSAT.SubexpOrderedTupleStep

def reverseRegisters : Fin 3 → Fin 10 := ![0,1,2]
def reverseStacks : Fin 4 → Fin 9 := ![5,1,0,2]

theorem reverseRegisters_injective : Function.Injective reverseRegisters := by decide
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

end SubexponentialSAT.SubexpOrderedTupleStep

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed framed call generates an ordered table from a runtime unary depth.
Only its output and depth ports change; the generator's sentinel is paid for
and cleared before returning. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open SubexpTupleRefinement

def generatorOut (candidate : Bool) : Fin 28 := if candidate then 24 else 20

def generatorRegs (i : Fin 10) : Fin 22 := Fin.castAdd 12 i

theorem generatorRegs_injective : Function.Injective generatorRegs :=
  Fin.castAdd_injective _ _

def generatorMap (candidate : Bool) : Fin 9 → Fin 28 :=
  ![generatorOut candidate, 10, 0, 1, 2, 3, 4, 5, 6]

theorem generatorMap_injective (candidate : Bool) :
    Function.Injective (generatorMap candidate) := by
  cases candidate <;> decide

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


/-! Paid construction of both search tables from a single unary depth word. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


def layout (depth count candidates factors alphabet fuel : List Bool) : Fin 28 → List Bool :=
  fun i => if i = 14 then depth else if i = 22 then count else if i = 24 then candidates
    else if i = 20 then factors else if i = 10 then alphabet else if i = 6 then fuel else []

@[simp] theorem layout14 (d c a b w f : List Bool) : layout d c a b w f 14 = d := rfl
@[simp] theorem layout22 (d c a b w f : List Bool) : layout d c a b w f 22 = c := rfl
@[simp] theorem layout24 (d c a b w f : List Bool) : layout d c a b w f 24 = a := rfl
@[simp] theorem layout20 (d c a b w f : List Bool) : layout d c a b w f 20 = b := rfl
@[simp] theorem layout10 (d c a b w f : List Bool) : layout d c a b w f 10 = w := rfl
@[simp] theorem layout6 (d c a b w f : List Bool) : layout d c a b w f 6 = f := rfl
@[simp] theorem layout7 (d c a b w f : List Bool) : layout d c a b w f 7 = [] := rfl

@[simp] theorem layout_update22 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 22 x = layout d x a b w f := by
  funext i; fin_cases i <;> simp [layout]

@[simp] theorem layout_update24 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 24 x = layout d c x b w f := by
  funext i; fin_cases i <;> simp [layout]

@[simp] theorem layout_update20 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 20 x = layout d c a x w f := by
  funext i; fin_cases i <;> simp [layout]

@[simp] theorem layout_update10 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 10 x = layout d c a b x f := by
  funext i; fin_cases i <;> simp [layout]

@[simp] theorem layout_update6 (d c a b w f x : List Bool) :
    Function.update (layout d c a b w f) 6 x = layout d c a b w x := by
  funext i; fin_cases i <;> simp [layout]

theorem layout_low (d c a b w f : List Bool) (i : Fin 28) (hi : i.val < 6) :
    layout d c a b w f i = [] := by
  fin_cases i <;> simp_all [layout]

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchCompanionList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A sequential list implementation of one companion-matrix step. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

variable {R : Type*} [Ring R]

def companionScan (tail previous : R) : List (R × R) → List R
  | [] => []
  | (c, a) :: xs => (previous - tail * c) :: companionScan tail a xs

theorem companionScan_ofFn {d : ℕ} (tail previous : R) (c a : Fin d → R) :
    companionScan tail previous (List.ofFn (fun i => (c i, a i))) =
      List.ofFn (fun i => (if _h : i.val = 0 then previous
        else a ⟨i.val - 1, by omega⟩) - tail * c i) := by
  induction d generalizing previous with
  | zero => simp [companionScan]
  | succ d ih =>
      rw [List.ofFn_succ, companionScan, List.ofFn_succ]
      congr 1
      rw [ih]
      apply congrArg List.ofFn
      funext i
      simp only [Fin.val_succ, Nat.add_sub_cancel, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, dite_false]
      split_ifs with hi
      · congr 1
        congr 1
        apply Fin.ext
        simp [hi]
      · congr 1
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega

end SubexponentialSAT.SqrtLog.IrreducibleSearch

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

def firstPorts : Fin 3 ↪ Fin 6 := ⟨![0, 2, 3], by decide⟩
def secondPorts : Fin 3 ↪ Fin 6 := ⟨![3, 2, 4], by decide⟩

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
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

def sixRegisters : Fin 6 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h⟩
def eightRegisters : Fin 8 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h⟩
def coefficientLeftPorts : Fin 3 ↪ Fin 11 := ⟨![3, 5, 6], by decide⟩
def coefficientReversePorts : Fin 3 ↪ Fin 11 := ⟨![6, 5, 7], by decide⟩
def coefficientRightPorts : Fin 3 ↪ Fin 11 := ⟨![4, 5, 8], by decide⟩
def coefficientDotPorts : Fin 3 ↪ Fin 11 := ⟨![7, 8, 9], by decide⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

def coefficientStackPorts : Fin 11 ↪ Fin 12 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 12 => x.val) h⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


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

def fourRegisters : Fin 4 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h⟩

def onePort {S : ℕ} (port : Fin S) : Fin 1 ↪ Fin S :=
  ⟨fun _ => port, by intro i j _; exact Subsingleton.elim i j⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! PairProduct -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

def pairProductPorts : Fin 12 ↪ Fin 18 :=
  ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 18 => x.val) h⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Candidate -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

def candidatePorts : Fin 3 ↪ Fin 18 := ⟨![15, 5, 16], by decide⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductCheck -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

def productComparePorts : Fin 2 ↪ Fin 18 := ⟨![9, 16], by decide⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/

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

open IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def lowStacks (i : Fin 18) : Fin 24 := Fin.castAdd 6 i

def splitStacks : Fin 6 → Fin 24 := ![1,22,2,3,0,4]

theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _
theorem splitStacks_injective : Function.Injective splitStacks := by decide

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/

end OAI.Algorithms
end


