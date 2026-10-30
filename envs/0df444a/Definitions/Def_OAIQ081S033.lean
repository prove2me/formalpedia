-- Prove2me | Definitions.Def_OAIQ081S033
-- name    : OAIQ081S033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:31:14.149279+00:00
-- url     : https://prove2.me/theorems/5cdfeb58-ab33-4a3a-9174-d511b72b42f9
-- title:
--   Definitions bundle OAIQ081S033 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 66 declarations of OpenAI's Lean: 42 definitions and 24 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.digitCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.scanCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.scanI`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.scanJ`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.scanProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.subCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.subtract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.subtractProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.copyCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.presentTrue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.saveResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.unpack`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.presentTrue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.saveResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.unpack`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.appendOneCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.atomsCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.candidateCountAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.compareCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.compareCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.compareProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotCopyAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotFinalAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotInitialAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotReadAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.monicAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.nonconstantCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.nonconstantCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.nonconstantProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.pairProductSetupAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.prefixCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.prefixCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.prefixReverseProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.productIncrement`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.transferCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.truthTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.writePair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount.program` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IdempotentProgramMachine`, `SubexponentialSAT_SqrtLog_IdempotentProgramNative`, `SubexponentialSAT_SqrtLog_IdempotentProgramOutput`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramFrame`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramSubtract`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgram`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramNatural`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramSigned`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBasic`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPrimitives`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramCompare`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramLift`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramNonconstant`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefix`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramScalar`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPrepareCount`, `SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic`, `SubexponentialSAT_StackEncoding`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpTupleRefinement`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S009`, `OAIQ081S010` and `OAIQ081S011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S060` and `OAIQ081S063`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S009
import Definitions.Def_OAIQ081S010
import Definitions.Def_OAIQ081S011

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem encodeDataStack_eq_flatMap {α : Type u} (c : BlockCode α) (s : List α) :
    encodeDataStack c s = s.flatMap c.block := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [encodeDataStack, ih]

end SubexponentialSAT.StackEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

def digitCode {t : ℕ} (v : Fin (3*t) → C) (s : Fin t) (a : Fin 3) : C :=
  v (digitIndex s a)

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native Newton control, conditional only on explicitly supplied native
array-operation services. Each service hypothesis requires a real `Eval` of a
fixed finite command. The iteration count is stack data, not generated control.
This module does not claim that the array-service obligations are discharged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.StructuredCalls

variable {C A : Type*} [CommRing A] {r s : ℕ}

theorem constant_budget (bound start fuel : ℕ) :
    CounterForPrograms.budgetSum (fun _ => bound) start fuel = fuel*bound := by
  induction fuel generalizing start with
  | zero => simp [CounterForPrograms.budgetSum]
  | succ fuel ih => simp [CounterForPrograms.budgetSum, ih]; ring

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed four-array Newton machine. Its native services perform full dynamic
vector arithmetic, operand copying, and target replacement. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem arrayRegister_injective : Function.Injective arrayRegister := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [arrayRegister] at hv
  omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary scanner. Each complete triple contributes three tokens
to the accumulator; the two output flags encode the remainder modulo three.
No runtime integer arithmetic is an instruction of this machine. -/
namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

abbrev scanProgram : Program 4 2 17 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 10,
    .pop 0 0 1 3, .branch 1 4 12,
    .pop 0 0 1 5, .branch 1 6 14,
    .set 0 true 7, .push 1 0 8, .push 1 0 9, .push 1 0 0,
    .set 2 false 11, .set 3 false 16,
    .set 2 true 13, .set 3 false 16,
    .set 2 false 15, .set 3 true 16, .halt]

def scanCfg (pc : Option (Fin 17)) (r : Fin 4 → Bool)
    (xs ys : List Bool) : Cfg 4 2 17 := ⟨pc, r, ![xs, ys]⟩

theorem scan_small (r : Fin 4 → Bool) (ys : List Bool) (b : Fin 3) :
    Trace scanProgram (2 * b.val + 5)
      (scanCfg (some 0) r (List.replicate b.val true) ys)
      (scanCfg none (remainderRegs b.val) [] ys) := by
  fin_cases b <;> apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, scanProgram, scanCfg, execInstr,
      readRegs, remainderRegs, Function.update_apply]
  all_goals first
    | (constructor <;> (funext i; fin_cases i <;> simp))
    | (funext i; fin_cases i <;> simp)

theorem scan_three (r : Fin 4 → Bool) (xs ys : List Bool) :
    Trace scanProgram 10
      (scanCfg (some 0) r (true :: true :: true :: xs) ys)
      (scanCfg (some 0) (Function.update (Function.update r 0 true) 1 true)
        xs (true :: true :: true :: ys)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, scanProgram, scanCfg, execInstr,
    readRegs, Function.update_apply]
  all_goals first | (constructor <;> (funext i; fin_cases i <;> simp)) | (funext i; fin_cases i <;> simp)

theorem scan_quotient (q : ℕ) (b : Fin 3) (r : Fin 4 → Bool) (ys : List Bool) :
    Trace scanProgram (10*q + 2*b.val + 5)
      (scanCfg (some 0) r (List.replicate (3*q+b.val) true) ys)
      (scanCfg none (remainderRegs b.val) [] (List.replicate (3*q) true ++ ys)) := by
  induction q generalizing r ys with
  | zero => simpa using scan_small r ys b
  | succ q ih =>
      have h := (scan_three r (List.replicate (3*q+b.val) true) ys).trans
        (ih (Function.update (Function.update r 0 true) 1 true)
          (true :: true :: true :: ys))
      have hn : 3*(q+1)+b.val = 3+(3*q+b.val) := by omega
      have ho : List.replicate (3*q) true ++ true :: true :: true :: ys =
          List.replicate (3*(q+1)) true ++ ys := by
        rw [show 3*(q+1) = 3*q+3 by omega, List.replicate_add]
        simp [List.append_assoc]
      rw [ho] at h
      have hl : List.replicate (3*(q+1)+b.val) true =
          true :: true :: true :: List.replicate (3*q+b.val) true := by
        rw [hn,List.replicate_add]
        rfl
      have hc : 10*(q+1)+2*b.val+5 = 10+(10*q+2*b.val+5) := by omega
      rw [hl,hc]
      exact h

theorem scan_trace (n : ℕ) (r : Fin 4 → Bool) (ys : List Bool) :
    Trace scanProgram (10*(n/3) + 2*(n%3) + 5)
      (scanCfg (some 0) r (List.replicate n true) ys)
      (scanCfg none (remainderRegs (n%3)) []
        (List.replicate (3*(n/3)) true ++ ys)) := by
  have hn : 3*(n/3)+n%3 = n := by omega
  simpa only [hn] using
    scan_quotient (n/3) ⟨n%3, Nat.mod_lt _ (by decide)⟩ r ys

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramSubtract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

/-- Consuming subtraction of unary lengths, with an underflow flag. -/
abbrev subtractProgram : Program 4 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 4, .pop 1 0 2 3,
    .branch 2 0 5, .set 3 false 6, .set 3 true 6, .halt]

def subCfg (pc : Option (Fin 7)) (r : Fin 4 → Bool)
    (xs ys : List Bool) : Cfg 4 2 7 := ⟨pc, r, ![xs, ys]⟩

theorem sub_nil (r : Fin 4 → Bool) (ys : List Bool) :
    Trace subtractProgram 4 (subCfg (some 0) r [] ys)
      (subCfg none (Function.update (readRegs r 0 1 none) 3 false) [] ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, subCfg,
    execInstr, readRegs, Function.update_apply]

theorem sub_fail (r : Fin 4 → Bool) (xs : List Bool) :
    Trace subtractProgram 6 (subCfg (some 0) r (true :: xs) [])
      (subCfg none
        (Function.update (readRegs (readRegs r 0 1 (some true)) 0 2 none) 3 true)
        xs []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, subCfg,
    execInstr, readRegs, Function.update_apply]
  all_goals
    first | done | (funext i; fin_cases i <;> simp)

theorem sub_round (r : Fin 4 → Bool) (xs ys : List Bool) :
    Trace subtractProgram 4 (subCfg (some 0) r (true :: xs) (true :: ys))
      (subCfg (some 0) (readRegs (readRegs r 0 1 (some true)) 0 2 (some true))
        xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, subCfg,
    execInstr, readRegs, Function.update_apply]
  all_goals
    first | done | (funext i; fin_cases i <;> simp)

theorem subtract_trace (a b : ℕ) (r : Fin 4 → Bool) :
    ∃ n rf xs, n ≤ 4*a+4 ∧
      Trace subtractProgram n
        (subCfg (some 0) r (List.replicate a true) (List.replicate b true))
        (subCfg none rf xs (List.replicate (b-a) true)) ∧
      rf 3 = decide (b < a) ∧ xs.length ≤ a := by
  induction a generalizing b r with
  | zero =>
      exact ⟨4, _, [], by omega, sub_nil r _, by simp, by simp⟩
  | succ a ih =>
      cases b with
      | zero =>
          refine ⟨6,Function.update (readRegs (readRegs r 0 1 (some true)) 0 2 none) 3 true,
            List.replicate a true,by omega,?_,by simp,by simp⟩
          simpa only [List.replicate_succ,List.replicate_zero,Nat.zero_sub] using
            sub_fail r (List.replicate a true)
      | succ b =>
          obtain ⟨n, rf, xs, hn, hrun, hf, hx⟩ :=
            ih b (readRegs (readRegs r 0 1 (some true)) 0 2 (some true))
          refine ⟨4+n,rf,xs,by omega,?_,by simpa using hf,by omega⟩
          simpa only [List.replicate_succ,Nat.add_sub_add_right] using
            (sub_round r (List.replicate a true) (List.replicate b true)).trans hrun

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

abbrev Data := State 8 4

def data (r : Fin 8 → Bool) (xs ys zs bs : List Bool) : Data :=
  ⟨r,![xs,ys,zs,bs]⟩

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

abbrev scanI : Cmd 8 4 := .call (ProgramLinking.liftProgram scanProgram scanIRegs scanIPorts)
abbrev scanJ : Cmd 8 4 := .call (ProgramLinking.liftProgram scanProgram scanJRegs scanJPorts)
abbrev subtract : Cmd 8 4 := .call (ProgramLinking.liftProgram subtractProgram subRegs subPorts)

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open SubexponentialSAT BitProgram StructuredCalls
open CRTLocalProgram (LowFrame CachePort)

theorem scan_decode {C A : Type*} [Ring A] (decode : C → A)
    (add : C → C → C) (ha : ∀ x y, decode (add x y) = decode x + decode y)
    (bs : List Bool) (a p : C) :
    decode (scan add bs a p).1 = decode a + (BinaryArithmetic.toNat bs : A) * decode p := by
  induction bs generalizing a p with
  | nil => simp [scan]
  | cons b bs ih =>
    cases b <;> simp [scan, ih, ha, BinaryArithmetic.toNat] <;> noncomm_ring

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramNatural
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls
open CRTLocalProgram (LowFrame )

theorem naturalValue_decode {C A : Type*} [Ring A] (decode : C → A)
    (add : C → C → C) (ha : ∀ x y, decode (add x y) = decode x + decode y)
    (zero one : C) (hz : decode zero = 0) (ho : decode one = 1) (bits : List Bool) :
    decode (naturalValue add zero one bits) = (BinaryArithmetic.toNat bits : A) := by
  simp [naturalValue, scan_decode decode add ha, hz, ho]

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramSigned
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls
open CRTLocalProgram (LowFrame )

theorem signedValue_decode {C A : Type*} [Ring A] (decode : C → A)
    (mul add : C → C → C)
    (hm : ∀ x y, decode (mul x y) = decode x * decode y)
    (ha : ∀ x y, decode (add x y) = decode x + decode y)
    (zero one minusOne : C) (hz : decode zero = 0) (ho : decode one = 1)
    (hn : decode minusOne = -1) (positive negative : List Bool) :
    decode (signedValue mul add zero one minusOne positive negative) =
      (((BinaryArithmetic.toNat positive : ℤ) - (BinaryArithmetic.toNat negative : ℤ) : ℤ) : A) := by
  simp [signedValue, hm, ha, naturalValue_decode decode add ha zero one hz ho,
    hn, sub_eq_add_neg]

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite coefficient tests for arbitrary-degree irreducible search

Only vectors, finite lists, and scalar arithmetic are executed. `ofFn` and
the polynomial interpretation occur solely in the correctness proofs.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial
open scoped BigOperators

theorem nonconstant_iff {n : ℕ} (hn : 0 < n) (a : Fin n → F) :
    nonconstant a = true ↔ 0 < (Polynomial.ofFn n a).natDegree := by
  simp only [nonconstant, List.any_eq_true, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, ha⟩
    have hc : (Polynomial.ofFn n a).coeff i.val ≠ 0 := by simpa using ha
    exact hi.trans_le (le_natDegree_of_ne_zero hc)
  · intro hp
    have hb := Polynomial.ofFn_natDegree_lt hn a
    refine ⟨⟨(Polynomial.ofFn n a).natDegree, hb⟩, hp, ?_⟩
    have hz : Polynomial.ofFn n a ≠ 0 := by
      intro h
      simp [h] at hp
    have hc : (Polynomial.ofFn n a).coeff (Polynomial.ofFn n a).natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr hz
    rw [Polynomial.ofFn_coeff_eq_val_of_lt a hb] at hc
    exact hc

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open Subexp.TupleProgram

theorem vectors_map {A B : Type*} (f : A → B) (alphabet : List A) (n : ℕ) :
    QuarticSearch.vectors (alphabet.map f) n =
      (QuarticSearch.vectors alphabet n).map (fun v i => f (v i)) := by
  induction n with
  | zero =>
      simp only [QuarticSearch.vectors, List.map_cons, List.map_nil]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [QuarticSearch.vectors, ih, List.flatMap_map, List.map_flatMap,
        List.map_map, Function.comp_def]
      congr 1
      funext a
      congr 1
      funext v
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem tuplePayload_map {A : Type*} (code : StackEncoding.BlockCode A)
    {n : ℕ} (v : Fin n → A) :
    tuplePayload (fun i => code.block (v i)) = encodeTuple code v := by
  rw [encodeTuple, StackEncoding.encodeDataStack_eq_flatMap]
  change (List.ofFn (code.block ∘ v)).flatten = _
  rw [← List.map_ofFn]
  rfl

end SubexponentialSAT.SubexpTupleRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open BitProgram

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

theorem reverseRecords_budget (records : List (List Bool)) :
    RecordPrograms.budget (fun bits => 5 * bits.length + 12) records =
      11 * (records.map List.length).sum + 19 * records.length := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
      simp only [RecordPrograms.budget, ih, List.map_cons, List.sum_cons, List.length_cons]
      omega

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed word loading and framed stack routines for the search bootstrap. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls

abbrev copyCmd (src dst : Fin 28) : Cmd 22 28 :=
  .call (StackRoutines.copyProgram src dst 7 0 1)

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed truth-table arithmetic for the irreducible search over F₃

The six input bits select one of 64 *static* leaves. No parameter of the
polynomial search occurs in this instruction table. The two output bits
encode the multiply-add `s + a*b` in the same two-bit scalar format as the
audited tuple generator.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev writePair {R S : ℕ} (lo hi : Fin R) (bits : Bool × Bool) : Cmd R S :=
  .seq (.atom (.set lo bits.1)) (.atom (.set hi bits.2))

/-- Finite synthesis from a fixed list of input registers. Only register
branches and constant bit assignments occur in the resulting command. -/
def truthTable {R S : ℕ} (lo hi : Fin R) :
    List (Fin R) → (List Bool → Bool × Bool) → Cmd R S
  | [], f => writePair lo hi (f [])
  | i :: is, f => .ite i
      (truthTable lo hi is (fun bs => f (true :: bs)))
      (truthTable lo hi is (fun bs => f (false :: bs)))

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program for the dynamically long F₃ dot product. Every
coefficient is physically read and every multiply-add uses the static
64-entry bit table. The source arrays are consumed. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def atomsCommand {R S : ℕ} : List (Atom R S) → Cmd R S
  | [] => .skip
  | a :: as => .seq (.atom a) (atomsCommand as)

def dotReadAtoms : List (Atom 8 3) := [.pop 0 1 7, .pop 1 2 7, .pop 1 3 7]
def dotCopyAtoms : List (Atom 8 3) := [.copy 4 6, .copy 5 7]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

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

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def dotInitialAtoms : List (Atom 8 3) := [.set 4 false, .set 5 false, .pop 0 0 6]
def dotFinalAtoms : List (Atom 8 3) := [.push 2 5, .push 2 4]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-length padded prefixes, with reversal by coefficient rather
than by bit. This is the physical stream preparation needed before a
convolution dot product. A unary count controls one fixed eight-label
program; exhaustion of the coefficient source supplies the zero cell. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

abbrev prefixReverseProgram : Program 6 3 8 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.pop 1 4 5 1, .branch 5 2 7, .pop 0 0 2 3,
    .pop 0 1 2 4, .push 2 1 5, .push 2 0 6, .goto 0, .halt]

def prefixCfg (pc : Option (Fin 8)) (regs : Fin 6 → Bool)
    (source count output : List Bool) : Cfg 6 3 8 :=
  ⟨pc, regs, ![source, count, output]⟩

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

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev prefixCall {R S : ℕ} (regs : Fin 6 ↪ Fin R) (ports : Fin 3 ↪ Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram prefixReverseProgram regs ports)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control equality of equally long serialized coefficient arrays.
Both inputs are consumed. The length premise is supplied by the explicit
coefficient-count invariants, never by an unchecked array access. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

abbrev compareProgram : Program 4 2 8 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.set 3 true 1, .pop 0 0 1 2, .branch 1 3 7,
    .pop 1 2 1 4, .bxor 0 0 2 5, .bnot 0 0 6, .band 3 3 0 1, .halt]

def compareCfg (pc : Option (Fin 8)) (regs : Fin 4 → Bool)
    (left right : List Bool) : Cfg 4 2 8 := ⟨pc, regs, ![left, right]⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramNonconstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control detection of positive-degree coefficients. The constant
coefficient is physically skipped, then every remaining two-bit cell is
read. The result is register 3; no semantic predicate is an instruction. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

abbrev nonconstantProgram : Program 4 1 9 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 0 0 1 1, .pop 0 0 1 2, .set 3 false 3,
    .pop 0 0 1 4, .branch 1 5 8, .pop 0 2 1 6,
    .bor 0 0 2 7, .bor 3 3 0 3, .halt]

def nonconstantCfg (pc : Option (Fin 9)) (regs : Fin 4 → Bool)
    (input : List Bool) : Cfg 4 1 9 := ⟨pc, regs, ![input]⟩

theorem nonconstant_exit (regs : Fin 4 → Bool) :
    Trace nonconstantProgram 3
      (nonconstantCfg (some 3) regs [])
      (nonconstantCfg none (readRegs regs 0 1 none) []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nonconstantProgram, nonconstantCfg,
    execInstr, readRegs, Function.update_apply]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

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
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

def productIncrement : List (Atom 16 12) := [.set 14 false, .push 2 14]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductRun -/


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

abbrev transferCommand {S : ℕ} (src dst : Fin S) : Cmd 16 S :=
  .call (StackRoutines.transferProgram src dst 0 1)

def monicAtoms {S : ℕ} (src : Fin S) : List (Atom 16 S) :=
  [.set 2 false, .push src 2, .set 2 true, .push src 2]
abbrev appendOneCommand {S : ℕ} (src tmp : Fin S) : Cmd 16 S :=
  .seq (transferCommand src tmp) <|
    .seq (.base (atomsCommand (monicAtoms src))) (transferCommand tmp src)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! MonicAlgebra -/


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev compareCall {S : ℕ} (ports : Fin 2 ↪ Fin S) : Cmd 16 S :=
  .call (ProgramLinking.liftProgram compareProgram fourRegisters ports)

abbrev nonconstantCall {S : ℕ} (port : Fin S) : Cmd 16 S :=
  .call (ProgramLinking.liftProgram nonconstantProgram fourRegisters (onePort port))

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! PairProduct -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)
open SubexponentialSAT.SubexpSetupStorage

def pairProductSetupAtoms : List (Atom 16 18) :=
  [.set 14 false, .push 2 14, .push 11 14]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Candidate -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

def candidateCountAtoms : List (Atom 16 18) := [.set 14 false, .push 5 14]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductCheck -/


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

open BitProgram StructuredCalls IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem lowRegs_injective : Function.Injective lowRegs := Fin.castAdd_injective _ _
abbrev unpack : Cmd 19 24 := .call (StackRoutines.transferProgram 19 1 16 17)
abbrev saveResult : Cmd 19 24 := .base (.atom (.copy 18 3))
abbrev presentTrue : Cmd 19 24 := .base (.atom (.set 17 true))

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem lowRegs_injective : Function.Injective lowRegs := Fin.castAdd_injective _ _
theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _

abbrev unpack : Cmd 22 28 := .call (StackRoutines.transferProgram 25 13 19 20)
abbrev saveResult : Cmd 22 28 := .base (.atom (.copy 21 18))
abbrev presentTrue : Cmd 22 28 := .base (.atom (.set 20 true))

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPrepareCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonicalize an arbitrary unary counter by an actual fixed bit loop. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount
open SubexponentialSAT BitProgram StructuredCalls

abbrev program : Program 3 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1,.branch 1 2 4,.set 2 true 3,.push 1 2 0,.set 2 false 5,.halt]

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact signed arithmetic for minor enumeration. Integers are represented as
pairs of natural binary words. No modular arithmetic, integer oracle, or
parameter-dependent instruction table is used. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

abbrev Data := State 8 15

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

namespace NodeUnits

variable {node : I → E}

theorem differenceInverse_mul (u : NodeUnits node) {i j : I} (hij : i ≠ j) :
    u.differenceInverse i j * (node i - node j) = 1 := by
  rw [differenceInverse, dite_eq_left hij, ← u.differenceUnit_val i j hij]
  exact Units.inv_mul (u.differenceUnit i j hij)

end NodeUnits

variable {node : I → E}

theorem basisDivisor_eval_left (u : NodeUnits node) {i j : I} (hij : i ≠ j) :
    (basisDivisor u i j).eval (node i) = 1 := by
  simpa [basisDivisor] using u.differenceInverse_mul hij

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/
namespace SubexponentialSAT.Subexp.PackingLeftoverEmitter

open BitProgram StructuredCalls

abbrev Code := Cmd 8 9

end SubexponentialSAT.Subexp.PackingLeftoverEmitter


end OAI.Algorithms
end


