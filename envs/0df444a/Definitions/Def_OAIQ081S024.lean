-- Prove2me | Definitions.Def_OAIQ081S024
-- name    : OAIQ081S024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:27:01.973004+00:00
-- url     : https://prove2.me/theorems/95046c8d-67f6-4635-a337-dad1a145839f
-- title:
--   Definitions bundle OAIQ081S024 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 246 declarations of OpenAI's Lean: 135 definitions, 1 inductive type or structure and 110 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport.clearCmd`, `OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport.copyCmd`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedCopyProgram`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedCopyResult`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedCopyStacks`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedSkipProgram`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedSkipResult`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedSkipStacks`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedTransferProgram`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedTransferResult`, `OAI.Algorithms.SubexponentialSAT.ArrayPrograms.countedTransferStacks`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdateLifted.readProgramAt`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdateLifted.readStacksAt`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdateLifted.replaceProgramAt`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdateLifted.replaceStacksAt`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.afterIndexRead`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.readCmd`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.readIndexCmd`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.readProgram`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.readSelectedCmd`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.readStacks`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.replaceCmd`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.replaceProgram`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.replaceSelectedCmd`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.replaceStacks`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.saveBeforeCmd`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.saveBeforeLoop`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.saveRecordCmd`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.savedBeforeStacks`, `OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms.savedRecordStacks`, `OAI.Algorithms.SubexponentialSAT.BankRoutines.clearBankStacks`, `OAI.Algorithms.SubexponentialSAT.BankRoutines.clearCmd`, `OAI.Algorithms.SubexponentialSAT.BankRoutines.fillCmd`, `OAI.Algorithms.SubexponentialSAT.BitProgram.dataBits`, `OAI.Algorithms.SubexponentialSAT.CoreMaskProgram.Code`, `OAI.Algorithms.SubexponentialSAT.CoreMaskProgram.Data`, `OAI.Algorithms.SubexponentialSAT.CoreMaskProgram.atom`, `OAI.Algorithms.SubexponentialSAT.CoreMaskProgram.command`, `OAI.Algorithms.SubexponentialSAT.CoreMaskProgram.emit`, `OAI.Algorithms.SubexponentialSAT.CoreMaskProgram.frameBody` and 96 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ArithmeticExpressionSupport`, `SubexponentialSAT_ArrayPrograms`, `SubexponentialSAT_ArrayUpdateLifted`, `SubexponentialSAT_ArrayUpdatePrograms`, `SubexponentialSAT_BankRoutines`, `SubexponentialSAT_BitProgramSelectedSpace`, `SubexponentialSAT_BitProgramSpace`, `SubexponentialSAT_CoreMaskProgram`, `SubexponentialSAT_CounterForPrograms`, `SubexponentialSAT_CounterNormalizeProgram`, `SubexponentialSAT_CounterPrograms`, `SubexponentialSAT_DensePolynomialLoop`, `SubexponentialSAT_DensePolynomialPrograms`, `SubexponentialSAT_ModularArithmetic`, `SubexponentialSAT_ModularDivisionPrograms`, `SubexponentialSAT_ModularPrograms`, `SubexponentialSAT_ModularRingCore`, `SubexponentialSAT_ModularRingPrograms`, `SubexponentialSAT_ProgramLinking`, `SubexponentialSAT_StackRoutines`, `SubexponentialSAT_SubexpFlatAdd`, `SubexponentialSAT_SubexpLiftRing`, `SubexponentialSAT_SubexpModulusConstruction`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_SubexpPreparedQuartic`, `SubexponentialSAT_SubexpQuarticRing`, `SubexponentialSAT_SubexpScanPrimitives`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001` and `OAIQ081S002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S063` and `OAIQ081S064`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace.clear_bank_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace.local_stack_bound`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace.local_stack_bound`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLinking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite program relocation and linking

Every linked block is an instruction table inside one finite program.  A block's
halt can be replaced by a jump to a caller-specified continuation.  The proofs
below transfer actual instruction traces, including that final instruction, and
preserve all ambient registers and stacks outside the block's assigned ports.

The finite sizes and maps are fixed when the linked program is constructed; they
do not inspect the unbounded input stacks.
-/

namespace SubexponentialSAT.ProgramLinking

open BitProgram

variable {r s l R S L : ℕ}

theorem trace_from_halted (p : Program r s l) {n : ℕ} {a b : Cfg r s l}
    (h : Trace p n a b) (ha : a.pc = none) : b.pc = none := by
  cases h with
  | refl => exact ha
  | cons hs _ => simp [step, ha] at hs

/-! ## Concrete disjoint linking -/

end SubexponentialSAT.ProgramLinking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

open BitProgram

/-- A complete concrete three-label clear program. Label `2` is its halt. -/
abbrev clearProgram {r s : ℕ} (src : Fin s) (value present : Fin r) : Program r s 3 where
  inputStack := src
  outputStack := src
  entry := 0
  code := ![.pop src value present 1, .branch present 0 2, .halt]

/-- In-place reversal through two initially empty temporary stacks. The
program has ten fixed labels independently of the word length. -/
abbrev reverseProgram {r s : ℕ} (src tmp₁ tmp₂ : Fin s)
    (value present : Fin r) : Program r s 10 where
  inputStack := src
  outputStack := src
  entry := 0
  code := ![.pop src value present 1, .branch present 2 3, .push tmp₁ value 0,
    .pop tmp₁ value present 4, .branch present 5 6, .push tmp₂ value 3,
    .pop tmp₂ value present 7, .branch present 8 9, .push src value 6, .halt]

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev copyCmd {S : ℕ} (src dst tmp : Fin S) : Cmd 8 S :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

abbrev clearCmd {S : ℕ} (port : Fin S) : Cmd 8 S :=
  .call (StackRoutines.clearProgram port 0 1)

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArrayPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Dynamic counted operations on Boolean stacks

The counter is a stack whose *length* is the requested number of bits. Its bit
values are ignored. In particular, bounds are data, not control-label counts.
-/

namespace SubexponentialSAT.ArrayPrograms

open BitProgram StackRoutines

/-- Exact result of consuming a counted segment and reversing it onto `dst`. -/
def countedTransferStacks {s : ℕ} (counter src dst : Fin s) (segment rest : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update (Function.update stk counter []) src rest)
    dst (segment.reverse ++ stk dst)

def countedTransferResult {r s l : ℕ} (exit : Fin l) (counter src dst : Fin s)
    (value present : Fin r) (segment rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none,
    countedTransferStacks counter src dst segment rest stk⟩

theorem countedTransferStacks_step {s : ℕ} (counter src dst : Fin s)
    (a : Bool) (segment rest counterTail : List Bool) (stk : Stacks (Fin s))
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst) :
    countedTransferStacks counter src dst segment rest
        (Function.update
          (Function.update (Function.update stk counter counterTail) src (segment ++ rest))
          dst (a :: stk dst)) =
      countedTransferStacks counter src dst (a :: segment) rest stk := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp [countedTransferStacks, List.reverse_cons, List.append_assoc]
  · by_cases hs : j = src
    · subst j
      simp [countedTransferStacks, hsd]
    · by_cases hc : j = counter
      · subst j
        simp [countedTransferStacks, hcs, hcd]
      · simp [countedTransferStacks, hc, hs, hd]

abbrev countedTransferProgram {r s : ℕ} (counter src dst : Fin s)
    (value present : Fin r) : Program r s 5 where
  inputStack := src
  outputStack := dst
  entry := 0
  code := ![.pop counter value present 1, .branch present 2 4,
    .pop src value present 3, .push dst value 0, .halt]

def countedSkipStacks {s : ℕ} (counter src : Fin s) (rest : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update stk counter []) src rest

def countedSkipResult {r s l : ℕ} (exit : Fin l) (counter src : Fin s)
    (value present : Fin r) (rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, countedSkipStacks counter src rest stk⟩

theorem clear_after_countedTransfer {s : ℕ} (counter src tmp : Fin s)
    (segment rest : List Bool) (stk : Stacks (Fin s))
    (hct : counter ≠ tmp) (hst : src ≠ tmp) (htmp : stk tmp = []) :
    clearStacks tmp (countedTransferStacks counter src tmp segment rest stk) =
      countedSkipStacks counter src rest stk := by
  funext j
  by_cases ht : j = tmp
  · subst j; simp [clearStacks, countedTransferStacks, countedSkipStacks,
      hct.symm, hst.symm, htmp]
  · simp [clearStacks, countedTransferStacks, countedSkipStacks, ht]

abbrev countedSkipProgram {r s : ℕ} (counter src tmp : Fin s)
    (value present : Fin r) : Program r s 7 where
  inputStack := src
  outputStack := src
  entry := 0
  code := ![.pop counter value present 1, .branch present 2 4,
    .pop src value present 3, .push tmp value 0,
    .pop tmp value present 5, .branch present 4 6, .halt]

def countedCopyStacks {s : ℕ} (counter dst : Fin s) (segment : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update stk counter []) dst (segment ++ stk dst)

def countedCopyResult {r s l : ℕ} (exit : Fin l) (counter dst : Fin s)
    (value present : Fin r) (segment : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, countedCopyStacks counter dst segment stk⟩

abbrev countedCopyProgram {r s : ℕ} (counter src dst tmp : Fin s)
    (value present : Fin r) : Program r s 9 where
  inputStack := src
  outputStack := dst
  entry := 0
  code := ![.pop counter value present 1, .branch present 2 4,
    .pop src value present 3, .push tmp value 0,
    .pop tmp value present 5, .branch present 6 8,
    .push src value 7, .push dst value 4, .halt]

/-! ## Indexed fixed-width records

The seven stacks are: source 0, output 1, unary index 2, unary width 3,
temporary counter 4, copy scratch 5, and data scratch 6. Their contents can be
arbitrarily long. The program always has exactly 31 control labels.
-/

end SubexponentialSAT.ArrayPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArrayUpdatePrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving access and update of packed arrays

The instruction tables have eight Boolean stacks. The record index and width
are unary stack data, so neither value affects the finite program control.
Stack 7 saves the preceding records in reverse order and restores them after
the selected record is read or replaced.
-/

namespace SubexponentialSAT.ArrayUpdatePrograms

open BitProgram StackRoutines ArrayPrograms StructuredCalls

/-- Save one runtime-width record on stack 7, consuming neither the width nor
the existing saved records. -/
abbrev saveRecordCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (.call (copyProgram 3 4 5 value present))
    (.call (countedTransferProgram 4 0 7 value present))

def savedRecordStacks (record rest : List Bool) (stk : Stacks (Fin 8)) :
    Stacks (Fin 8) :=
  Function.update (Function.update stk 0 rest) 7 (record.reverse ++ stk 7)

abbrev readIndexCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .base (.atom (.pop 2 value present))

def afterIndexRead {r : ℕ} (value present : Fin r) (regs : Fin r → Bool)
    (stk : Stacks (Fin 8)) : State r 8 :=
  ⟨readRegs regs value present (stk 2).head?, Function.update stk 2 (stk 2).tail⟩

abbrev saveBeforeLoop {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .while present (.seq (saveRecordCmd value present) (readIndexCmd value present))

/-- The index is consumed; the width is preserved. -/
abbrev saveBeforeCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (readIndexCmd value present) (saveBeforeLoop value present)

def savedBeforeStacks (earlier : List (List Bool)) (rest : List Bool)
    (stk : Stacks (Fin 8)) : Stacks (Fin 8) :=
  Function.update (Function.update (Function.update stk 2 []) 0 rest)
    7 (earlier.flatten.reverse ++ stk 7)

theorem savedBeforeStacks_cons (row : List Bool) (earlier : List (List Bool))
    (rest indexTail : List Bool) (stk : Stacks (Fin 8)) :
    savedBeforeStacks earlier rest
        (savedRecordStacks row (earlier.flatten ++ rest) (Function.update stk 2 indexTail)) =
      savedBeforeStacks (row :: earlier) rest stk := by
  funext j
  fin_cases j <;> simp [savedBeforeStacks, savedRecordStacks, List.flatten_cons,
    List.reverse_append, List.append_assoc]

/-- Copy the selected record in forward order onto stack 1, preserving the
array suffix on stack 0. -/
abbrev readSelectedCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (.call (copyProgram 3 4 5 value present))
    (.call (countedCopyProgram 4 0 1 6 value present))

/-- Replace the selected record by the equally wide word in stack 1.
The replacement word itself is preserved. -/
abbrev replaceSelectedCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (.call (copyProgram 3 4 5 value present))
    (.seq (.call (countedSkipProgram 4 0 6 value present))
      (.call (copyProgram 1 0 6 value present)))

/-- The full access command restores all preceding records after reading. -/
abbrev readCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (saveBeforeCmd value present)
    (.seq (readSelectedCmd value present) (.call (transferProgram 7 0 value present)))

/-- The full update command restores all preceding records after replacement. -/
abbrev replaceCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (saveBeforeCmd value present)
    (.seq (replaceSelectedCmd value present) (.call (transferProgram 7 0 value present)))

def readStacks (record : List Bool) (stk : Stacks (Fin 8)) : Stacks (Fin 8) :=
  Function.update (Function.update stk 2 []) 1 (record ++ stk 1)

def replaceStacks (earlier : List (List Bool)) (replacement rest : List Bool)
    (stk : Stacks (Fin 8)) : Stacks (Fin 8) :=
  Function.update (Function.update stk 2 []) 0 (earlier.flatten ++ (replacement ++ rest))

/-- The compiled access program has 38 labels for every runtime width/index. -/
abbrev readProgram {r : ℕ} (value present : Fin r) : Program r 8 38 :=
  compiled (readCmd value present) 0 1

/-- The compiled replacement program has 44 labels for every runtime width/index. -/
abbrev replaceProgram {r : ℕ} (value present : Fin r) : Program r 8 44 :=
  compiled (replaceCmd value present) 0 0

@[simp] theorem readStacks_array (record : List Bool) (stk : Stacks (Fin 8)) :
    readStacks record stk 0 = stk 0 := by simp [readStacks]

@[simp] theorem readStacks_output (record : List Bool) (stk : Stacks (Fin 8)) :
    readStacks record stk 1 = record ++ stk 1 := by simp [readStacks]

@[simp] theorem readStacks_index (record : List Bool) (stk : Stacks (Fin 8)) :
    readStacks record stk 2 = [] := by simp [readStacks]

@[simp] theorem replaceStacks_array (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin 8)) :
    replaceStacks earlier replacement rest stk 0 =
      earlier.flatten ++ (replacement ++ rest) := by simp [replaceStacks]

@[simp] theorem replaceStacks_word (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin 8)) :
    replaceStacks earlier replacement rest stk 1 = stk 1 := by simp [replaceStacks]

@[simp] theorem replaceStacks_index (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin 8)) :
    replaceStacks earlier replacement rest stk 2 = [] := by simp [replaceStacks]

end SubexponentialSAT.ArrayUpdatePrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArrayUpdateLifted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Caller-state interfaces for the persistent packed-array routines. -/

namespace SubexponentialSAT.ArrayUpdateLifted

open BitProgram StackRoutines StructuredCalls ArrayUpdatePrograms

theorem extend_restrict {s : ℕ} (ports : Fin 8 ↪ Fin s) (stk : Stacks (Fin s)) :
    Function.extend ports (fun i => stk (ports i)) stk = stk := by
  classical
  funext j
  by_cases hj : ∃ i, ports i = j
  · obtain ⟨i, rfl⟩ := hj
    exact ports.injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hj

def readStacksAt {s : ℕ} (ports : Fin 8 ↪ Fin s) (record : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update stk (ports 2) []) (ports 1) (record ++ stk (ports 1))

def replaceStacksAt {s : ℕ} (ports : Fin 8 ↪ Fin s) (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update stk (ports 2) []) (ports 0)
    (earlier.flatten ++ (replacement ++ rest))

theorem extend_read {s : ℕ} (ports : Fin 8 ↪ Fin s) (record : List Bool)
    (stk : Stacks (Fin s)) :
    Function.extend ports (readStacks record (fun i => stk (ports i))) stk =
      readStacksAt ports record stk := by
  simp only [readStacks, ProgramLinking.extend_update ports.injective, extend_restrict]
  rfl

theorem extend_replace {s : ℕ} (ports : Fin 8 ↪ Fin s) (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin s)) :
    Function.extend ports (replaceStacks earlier replacement rest (fun i => stk (ports i))) stk =
      replaceStacksAt ports earlier replacement rest stk := by
  simp only [replaceStacks, ProgramLinking.extend_update ports.injective, extend_restrict]
  rfl

abbrev readProgramAt {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r) : Program r s 38 :=
  ProgramLinking.liftProgram (readProgram value present) id ports

abbrev replaceProgramAt {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r) : Program r s 44 :=
  ProgramLinking.liftProgram (replaceProgram value present) id ports

end SubexponentialSAT.ArrayUpdateLifted

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

/-- Empty the selected bank, preserving every other stack. -/
def clearBankStacks {S : Type u} [DecidableEq S] (ports : List S)
    (stk : Stacks S) : Stacks S :=
  fun j => if j ∈ ports then [] else stk j

@[simp] theorem clearBankStacks_nil {S : Type u} [DecidableEq S]
    (stk : Stacks S) : clearBankStacks [] stk = stk := by
  funext j
  simp [clearBankStacks]

@[simp] theorem clearBankStacks_mem {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∈ ports) :
    clearBankStacks ports stk j = [] := by
  simp [clearBankStacks, hj]

/-- One copy per static destination, followed by a read-register reset. -/
def fillCmd {r s : ℕ} (src tmp : Fin s) (value present : Fin r) :
    List (Fin s) → Cmd r s
  | [] => .call (clearProgram tmp value present)
  | dst :: dests => .seq (.call (copyProgram src dst tmp value present))
      (fillCmd src tmp value present dests)

/-- One clear per static bank port, followed by a read-register reset. -/
def clearCmd {r s : ℕ} (tmp : Fin s) (value present : Fin r) :
    List (Fin s) → Cmd r s
  | [] => .call (clearProgram tmp value present)
  | dst :: ports => .seq (.call (clearProgram dst value present))
      (clearCmd tmp value present ports)

@[simp] theorem size_fillCmd {r s : ℕ} (src tmp : Fin s) (value present : Fin r)
    (dests : List (Fin s)) :
    size (fillCmd src tmp value present dests) = 8 * dests.length + 3 := by
  induction dests with
  | nil => rfl
  | cons dst dests ih => simp [fillCmd, size, ih, Nat.mul_add]; omega

@[simp] theorem size_clearCmd {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) :
    size (clearCmd tmp value present ports) = 3 * ports.length + 3 := by
  induction ports with
  | nil => rfl
  | cons dst ports ih => simp [clearCmd, size, ih, Nat.mul_add]; omega

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

def dataBits {r s l : ℕ} (c : Cfg r s l) : ℕ := stackBits c.stacks

@[simp] theorem initial_dataBits {r s l : ℕ} (p : Program r s l) (input : List Bool) :
    dataBits (initial p input) = input.length := by
  simp only [dataBits, stackBits ]
  have lengths (k : Fin s) : (if k = p.inputStack then input else []).length =
      if k = p.inputStack then input.length else 0 := by split_ifs <;> rfl
  simp_rw [lengths]
  simp

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSelectedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Stack-bit growth inside a fixed set of ports

Every actual instruction adds at most one bit to any fixed set of stacks.
These bounds exclude unselected persistent stacks, whose contents may be
arbitrarily long. The list corollaries require distinct ports, as used by the
physical workspace cleanup program.
-/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem execInstr_selectedStackBits {r s l : ℕ} (ports : Finset (Fin s))
    (i : Instr r s l) (c : Cfg r s l) :
    selectedStackBits ports (execInstr i c).stacks ≤ selectedStackBits ports c.stacks + 1 := by
  cases i <;> try simp [execInstr]
  · rename_i stack src next
    exact selectedStackBits_update_le ports c.stacks stack
      (c.regs src :: c.stacks stack) (by simp)
  · rename_i stack value present next
    apply selectedStackBits_update_le ports c.stacks stack (c.stacks stack).tail
    cases c.stacks stack <;> simp ; omega

theorem step_selectedStackBits {r s l : ℕ} (p : Program r s l)
    (ports : Finset (Fin s)) {a b : Cfg r s l} (h : step p a = some b) :
    selectedStackBits ports b.stacks ≤ selectedStackBits ports a.stacks + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_selectedStackBits ports _ _

theorem trace_selectedStackBits {r s l : ℕ} (p : Program r s l)
    (ports : Finset (Fin s)) {a b : Cfg r s l} {n : ℕ} (h : Trace p n a b) :
    selectedStackBits ports b.stacks ≤ selectedStackBits ports a.stacks + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_selectedStackBits p ports hs
      omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CoreMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Applying a runtime mask to an encoded clause

The mask and clause occupy separate Boolean stacks.  Selection consumes one
mask bit per literal, treating a missing bit as false and leaving excess mask
bits unread.  Payloads are copied as framed bit strings without interpreting
their contents.
-/

namespace SubexponentialSAT.CoreMaskProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredProgram

abbrev Data := StructuredProgram.State 4 4
abbrev Code := StructuredCalls.Cmd 4 4

def state (tag present keep bit : Bool) (source mask accum output : List Bool) : Data :=
  ⟨regs tag present keep bit, stackData source mask accum output⟩

def atom (a : StructuredProgram.Atom 4 4) : Code := .base (.atom a)
def popTag : Code := atom (.pop 0 0 1)
def popBit : Code := atom (.pop 0 3 1)
def popMask : Code := atom (.pop 1 2 1)
def emit (r : Fin 4) : Code := .ite 2 (atom (.push 2 r)) (.base .skip)

def frameBody : Code := .seq (emit 0) (.seq popBit (.seq (emit 3) popTag))
def frameLoop : Code := .while 0 frameBody
def scanFrame : Code := .seq popTag (.seq frameLoop (emit 0))

def frameReady (bits tail mask accum output : List Bool) (keep bit : Bool) : Data :=
  match bits with
  | [] => state false true keep bit tail mask accum output
  | b :: bs => state true true keep bit (b :: (Encoding.frame bs ++ tail)) mask accum output

def recordBody : Code := .seq popMask (.seq (emit 0) (.seq scanFrame popTag))
def recordLoop : Code := .while 0 recordBody
def scanRecords : Code := .seq popTag recordLoop

def recordReady (records : List (List Bool)) (suffix mask accum output : List Bool)
    (keep bit : Bool) : Data :=
  match records with
  | [] => state false true keep bit suffix mask accum output
  | item :: rest => state true true keep bit
      (Encoding.frame item ++ (Encoding.encodeList id rest ++ suffix)) mask accum output

def reverseAccum : Code := .call (StackRoutines.transferProgram 2 3 3 1)
def resetKeep : Code := atom (.set 2 false)

def command : Code :=
  .seq scanRecords (.seq (atom (.push 2 0)) (.seq reverseAccum resetKeep))

def program := StructuredCalls.compiled command (0 : Fin 4) 3

end SubexponentialSAT.CoreMaskProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable binary counters on Boolean stacks

The head of a stack is the least-significant bit.  Leading zeroes are allowed:
there is no hidden normalization precondition, and zero testing scans the bits.
The arithmetic functions below specify the results of finite instruction-table
programs; the machine execution theorems appear after the specifications.
-/

namespace SubexponentialSAT.CounterPrograms


open SubexponentialSAT.BitProgram

def counterCfg {l : ℕ} (q : Fin l) (b p z : Bool) (xs ys : List Bool) : Cfg 3 2 l :=
  ⟨some q, counterRegs b p z, counterStacks xs ys⟩

/-- Eleven fixed labels implement carry/borrow and scratch restoration.
The `carry` parameter is a fixed program bit, not an unbounded control value. -/
abbrev rippleProgram (carry : Bool) : Program 3 2 11 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 5
    | 2 => if carry then .branch 0 3 5 else .branch 0 5 3
    | 3 => .bnot 0 0 4
    | 4 => .push 1 0 0
    | 5 => .set 0 carry 6
    | 6 => .push 0 0 7
    | 7 => .pop 1 0 1 8
    | 8 => .branch 1 9 10
    | 9 => .push 0 0 7
    | _ => .halt

@[simp] theorem ripple_step0_nil (c b p z : Bool) (ys : List Bool) :
    step (rippleProgram c) (counterCfg 0 b p z [] ys) =
      some (counterCfg 1 false false z [] ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem ripple_step0_cons (c b p z a : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 0 b p z (a :: xs) ys) =
      some (counterCfg 1 a true z xs ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem ripple_step1 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 1 b p z xs ys) =
      some (counterCfg (if p then 2 else 5) b p z xs ys) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem ripple_step2 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 2 b p z xs ys) =
      some (counterCfg (if b = c then 3 else 5) b p z xs ys) := by
  cases c <;> cases b <;> simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step3 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 3 b p z xs ys) =
      some (counterCfg 4 (!b) p z xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step4 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 4 b p z xs ys) =
      some (counterCfg 0 b p z xs (b :: ys)) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step5 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 5 b p z xs ys) =
      some (counterCfg 6 c p z xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step6 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 6 b p z xs ys) =
      some (counterCfg 7 b p z (b :: xs) ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step7_nil (c b p z : Bool) (xs : List Bool) :
    step (rippleProgram c) (counterCfg 7 b p z xs []) =
      some (counterCfg 8 false false z xs []) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem ripple_step7_cons (c b p z a : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 7 b p z xs (a :: ys)) =
      some (counterCfg 8 a true z xs ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem ripple_step8 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 8 b p z xs ys) =
      some (counterCfg (if p then 9 else 10) b p z xs ys) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem ripple_step9 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 9 b p z xs ys) =
      some (counterCfg 7 b p z (b :: xs) ys) := by
  simp [step, counterCfg, execInstr]

/-- Exact instruction count of the complete scratch-restoration loop. -/
theorem ripple_restore_trace (c b p z : Bool) (xs ys : List Bool) :
    Trace (rippleProgram c) (3 * ys.length + 2)
      (counterCfg 7 b p z xs ys)
      (counterCfg 10 false false z (ys.reverse ++ xs) []) := by
  induction ys generalizing b p xs with
  | nil =>
      simpa using SubexponentialSAT.Computation.Trace.cons (ripple_step7_nil c b p z xs)
        (SubexponentialSAT.Computation.Trace.cons (ripple_step8 c false false z xs [])
          (SubexponentialSAT.Computation.Trace.refl (counterCfg 10 false false z xs [])))
  | cons a ys ih =>
      have h := SubexponentialSAT.Computation.Trace.cons (ripple_step7_cons c b p z a xs ys)
        (SubexponentialSAT.Computation.Trace.cons (ripple_step8 c a true z xs ys)
          (SubexponentialSAT.Computation.Trace.cons (ripple_step9 c a true z xs ys) (ih a true (a :: xs))))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      simp [ List.reverse_cons, List.append_assoc]

/-- Complete program correctness, allowing arbitrary initial scratch contents.
The old scratch contents are restored to the front of the result in reverse. -/
theorem ripple_trace (c b p z : Bool) (xs ys : List Bool) :
    Trace (rippleProgram c) (rippleCost c xs + 3 * ys.length)
      (counterCfg 0 b p z xs ys)
      (counterCfg 10 false false z (ys.reverse ++ ripple c xs) []) := by
  induction xs generalizing b p ys with
  | nil =>
      have h := SubexponentialSAT.Computation.Trace.cons (ripple_step0_nil c b p z ys)
        (SubexponentialSAT.Computation.Trace.cons (ripple_step1 c false false z [] ys)
          (SubexponentialSAT.Computation.Trace.cons (ripple_step5 c false false z [] ys)
            (SubexponentialSAT.Computation.Trace.cons (ripple_step6 c c false z [] ys)
              (ripple_restore_trace c c false z [c] ys))))
      convert h using 1
      · simp [rippleCost ]
        omega
      · simp [ ripple]
  | cons a xs ih =>
      by_cases ha : a = c
      · subst a
        have h := SubexponentialSAT.Computation.Trace.cons (ripple_step0_cons c b p z c xs ys)
          (SubexponentialSAT.Computation.Trace.cons (ripple_step1 c c true z xs ys)
            (SubexponentialSAT.Computation.Trace.cons (by simp)
              (SubexponentialSAT.Computation.Trace.cons (ripple_step3 c c true z xs ys)
                (SubexponentialSAT.Computation.Trace.cons (ripple_step4 c (!c) true z xs ys)
                  (ih (!c) true ((!c) :: ys))))))
        convert h using 1 <;>
          simp [rippleCost, ripple, List.length_cons, List.reverse_cons, List.append_assoc]
        omega
      · have h := SubexponentialSAT.Computation.Trace.cons (ripple_step0_cons c b p z a xs ys)
          (SubexponentialSAT.Computation.Trace.cons (ripple_step1 c a true z xs ys)
            (SubexponentialSAT.Computation.Trace.cons (by simp [ha])
              (SubexponentialSAT.Computation.Trace.cons (ripple_step5 c a true z xs ys)
                (SubexponentialSAT.Computation.Trace.cons (ripple_step6 c c true z xs ys)
                  (ripple_restore_trace c c true z (c :: xs) ys)))))
        convert h using 1 <;> simp [rippleCost, ripple, ha]
        omega


@[simp] theorem initial_ripple_eq (c : Bool) (xs : List Bool) :
    initial (rippleProgram c) xs = counterCfg 0 false false false xs [] := by
  simp [initial, counterCfg ]
  constructor
  · funext i
    simp [counterRegs]
  · rfl

theorem ripple_halt_step (c : Bool) (xs : List Bool) :
    step (rippleProgram c) (counterCfg 10 false false false xs []) =
      some (terminal (rippleProgram c) xs) := by
  simp [step, counterCfg, execInstr, terminal, counterRegs, counterStacks]
  constructor
  · funext i
    simp [counterRegs]
  · rfl

/-- Complete execution from the language's actual input convention through halt. -/
theorem ripple_terminal_trace (c : Bool) (xs : List Bool) :
    Trace (rippleProgram c) (rippleCost c xs + 1)
      (initial (rippleProgram c) xs) (terminal (rippleProgram c) (ripple c xs)) := by
  have hbase : Trace (rippleProgram c) (rippleCost c xs)
      (counterCfg 0 false false false xs [])
      (counterCfg 10 false false false (ripple c xs) []) := by
    simpa using ripple_trace c false false false xs []
  have hhalt : Trace (rippleProgram c) 1
      (counterCfg 10 false false false (ripple c xs) [])
      (terminal (rippleProgram c) (ripple c xs)) :=
    .cons (ripple_halt_step c (ripple c xs)) (.refl _)
  simpa only [initial_ripple_eq] using hbase.trans hhalt

/-- A ten-label zero test. It preserves the data stack, clears scratch, and
returns its answer in Boolean register 2. -/
abbrev zeroProgram : Program 3 2 10 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .set 2 true 1
    | 1 => .pop 0 0 1 2
    | 2 => .branch 1 3 6
    | 3 => .push 1 0 4
    | 4 => .bnot 0 0 5
    | 5 => .band 2 2 0 1
    | 6 => .pop 1 0 1 7
    | 7 => .branch 1 8 9
    | 8 => .push 0 0 6
    | _ => .halt

@[simp] theorem zero_step0 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 0 b p z xs ys) =
      some (counterCfg 1 b p true xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem zero_step1_nil (b p z : Bool) (ys : List Bool) :
    step zeroProgram (counterCfg 1 b p z [] ys) =
      some (counterCfg 2 false false z [] ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem zero_step1_cons (b p z a : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 1 b p z (a :: xs) ys) =
      some (counterCfg 2 a true z xs ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem zero_step2 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 2 b p z xs ys) =
      some (counterCfg (if p then 3 else 6) b p z xs ys) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem zero_step3 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 3 b p z xs ys) =
      some (counterCfg 4 b p z xs (b :: ys)) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem zero_step4 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 4 b p z xs ys) =
      some (counterCfg 5 (!b) p z xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem zero_step5 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 5 b p z xs ys) =
      some (counterCfg 1 b p (z && b) xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem zero_step6_nil (b p z : Bool) (xs : List Bool) :
    step zeroProgram (counterCfg 6 b p z xs []) =
      some (counterCfg 7 false false z xs []) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem zero_step6_cons (b p z a : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 6 b p z xs (a :: ys)) =
      some (counterCfg 7 a true z xs ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem zero_step7 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 7 b p z xs ys) =
      some (counterCfg (if p then 8 else 9) b p z xs ys) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem zero_step8 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 8 b p z xs ys) =
      some (counterCfg 6 b p z (b :: xs) ys) := by
  simp [step, counterCfg, execInstr]

theorem zero_restore_trace (b p z : Bool) (xs ys : List Bool) :
    Trace zeroProgram (3 * ys.length + 2)
      (counterCfg 6 b p z xs ys)
      (counterCfg 9 false false z (ys.reverse ++ xs) []) := by
  induction ys generalizing b p xs with
  | nil =>
      simpa using SubexponentialSAT.Computation.Trace.cons (zero_step6_nil b p z xs)
        (SubexponentialSAT.Computation.Trace.cons (zero_step7 false false z xs [])
          (SubexponentialSAT.Computation.Trace.refl (counterCfg 9 false false z xs [])))
  | cons a ys ih =>
      have h := SubexponentialSAT.Computation.Trace.cons (zero_step6_cons b p z a xs ys)
        (SubexponentialSAT.Computation.Trace.cons (zero_step7 a true z xs ys)
          (SubexponentialSAT.Computation.Trace.cons (zero_step8 a true z xs ys) (ih a true (a :: xs))))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      simp [ List.reverse_cons, List.append_assoc]

/-- Exact trace through scan and restore, preserving every scanned data bit. -/
theorem zero_scan_trace (b p z : Bool) (xs ys : List Bool) :
    Trace zeroProgram (8 * xs.length + 3 * ys.length + 4)
      (counterCfg 1 b p z xs ys)
      (counterCfg 9 false false (z && isZero xs) (ys.reverse ++ xs) []) := by
  induction xs generalizing b p z ys with
  | nil =>
      have h := SubexponentialSAT.Computation.Trace.cons (zero_step1_nil b p z ys)
        (SubexponentialSAT.Computation.Trace.cons (zero_step2 false false z [] ys) (zero_restore_trace false false z [] ys))
      convert h using 1 <;> simp [isZero]
  | cons a xs ih =>
      have h := SubexponentialSAT.Computation.Trace.cons (zero_step1_cons b p z a xs ys)
        (SubexponentialSAT.Computation.Trace.cons (zero_step2 a true z xs ys)
          (SubexponentialSAT.Computation.Trace.cons (zero_step3 a true z xs ys)
            (SubexponentialSAT.Computation.Trace.cons (zero_step4 a true z xs (a :: ys))
              (SubexponentialSAT.Computation.Trace.cons (zero_step5 (!a) true z xs (a :: ys))
                (ih (!a) true (z && !a) (a :: ys))))))
      convert h using 1 <;>
        simp [isZero, Bool.and_assoc, List.length_cons, List.reverse_cons, List.append_assoc]
      omega


@[simp] theorem initial_zero_eq (xs : List Bool) :
    initial zeroProgram xs = counterCfg 0 false false false xs [] := by
  simp [initial, counterCfg ]
  constructor
  · funext i
    simp [counterRegs]
  · rfl


/-! ## Deriving a binary counter from an input list -/

def lengthCfg (q : Fin 14) (b p z : Bool) (data count scratch : List Bool) : Cfg 3 3 14 :=
  ⟨some q, counterRegs b p z, lengthStacks data count scratch⟩

/-- Count a list by consuming one bit and incrementing a binary stack counter.
The program has fourteen fixed labels; the input length is never in control. -/
abbrev lengthProgram : Program 3 3 14 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 13
    | 2 => .pop 1 0 1 3
    | 3 => .branch 1 4 7
    | 4 => .branch 0 5 7
    | 5 => .bnot 0 0 6
    | 6 => .push 2 0 2
    | 7 => .set 0 true 8
    | 8 => .push 1 0 9
    | 9 => .pop 2 0 1 10
    | 10 => .branch 1 11 12
    | 11 => .push 1 0 9
    | 12 => .goto 0
    | _ => .halt

theorem length_increment_code (i : Fin 11) (hi : i ≠ 10) :
    lengthProgram.code (lengthLabel i) =
      ProgramLinking.relocateInstr id Fin.succ lengthLabel none ((rippleProgram true).code i) := by
  fin_cases i <;>
    simp_all [ lengthLabel, ProgramLinking.relocateInstr]

@[simp] theorem embed_lengthCfg (q : Fin 11) (b p z : Bool) (data count scratch : List Bool) :
    ProgramLinking.embedCfg id Fin.succ lengthLabel none
      (lengthCfg 0 false false false data [] []) (counterCfg q b p z count scratch) =
        lengthCfg (lengthLabel q) b p z data count scratch := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, counterCfg, lengthCfg,
    extend_lengthStacks]

@[simp] theorem length_step0_nil (b p : Bool) (count : List Bool) :
    step lengthProgram (lengthCfg 0 b p false [] count []) =
      some (lengthCfg 1 false false false [] count []) := by
  simp [step, lengthCfg, execInstr, readRegs]

@[simp] theorem length_step0_cons (b p a : Bool) (data count : List Bool) :
    step lengthProgram (lengthCfg 0 b p false (a :: data) count []) =
      some (lengthCfg 1 a true false data count []) := by
  simp [step, lengthCfg, execInstr, readRegs]

@[simp] theorem length_step1 (b p : Bool) (data count : List Bool) :
    step lengthProgram (lengthCfg 1 b p false data count []) =
      some (lengthCfg (if p then 2 else 13) b p false data count []) := by
  simp [step, lengthCfg, execInstr]
  rfl

@[simp] theorem length_step12 (data count : List Bool) :
    step lengthProgram (lengthCfg 12 false false false data count []) =
      some (lengthCfg 0 false false false data count []) := by
  simp [step, lengthCfg, execInstr]

theorem length_halt_step (output : List Bool) :
    step lengthProgram (lengthCfg 13 false false false [] output []) =
      some (terminal lengthProgram output) := by
  simp [step, lengthCfg, execInstr, terminal]
  constructor
  · funext i
    simp [counterRegs]
  · funext i
    fin_cases i <;> simp [lengthStacks]

@[simp] theorem initial_length_eq (data : List Bool) :
    initial lengthProgram data = lengthCfg 0 false false false data [] [] := by
  simp [initial, lengthCfg]
  constructor
  · funext i
    simp [counterRegs]
  · funext i
    fin_cases i <;> simp [lengthStacks]

end SubexponentialSAT.CounterPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterForPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite binary-counted callback loop

The loop bound lives on a little-endian Boolean stack.  Fixed finite subroutines
perform zero testing and decrement, and an arbitrary fixed command is the loop
body.  The body may overwrite every register.  All measured evaluations below
compile to traces of a finite instruction table; proof-level state embeddings
are never used as executable instructions.
-/

namespace SubexponentialSAT.CounterForPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms

abbrev Data := StructuredProgram.State

variable {R S : ℕ}

@[ext] theorem data_ext {a b : Data R S} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

def localData (b present flag : Bool) (xs ys : List Bool) : Data 3 2 :=
  ⟨counterRegs b present flag, counterStacks xs ys⟩

end SubexponentialSAT.CounterForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Binary long division with finite-bit operations

The executable functions below inspect Bool/list constructors only: they do not
call Nat division, multiplication, comparison, or subtraction on encoded values.
Natural arithmetic appears solely in specifications and event-count proofs.
The event count is not asserted to be a primitive Turing-machine runtime.
-/

namespace SubexponentialSAT.ModularArithmetic

open SubexponentialSAT.BinaryArithmetic

theorem bitVal_le_one (b : Bool) : bitVal b ≤ 1 := by
  cases b <;> decide

theorem toNat_lt_pow_length (xs : List Bool) : BinaryArithmetic.toNat xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    have hb := bitVal_le_one b
    simp only [toNat_cons, List.length_cons, pow_succ]
    omega

theorem fullSubtractor_correct (a b borrow : Bool) :
    bitVal a + 2 * bitVal (borrowBit a b borrow) =
      bitVal b + bitVal borrow + bitVal (differenceBit a b borrow) := by
  cases a <;> cases b <;> cases borrow <;> decide

theorem subCarry_correct (c : Bool) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    BinaryArithmetic.toNat xs + 2 ^ xs.length * bitVal (subCarry c xs ys).2 =
      BinaryArithmetic.toNat ys + bitVal c + BinaryArithmetic.toNat (subCarry c xs ys).1 := by
  induction xs generalizing ys c with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simp [subCarry]
  | cons a as ih =>
    cases ys with
    | nil => simp at hlen
    | cons b bs =>
      have hl : as.length = bs.length := by simpa using hlen
      have ht := ih (borrowBit a b c) bs hl
      have hb := fullSubtractor_correct a b c
      simp only [subCarry, toNat_cons, List.length_cons, pow_succ]
      nlinarith

theorem subCarry_borrow_iff (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    (subCarry false xs ys).2 = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys := by
  have hv := subCarry_correct false xs ys hlen
  have hd := toNat_lt_pow_length (subCarry false xs ys).1
  rw [subCarry_length false xs ys hlen] at hd
  cases hc : (subCarry false xs ys).2 <;> simp [hc, bitVal] at hv ⊢ <;> omega

theorem padTo_correct (shape xs : List Bool) (hlen : xs.length ≤ shape.length) :
    BinaryArithmetic.toNat (padTo shape xs) = BinaryArithmetic.toNat xs := by
  induction shape generalizing xs with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst xs
    rfl
  | cons b shape ih =>
    cases xs with
    | nil => simp [padTo, ih [] (Nat.zero_le _), bitVal]
    | cons a as =>
      have hl : as.length ≤ shape.length := by simpa using hlen
      simp [padTo, toNat_cons, ih as hl]

theorem shiftReduce_correct (m r : List Bool) (b : Bool)
    (hlen : m.length ≤ r.length) (_hm : 0 < BinaryArithmetic.toNat m)
    (hr : BinaryArithmetic.toNat r < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (shiftReduce m r b) = (bitVal b + 2 * BinaryArithmetic.toNat r) % BinaryArithmetic.toNat m := by
  let shifted := b :: r
  let padded := padTo shifted m
  have hlength : shifted.length = padded.length := (padTo_length shifted m).symm
  have hpadded : BinaryArithmetic.toNat padded = BinaryArithmetic.toNat m :=
    padTo_correct shifted m (by simpa [shifted] using Nat.le_trans hlen (Nat.le_succ _))
  have hv := subCarry_correct false shifted padded hlength
  have hc := subCarry_borrow_iff shifted padded hlength
  have hb := bitVal_le_one b
  have hsmall : BinaryArithmetic.toNat shifted < 2 * BinaryArithmetic.toNat m := by
    simp only [shifted, toNat_cons]
    omega
  change BinaryArithmetic.toNat (if (subCarry false shifted padded).2 then shifted
    else (subCarry false shifted padded).1) = BinaryArithmetic.toNat shifted % BinaryArithmetic.toNat m
  cases hborrow : (subCarry false shifted padded).2 with
  | false =>
    have hid : BinaryArithmetic.toNat shifted = BinaryArithmetic.toNat m + BinaryArithmetic.toNat (subCarry false shifted padded).1 := by
      simpa only [hborrow, bitVal, Bool.false_eq_true, ↓reduceIte,
        mul_zero, add_zero, hpadded] using hv
    have hd : BinaryArithmetic.toNat (subCarry false shifted padded).1 < BinaryArithmetic.toNat m := by omega
    simp only [ Bool.false_eq_true, ↓reduceIte]
    rw [hid, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hd]
  | true =>
    have hlt : BinaryArithmetic.toNat shifted < BinaryArithmetic.toNat m := by
      simpa only [hpadded] using hc.mp hborrow
    simp only [ ↓reduceIte, Nat.mod_eq_of_lt hlt]

/-- Correct modular reduction, proved without Nat division in the algorithm. -/
theorem reduce_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (reduce m xs) = BinaryArithmetic.toNat xs % BinaryArithmetic.toNat m := by
  induction xs with
  | nil =>
    simpa [reduce] using padTo_correct m [] (Nat.zero_le _)
  | cons b bs ih =>
    rw [reduce, shiftReduce_correct]
    · simp only [toNat_cons, ih, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    · rw [reduce_length]
      omega
    · exact hm
    · rw [ih]
      exact Nat.mod_lt _ hm

/-! A measured finite-control subtraction transducer. -/

/-! Instrumentation with events carrying only finitely many Boolean values.
The logs record every padding/subtraction cell and each shift/selection.
They are not a primitive-machine simulation certificate. -/

/-! Modular addition and multiplication combine the concrete binary
arithmetic runs with the concrete long-division run. -/

abbrev ModularEvent := SubexponentialSAT.BinaryArithmetic.BitEvent ⊕ Event

def addModRun (m xs ys : List Bool) : List Bool × List ModularEvent :=
  let added := SubexponentialSAT.BinaryArithmetic.addRun false xs ys
  let reduced := reduceLogged m added.1
  (reduced.1, added.2.map Sum.inl ++ reduced.2.map Sum.inr)

/-! An explicit finite ring expression for geometric correction. Its
operation-node count is a ring-operation bound, separately from bit costs. -/

end SubexponentialSAT.ModularArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiftRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform coefficient representations for the growing-parameter argument

Every base residue has an explicit little-endian word of width
`mu * (Nat.log 2 p + 1)`. The polynomial quotient uses one such word per
basis coefficient. These bounds keep p and mu visible. Binary modular
operations below use the existing bit/list algorithms and normalize back
to the prescribed width; their counters are source-level finite events,
not a claimed Turing-machine simulation.
-/

namespace SubexponentialSAT.SubexpLiftRing

open SubexponentialSAT.BinaryArithmetic

theorem bitVal_mod_two (n : ℕ) : bitVal (decide (n % 2 = 1)) = n % 2 := by
  have h := Nat.mod_lt n (by decide : 0 < 2)
  by_cases he : n % 2 = 1 <;> simp [bitVal, he] ; omega

theorem toNat_fixedBits (B n : ℕ) : BinaryArithmetic.toNat (fixedBits B n) = n % 2 ^ B := by
  induction B generalizing n with
  | zero => simp [fixedBits, Nat.mod_one]
  | succ B ih =>
      rw [fixedBits, toNat_cons, bitVal_mod_two, ih, pow_succ']
      exact Nat.mod_mul.symm

theorem toNat_fixedBits_of_lt (B n : ℕ) (hn : n < 2 ^ B) :
    BinaryArithmetic.toNat (fixedBits B n) = n := by rw [toNat_fixedBits, Nat.mod_eq_of_lt hn]

section ResidueEncoding

variable (p μ : ℕ) [Fact p.Prime]

theorem encodeBase_value (x : ZMod (p ^ μ)) : BinaryArithmetic.toNat (encodeBase p μ x) = x.val :=
  toNat_fixedBits_of_lt _ _ (x.val_lt.trans_le (modulus_le_width p μ))

end ResidueEncoding

/-- Truncating high zero bits preserves any value already below the capacity. -/
theorem toNat_take_of_lt (B : ℕ) (xs : List Bool) (hx : BinaryArithmetic.toNat xs < 2 ^ B) :
    BinaryArithmetic.toNat (xs.take B) = BinaryArithmetic.toNat xs := by
  induction B generalizing xs with
  | zero => simpa using (Nat.eq_zero_of_le_zero (by simpa using hx)).symm
  | succ B ih =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          have htail : BinaryArithmetic.toNat xs < 2 ^ B := by
            rw [toNat_cons, pow_succ] at hx
            omega
          simpa using congrArg (fun n => bitVal a + 2 * n) (ih xs htail)

theorem normalizeBits_value (B : ℕ) (xs : List Bool) (hx : BinaryArithmetic.toNat xs < 2 ^ B) :
    BinaryArithmetic.toNat (normalizeBits B xs) = BinaryArithmetic.toNat xs := by
  rw [normalizeBits, ModularArithmetic.padTo_correct]
  · exact toNat_take_of_lt B xs hx
  · simp only [List.length_replicate, List.length_take]
    exact Nat.min_le_left _ _

/-- Addition of encoded residues using only the already verified binary
arithmetic, binary division, and bounded list normalization. -/
def addBaseRun (B : ℕ) (modulus xs ys : List Bool) : List Bool × ℕ :=
  let out := ModularArithmetic.addModRun modulus xs ys
  (normalizeBits B out.1, out.2.length + 3 * B)

@[simp] theorem addBaseRun_length (B : ℕ) (m xs ys : List Bool) :
    (addBaseRun B m xs ys).1.length = B := by simp [addBaseRun]

end SubexponentialSAT.SubexpLiftRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpModulusConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Constructing the prime-power modulus by binary multiplication

The data routine calls the existing binary `mulRun` once per iteration and
starts with the one-bit representation of one. No natural-number exponentiation
or conversion of the encoded value occurs in the data path. A single final
traced pass trims or zero-pads the output. Cost statements count the concrete
finite-alphabet BitEvent traces, not primitive-machine execution steps.
-/

namespace SubexponentialSAT.SubexpModulusConstruction

open BinaryArithmetic

/-- A single pass of exactly the requested output width. Each step inspects
an input cell and writes either its bit or a padding zero. -/
def normalizeRun : ℕ → List Bool → List Bool × List BitEvent
  | 0, _ => ([], [.control])
  | B + 1, [] =>
      let next := normalizeRun B []
      (false :: next.1, [.control, .inspect, .push] ++ next.2)
  | B + 1, b :: bs =>
      let next := normalizeRun B bs
      (b :: next.1, [.control, .inspect, .push] ++ next.2)

theorem normalizeRun_eq (B : ℕ) (xs : List Bool) :
    (normalizeRun B xs).1 = SubexpLiftRing.normalizeBits B xs := by
  induction B generalizing xs with
  | zero => simp [normalizeRun, SubexpLiftRing.normalizeBits, ModularArithmetic.padTo]
  | succ B ih =>
      cases xs <;>
        simp [normalizeRun, ih, SubexpLiftRing.normalizeBits,
          ModularArithmetic.padTo, List.replicate_succ]

@[simp] theorem normalizeRun_length (B : ℕ) (xs : List Bool) :
    (normalizeRun B xs).1.length = B := by
  rw [normalizeRun_eq, SubexpLiftRing.normalizeBits_length]

@[simp] theorem normalizeRun_cost (B : ℕ) (xs : List Bool) :
    (normalizeRun B xs).2.length = 3 * B + 1 := by
  induction B generalizing xs with
  | zero => simp [normalizeRun]
  | succ B ih =>
      cases xs <;> simp [normalizeRun, ih] <;> omega

theorem normalizeRun_value (B : ℕ) (xs : List Bool) (hx : BinaryArithmetic.toNat xs < 2 ^ B) :
    BinaryArithmetic.toNat (normalizeRun B xs).1 = BinaryArithmetic.toNat xs := by
  rw [normalizeRun_eq]
  exact SubexpLiftRing.normalizeBits_value B xs hx

end SubexponentialSAT.SubexpModulusConstruction

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

open SubexponentialSAT.BitProgram
open SubexponentialSAT.CounterPrograms

/-! ## Consume a most-significant zero prefix and the leading one -/

abbrev trimProgram : Program 3 3 6 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 1 0 1 1
    | 1 => .branch 1 2 3
    | 2 => .branch 0 3 0
    | 3 => .set 0 false 4
    | 4 => .set 1 false 5
    | _ => .halt

/-! ## Concrete input reversal -/

abbrev reverseTransfer : Program 3 3 4 := StackRoutines.transferProgram 0 1 0 1

abbrev prepareLogProgram : Program 3 3 10 := ProgramLinking.link reverseTransfer trimProgram

/-! ## Reindex and call the checked binary word-length counter -/

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterNormalizeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual normalization of a positive binary counter word

The logarithm preparer reverses its input and removes high zeroes together
with the leading one. This wrapper physically restores that one and reverses
the remaining word. Positive inputs therefore retain their exact value and
have width log2(value)+1. All three registers and both work stacks are clean
at return, even when the incoming registers are arbitrary.
-/

namespace SubexponentialSAT.CounterNormalizeProgram

open BitProgram StructuredProgram StructuredCalls CounterPrograms

abbrev Data := StructuredProgram.State 3 3

def state (regs : Fin 3 → Bool) (input output : List Bool) : Data :=
  ⟨regs, ![input, output, []]⟩

abbrev reset : StructuredCalls.Cmd 3 3 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

abbrev pushTop : StructuredCalls.Cmd 3 3 :=
  .base (.seq (.atom (.set 0 true)) (.atom (.push 1 0)))

def pushed (d : Data) : Data :=
  ⟨Function.update d.regs 0 true, Function.update d.stacks 1 (true :: d.stacks 1)⟩

abbrev reverseProgram : Program 3 3 4 := StackRoutines.transferProgram 1 0 0 1

def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 1 0 d.stacks⟩

abbrev restore : StructuredCalls.Cmd 3 3 := .seq pushTop (.call reverseProgram)

abbrev command : StructuredCalls.Cmd 3 3 :=
  .seq reset (.seq (.call SubexpParameterProgram.prepareLogProgram) restore)

abbrev program : Program 3 3 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 0

@[simp] theorem command_size : StructuredCalls.size command = 19 := by
  simp [ StructuredCalls.size, StructuredProgram.size]

end SubexponentialSAT.CounterNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpQuarticRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed-size, executable quartic ring implementation

The data are four coefficients.  Multiplication is Horner evaluation with
the explicit reduction `T^4 = t0 + t1*T + t2*T^2 + t3*T^3`.
The coefficient operations are parameters of the implementation; the binary
instance below discharges their correctness and uniform finite-event bound.
-/

namespace SubexponentialSAT.SubexpQuarticRing

/-! These loops execute exactly the displayed scalar calls. -/

section BinaryInstance

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing

variable (p μ : ℕ) [Fact p.Prime]

def wordValue (x : Word (baseWidth p μ)) : ZMod (p^μ) := (BinaryArithmetic.toNat x.val : ℕ)

def encodeWord (x : ZMod (p^μ)) : Word (baseWidth p μ) :=
  ⟨encodeBase p μ x, encodeBase_length p μ x⟩

@[simp] theorem wordValue_encodeWord (x : ZMod (p^μ)) :
    wordValue p μ (encodeWord p μ x) = x := by
  simp [wordValue, encodeWord, encodeBase_value]

end BinaryInstance

end SubexponentialSAT.SubexpQuarticRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScanPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack operations used by the serialized coefficient scanner. -/

namespace SubexponentialSAT.SubexpScanPrimitives

open BitProgram StructuredCalls

/-- Copy the runtime width, consume exactly that many source bits, and restore
their order in the destination. The control table does not contain the width. -/
abbrev takeWord {r s : ℕ} (width counter tmp src dst : Fin s) (v p : Fin r) : Cmd r s :=
  .seq (.call (StackRoutines.copyProgram width counter tmp v p))
    (.seq (.call (ArrayPrograms.countedTransferProgram counter src tmp v p))
      (.call (StackRoutines.transferProgram tmp dst v p)))

end SubexponentialSAT.SubexpScanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DensePolynomialLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed streaming array loop, parameterized by a finite word program
and an actual trace theorem for one word. The concrete modular-word
instantiation is supplied in DensePolynomialPrograms. -/

namespace SubexponentialSAT.DensePolynomialLoop

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 20

def state (regs : Fin 8 → Bool)
    (x y modulus left right width counter tmp packed : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  ⟨regs, stackArray x y modulus left right width counter tmp packed frame⟩

def ready (regs : Fin 8 → Bool) (modulus left right width packed : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  state regs [] [] modulus left right width [] [] packed frame

abbrev guard : Cmd 8 20 :=
  .seq (.base (.atom (.peek 8 0 1)))
    (.seq (.base (.atom (.peek 9 2 3))) (.base (.atom (.band 4 1 3))))

def guardRegs (regs : Fin 8 → Bool) (left right : List Bool) : Fin 8 → Bool :=
  let r := readRegs (readRegs regs 0 1 left.head?) 2 3 right.head?
  Function.update r 4 (r 1 && r 3)

@[simp] theorem guardRegs_test (regs : Fin 8 → Bool) (left right : List Bool) :
    guardRegs regs left right 4 = (left.head?.isSome && right.head?.isSome) := by
  simp [guardRegs, readRegs]

abbrev addLoop (step : Cmd 8 20) : Cmd 8 20 := .while 4 (.seq step guard)

abbrev flush : Cmd 8 20 :=
  .seq (.call (StackRoutines.transferProgram 8 13 (0 : Fin 8) 1))
    (.seq (.call (StackRoutines.transferProgram 9 13 (0 : Fin 8) 1))
      (.call (StackRoutines.transferProgram 13 8 (0 : Fin 8) 1)))

abbrev addCmd (step : Cmd 8 20) : Cmd 8 20 := .seq guard (.seq (addLoop step) flush)


end SubexponentialSAT.DensePolynomialLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPreparedQuartic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Quartic operations with a stored modulus

The modulus is input data. None of the operations in this file computes
`p^mu`, its bit expansion, or an irreducible polynomial. Setup is separate.
-/

namespace SubexponentialSAT.SubexpPreparedQuartic

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Prepared bytes together with their mathematical interpretation. -/
structure Modulus (p μ : ℕ) where
  bits : List Bool
  length_le : bits.length ≤ baseWidth p μ + 1
  value : BinaryArithmetic.toNat bits = p^μ

variable (p μ : ℕ) [Fact p.Prime]

/-- The same explicit traced copying/padding routine prepares literal words.
Its input is a fixed literal list, never a natural-number residue conversion. -/
def literalWordRun (literal : List Bool) : Word (baseWidth p μ) × ℕ :=
  let out := SubexpModulusConstruction.normalizeRun (baseWidth p μ) literal
  (⟨out.1, SubexpModulusConstruction.normalizeRun_length _ _⟩, out.2.length)

omit [Fact (Nat.Prime p)] in
@[simp] theorem literalWordRun_zero :
    wordValue p μ (literalWordRun p μ []).1 = 0 := by
  change (BinaryArithmetic.toNat (SubexpModulusConstruction.normalizeRun _ []).1 : ZMod (p^μ)) = 0
  rw [SubexpModulusConstruction.normalizeRun_value]
  · simp [SubexponentialSAT.BinaryArithmetic.toNat]
  · exact Nat.two_pow_pos _

variable (M : Modulus p μ)

def wordAdd (x y : Word (baseWidth p μ)) : Word (baseWidth p μ) × ℕ :=
  let r := addBaseRun (baseWidth p μ) M.bits x.val y.val
  (⟨r.1, addBaseRun_length _ _ _ _⟩, r.2)

end SubexponentialSAT.SubexpPreparedQuartic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean-stack programs for modular arithmetic

The programs in this file use only a fixed finite collection of labels,
Boolean registers, and Boolean stacks. The operand width and modulus are data.
-/

namespace SubexponentialSAT.ModularPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic

/-- Three operand stacks, eight Boolean registers, and thirteen fixed labels.
Register 0 is the incoming/outgoing borrow. Stacks 0 and 1 are consumed;
stack 2 receives the reversed difference. -/
abbrev subtractProgram : Program 8 3 13 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code label :=
    match label.val with
    | 0 => .pop 0 1 3 1
    | 1 => .branch 3 2 12
    | 2 => .pop 1 2 4 3
    | 3 => .bxor 5 1 2 4
    | 4 => .bxor 6 5 0 5
    | 5 => .bnot 7 1 6
    | 6 => .band 7 7 2 7
    | 7 => .bnot 5 5 8
    | 8 => .band 5 5 0 9
    | 9 => .bxor 0 7 5 10
    | 10 => .push 2 6 11
    | 11 => .goto 0
    | _ => .halt

abbrev subtractCfg (pc : Option (Fin 13)) (regs : Fin 8 → Bool)
    (left right output : List Bool) : Cfg 8 3 13 :=
  ⟨pc, regs, operandStacks left right output⟩

/-- Exact register transformation of one subtraction cell. -/
def roundRegs (regs : Fin 8 → Bool) (a b : Bool) : Fin 8 → Bool :=
  let r := readRegs (readRegs regs 1 3 (some a)) 2 4 (some b)
  let r := Function.update r 5 (a ^^ b)
  let r := Function.update r 6 ((a ^^ b) ^^ regs 0)
  let r := Function.update r 7 (!a)
  let r := Function.update r 7 ((!a) && b)
  let r := Function.update r 5 (!(a ^^ b))
  let r := Function.update r 5 ((!(a ^^ b)) && regs 0)
  Function.update r 0 (((!a) && b) ^^ ((!(a ^^ b)) && regs 0))

theorem roundRegs_borrow (regs : Fin 8 → Bool) (a b : Bool) :
    roundRegs regs a b 0 = borrowBit a b (regs 0) := by
  simp [roundRegs, borrowBit_gate_form]

/-- An actual twelve-instruction trace of the fixed Boolean program. -/
theorem subtract_round (regs : Fin 8 → Bool)
    (a b : Bool) (xs ys output : List Bool) :
    Trace subtractProgram 12
      (subtractCfg (some 0) regs (a :: xs) (b :: ys) output)
      (subtractCfg (some 0) (roundRegs regs a b) xs ys
        (differenceBit a b (regs 0) :: output)) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, execInstr,
    subtractCfg, readRegs, roundRegs, differenceBit,
    stacks_update_left, stacks_update_right, stacks_update_output,
    Function.update_apply]

theorem subtract_exit (regs : Fin 8 → Bool) (output : List Bool) :
    Trace subtractProgram 3
      (subtractCfg (some 0) regs [] [] output)
      (subtractCfg none (readRegs regs 1 3 none) [] [] output) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, execInstr,
    subtractCfg, readRegs, stacks_update_left,
    Function.update_apply]

/-- Full measured subtraction on arbitrary equal-width operands. -/
theorem subtract_correct (regs : Fin 8 → Bool) (xs ys output : List Bool)
    (hlen : xs.length = ys.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace subtractProgram (12 * xs.length + 3)
        (subtractCfg (some 0) regs xs ys output)
        (subtractCfg none finalRegs [] []
          ((subCarry (regs 0) xs ys).1.reverse ++ output)) ∧
      finalRegs 0 = (subCarry (regs 0) xs ys).2 := by
  induction xs generalizing regs ys output with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    refine ⟨readRegs regs 1 3 none, ?_, ?_⟩
    · simpa [subCarry] using subtract_exit regs output
    · simp [readRegs, subCarry]
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hl : xs.length = ys.length := by simpa using hlen
      obtain ⟨finalRegs, hrun, hborrow⟩ :=
        ih (roundRegs regs a b) ys (differenceBit a b (regs 0) :: output) hl
      refine ⟨finalRegs, ?_, ?_⟩
      · have h := (subtract_round regs a b xs ys output).trans hrun
        convert h using 1 <;>
          simp [subCarry, roundRegs_borrow, List.reverse_cons, List.append_assoc] ; omega
      · simpa [subCarry, roundRegs_borrow] using hborrow

/-- Pad a modulus word to the width of a shape word. Both input stacks are
consumed; the padded word is pushed in reverse onto output stack 2. -/
abbrev paddingProgram : Program 8 3 5 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code label :=
    match label.val with
    | 0 => .pop 0 1 3 1
    | 1 => .branch 3 2 4
    | 2 => .pop 1 2 4 3
    | 3 => .push 2 2 0
    | _ => .halt

abbrev paddingCfg (pc : Option (Fin 5)) (regs : Fin 8 → Bool)
    (shape input output : List Bool) : Cfg 8 3 5 :=
  ⟨pc, regs, operandStacks shape input output⟩

def paddingRegs (regs : Fin 8 → Bool) (shapeBit : Bool) (input : List Bool) :
    Fin 8 → Bool :=
  readRegs (readRegs regs 1 3 (some shapeBit)) 2 4 input.head?

theorem padding_round (regs : Fin 8 → Bool) (a : Bool)
    (shape input output : List Bool) :
    Trace paddingProgram 4
      (paddingCfg (some 0) regs (a :: shape) input output)
      (paddingCfg (some 0) (paddingRegs regs a input) shape input.tail
        (input.head?.getD false :: output)) := by
  cases input <;>
    apply SubexponentialSAT.Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
      paddingCfg, paddingRegs, readRegs,
      stacks_update_left, stacks_update_right, stacks_update_output,
      Function.update_apply]

theorem padding_exit (regs : Fin 8 → Bool) (output : List Bool) :
    Trace paddingProgram 3
      (paddingCfg (some 0) regs [] [] output)
      (paddingCfg none (readRegs regs 1 3 none) [] [] output) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
    paddingCfg, readRegs, stacks_update_left, Function.update_apply]

theorem padding_correct (regs : Fin 8 → Bool) (shape input output : List Bool)
    (hlen : input.length ≤ shape.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace paddingProgram (4 * shape.length + 3)
        (paddingCfg (some 0) regs shape input output)
        (paddingCfg none finalRegs [] [] ((padTo shape input).reverse ++ output)) ∧
      finalRegs 0 = regs 0 := by
  induction shape generalizing regs input output with
  | nil =>
    have hi : input = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst input
    refine ⟨readRegs regs 1 3 none, ?_, ?_⟩
    · simpa [padTo] using padding_exit regs output
    · simp [readRegs]
  | cons a shape ih =>
    cases input with
    | nil =>
      obtain ⟨finalRegs, hrun, hreg⟩ :=
        ih (paddingRegs regs a []) [] (false :: output) (Nat.zero_le _)
      refine ⟨finalRegs, ?_, ?_⟩
      · have h := (padding_round regs a shape [] output).trans hrun
        convert h using 1 <;> simp [padTo, List.reverse_cons, List.append_assoc] ; omega
      · simpa [paddingRegs, readRegs] using hreg
    | cons b input =>
      have hl : input.length ≤ shape.length := by simpa using hlen
      obtain ⟨finalRegs, hrun, hreg⟩ :=
        ih (paddingRegs regs a (b :: input)) input (b :: output) hl
      refine ⟨finalRegs, ?_, ?_⟩
      · have h := (padding_round regs a shape (b :: input) output).trans hrun
        convert h using 1 <;> simp [padTo, List.reverse_cons, List.append_assoc] ; omega
      · simpa [paddingRegs, readRegs] using hreg

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

theorem subtractionPorts_injective : Function.Injective subtractionPorts := by decide

abbrev subtractWideProgram : Program 8 5 13 where
  inputStack := 2
  outputStack := 3
  entry := 0
  code pc := SubexponentialSAT.ProgramLinking.relocateInstr id subtractionPorts id none
    (subtractProgram.code pc)

abbrev copyCandidateProgram : Program 8 5 8 :=
  SubexponentialSAT.StackRoutines.copyProgram 0 2 4 1 3

theorem copy_candidate (candidate modulus : List Bool) :
    SubexponentialSAT.StackRoutines.copyStacks (0 : Fin 5) 2
      (wideStacks candidate [] modulus []) =
      wideStacks candidate candidate modulus [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.copyStacks, wideStacks]

abbrev copyAndSubtractProgram : Program 8 5 21 :=
  SubexponentialSAT.ProgramLinking.link copyCandidateProgram subtractWideProgram

/-- Select the saved candidate on borrow; otherwise reverse the difference.
The unused candidate and all work stacks are consumed in either branch. -/
abbrev selectDifferenceProgram : Program 8 5 10 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.branch 0 1 3,
    .pop 3 1 3 2, .branch 3 1 9,
    .pop 0 1 3 4, .branch 3 3 5,
    .pop 3 1 3 6, .branch 3 7 9, .push 0 1 5,
    .halt, .halt]

theorem clear_difference (candidate difference : List Bool) :
    SubexponentialSAT.StackRoutines.clearStacks (3 : Fin 5)
      (wideStacks candidate [] [] difference) =
      wideStacks candidate [] [] [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.clearStacks, wideStacks]

theorem clear_candidate (candidate difference : List Bool) :
    SubexponentialSAT.StackRoutines.clearStacks (0 : Fin 5)
      (wideStacks candidate [] [] difference) =
      wideStacks [] [] [] difference := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.clearStacks, wideStacks]

theorem transfer_difference (difference : List Bool) :
    SubexponentialSAT.StackRoutines.transferStacks (3 : Fin 5) 0
      (wideStacks [] [] [] difference) =
      wideStacks difference.reverse [] [] [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.transferStacks, wideStacks]

abbrev conditionalSubtractProgram : Program 8 5 31 :=
  SubexponentialSAT.ProgramLinking.link copyAndSubtractProgram selectDifferenceProgram

end SubexponentialSAT.ModularPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularDivisionPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite binary long-division program

The modulus and dividend are Boolean words stored on stacks. Every routine below
has a fixed finite table, independently of the lengths and values of these words.
-/

namespace SubexponentialSAT.ModularDivisionPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms
open SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines

theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

theorem paddingPorts_injective : Function.Injective paddingPorts := by decide
theorem conditionalPorts_injective : Function.Injective conditionalPorts := by decide

abbrev paddingWideProgram : Program 8 7 5 :=
  liftProgram paddingProgram id paddingPorts

abbrev conditionalWideProgram : Program 8 7 31 :=
  liftProgram conditionalSubtractProgram id conditionalPorts

abbrev copyShapeProgram : Program 8 7 8 := copyProgram 0 2 4 1 3
abbrev copyModulusProgram : Program 8 7 8 := copyProgram 5 1 4 1 3
abbrev movePaddingProgram : Program 8 7 4 := transferProgram 3 1 1 3

theorem copy_shape (candidate modulus input : List Bool) :
    copyStacks (0 : Fin 7) 2 (resting candidate modulus input) =
      seven candidate modulus input [] candidate [] [] := by
  funext i
  fin_cases i <;> simp [copyStacks, resting, seven]

theorem copy_modulus (candidate modulus input : List Bool) :
    copyStacks (5 : Fin 7) 1 (seven candidate modulus input [] candidate [] []) =
      seven candidate modulus input modulus candidate [] [] := by
  funext i
  fin_cases i <;> simp [copyStacks, seven]

theorem move_padding (candidate modulus input padded : List Bool) :
    transferStacks (3 : Fin 7) 1 (seven candidate modulus input [] [] padded.reverse []) =
      seven candidate modulus input padded [] [] [] := by
  funext i
  fin_cases i <;> simp [transferStacks, seven]

abbrev preparePaddingProgram : Program 8 7 25 :=
  link (link (link copyShapeProgram copyModulusProgram) paddingWideProgram) movePaddingProgram

abbrev resetBorrowProgram : Program 8 7 2 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.set 0 false 1, .halt]

abbrev reductionStepProgram : Program 8 7 58 :=
  link (link preparePaddingProgram resetBorrowProgram) conditionalWideProgram

/-- Four control instructions followed by the fixed reduction-step table.
The step table's halt becomes a jump back to the input loop. -/
def divisionLoopProgram : Program 8 7 62 where
  inputStack := 6
  outputStack := 0
  entry := 0
  code := Fin.addCases
    (motive := fun _ : Fin (4 + 58) => Instr 8 7 62)
    (![.pop 6 1 3 1, .branch 3 2 3, .push 0 1 4, .halt] : Fin 4 → Instr 8 7 62)
    (fun pc : Fin 58 =>
      relocateInstr id id (Fin.natAdd 4) (some 0) (reductionStepProgram.code pc))

@[simp] theorem loop_code_0 : divisionLoopProgram.code 0 = .pop 6 1 3 1 := rfl
@[simp] theorem loop_code_1 : divisionLoopProgram.code 1 = .branch 3 2 3 := rfl
@[simp] theorem loop_code_2 : divisionLoopProgram.code 2 = .push 0 1 4 := rfl
@[simp] theorem loop_code_3 : divisionLoopProgram.code 3 = .halt := rfl

theorem update_input (candidate modulus input next : List Bool) :
    Function.update (resting candidate modulus input) 6 next =
      resting candidate modulus next := by
  funext i
  fin_cases i <;> simp [resting, seven]

theorem update_candidate (candidate modulus input next : List Bool) :
    Function.update (resting candidate modulus input) 0 next =
      resting next modulus input := by
  funext i
  fin_cases i <;> simp [resting, seven]

theorem divisionLoop_head (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (b : Bool) :
    Trace divisionLoopProgram 3
      ⟨some 0, regs, resting candidate modulus (b :: input)⟩
      ⟨some 4, readRegs regs 1 3 (some b), resting (b :: candidate) modulus input⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr,
    readRegs, update_input, update_candidate, Function.update_apply]

theorem divisionLoop_exit (regs : Fin 8 → Bool) (candidate modulus : List Bool) :
    Trace divisionLoopProgram 3
      ⟨some 0, regs, resting candidate modulus []⟩
      ⟨none, readRegs regs 1 3 none, resting candidate modulus []⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr,
    readRegs, update_input, Function.update_apply]

abbrev copyInitialModulusProgram : Program 8 7 8 := copyProgram 5 2 4 1 3
abbrev moveInitialRemainderProgram : Program 8 7 4 := transferProgram 3 0 1 3
abbrev reverseInputProgram : Program 8 7 10 := reverseProgram 6 1 2 1 3

abbrev initializeProgram : Program 8 7 27 :=
  link (link (link copyInitialModulusProgram paddingWideProgram) moveInitialRemainderProgram)
    reverseInputProgram

/-- One fixed finite program computing binary remainder. -/
abbrev remainderProgram : Program 8 7 89 := link initializeProgram divisionLoopProgram

end SubexponentialSAT.ModularDivisionPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed Boolean-stack programs for arithmetic with a supplied binary modulus. -/

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

abbrev addWideProgram : Program 8 7 17 :=
  liftProgram SubexponentialSAT.BinaryPrograms.Add.littleEndianProgram id addPorts

abbrev firstMoveProgram : Program 8 7 4 := transferProgram 0 2 1 3
abbrev secondMoveProgram : Program 8 7 4 := transferProgram 2 6 1 3
abbrev moveSumProgram : Program 8 7 8 := link firstMoveProgram secondMoveProgram

abbrev addModProgram : Program 8 7 116 :=
  link (link (link resetBorrowProgram addWideProgram) moveSumProgram) remainderProgram


end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

/-! ## Restore a runtime-specified output width -/

open SubexponentialSAT.ModularPrograms

abbrev normalizationPrefixProgram : Program 8 8 5 :=
  liftProgram paddingProgram id normalizePorts

abbrev normalizationClearProgram : Program 8 8 3 := clearProgram 0 1 3
abbrev normalizationMoveProgram : Program 8 8 4 := transferProgram 2 0 1 3
abbrev normalizeProgram : Program 8 8 12 :=
  link (link normalizationPrefixProgram normalizationClearProgram) normalizationMoveProgram

abbrev shapeCopyProgram : Program 8 8 8 := copyProgram 0 7 3 1 3

abbrev canonicalProgram {l : ℕ} (p : Program 8 7 l) : Program 8 8 (8 + l + 12) :=
  link (link shapeCopyProgram (liftProgram p id sevenPorts)) normalizeProgram

abbrev wordAddProgram : Program 8 8 136 := canonicalProgram addModProgram

end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Streaming addition of serialized quartic coefficients

There are four calls to the actual modular-word machine. Width is supplied as
stack data. No instruction table is generated from a coefficient or its width.
-/

namespace SubexponentialSAT.SubexpFlatAdd

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 20

def state (regs : Fin 8 → Bool)
    (x y modulus left right width counter tmp packed : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  ⟨regs, «stacks» x y modulus left right width counter tmp packed frame⟩

abbrev addScalar : Cmd 8 20 :=
  .call (ProgramLinking.liftProgram ModularRingPrograms.wordAddProgram id scalarPorts)

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- One word from each flattened coefficient, followed by a real scalar add. -/
abbrev addOne : Cmd 8 20 :=
  .seq (takeWord 10 11 12 8 0 0 1)
    (.seq (takeWord 10 11 12 9 1 0 1)
      (.seq addScalar (.call (StackRoutines.transferProgram 0 13 (0 : Fin 8) 1))))

end SubexponentialSAT.SubexpFlatAdd

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DensePolynomialPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed streaming program for dense polynomial addition

Quartic coefficients are four consecutive fixed-width base words. The loop
uses the actual modular-word addition program and tests the input stacks.
Its instruction table is independent of the array lengths and the width.
-/

namespace SubexponentialSAT.DensePolynomialPrograms

open BitProgram StructuredCalls DensePolynomialLoop
open SubexpLiftRing SubexpQuarticRing

/-- The fixed program calls the same fixed modular-word routine at each step. -/
abbrev addCmd : Cmd 8 20 := DensePolynomialLoop.addCmd SubexpFlatAdd.addOne

end SubexponentialSAT.DensePolynomialPrograms

end OAI.Algorithms
end


