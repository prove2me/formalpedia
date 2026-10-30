-- Prove2me | Definitions.Def_OAIQ081S034
-- name    : OAIQ081S034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:31:03.06349+00:00
-- url     : https://prove2.me/theorems/e824964b-b349-4bed-89e5-08ba361a553c
-- title:
--   Definitions bundle OAIQ081S034 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 65 declarations of OpenAI's Lean: 33 definitions and 32 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.compareRoundRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatZeros`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.iterate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.last`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.normalizedWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.pulledConstraints`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.readIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.copySource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.encodeIndices`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.popDecoded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.normalizedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.workCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.firstProductPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.productSumPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.secondProductPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.AvoidsAtom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.AvoidsBase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.AvoidsCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.AvoidsInstr`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.AvoidsProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries.pairPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.addCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.addNegativePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.addPositivePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairEncoding`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read.program`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramCompare`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramMath`, `SubexponentialSAT_SqrtLog_LayoutExactBuckets`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic`, `SubexponentialSAT_SqrtLog_LayoutHeadPullback`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutProgramNormalize`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutPullback`, `SubexponentialSAT_SqrtLog_LayoutScalarEmitter`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts`, `SubexponentialSAT_SqrtLog_PackingProgramArithmetic`, `SubexponentialSAT_SqrtLog_ProgramTapeReplay`, `SubexponentialSAT_SqrtLog_ProgramTapeReplayFootprint`, `SubexponentialSAT_SqrtLog_RowSelectionProgramAdd`, `SubexponentialSAT_SqrtLog_RowSelectionProgramEntriesEmit`, `SubexponentialSAT_SqrtLog_RowSelectionProgramParser`, `SubexponentialSAT_SqrtLog_RowSelectionProgramTupleCheckRead`, `SubexponentialSAT_StackEncoding`, `SubexponentialSAT_SubexpTupleRefinement`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S006` and `OAIQ081S011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S051`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S058` and `OAIQ081S063`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S011

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
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

theorem encodeDataStack_eq_nil_iff {α : Type u} (c : BlockCode α) (s : List α) :
    encodeDataStack c s = [] ↔ s = [] := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    rw [length_encodeDataStack, List.length_nil] at hlen
    have hs : s.length = 0 := (Nat.mul_eq_zero.mp hlen).resolve_right
      (Nat.ne_of_gt c.width_pos)
    exact List.length_eq_zero_iff.mp hs
  · rintro rfl
    rfl

theorem encodeDataStack_injective {α : Type u} (c : BlockCode α) :
    Function.Injective (encodeDataStack c) := by
  intro s
  induction s with
  | nil =>
      intro t ht
      exact ((encodeDataStack_eq_nil_iff c t).mp ht.symm).symm
  | cons a s ih =>
      intro t ht
      cases t with
      | nil =>
          exact (List.cons_ne_nil a s ((encodeDataStack_eq_nil_iff c (a :: s)).mp ht)).elim
      | cons b t =>
          have hab : c.block a = c.block b := by
            simpa only [take_width_cons] using congrArg (List.take c.width) ht
          have hab' := c.injective_block hab
          subst b
          have hst : encodeDataStack c s = encodeDataStack c t := by
            simpa only [drop_width_cons] using congrArg (List.drop c.width) ht
          exact congrArg (List.cons a) (ih hst)

end SubexponentialSAT.StackEncoding

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

theorem encodeTuple_injective {A : Type*} (code : StackEncoding.BlockCode A) (n : ℕ) :
    Function.Injective (encodeTuple code (n := n)) := by
  intro v w h
  exact List.ofFn_injective (StackEncoding.encodeDataStack_injective code h)

theorem encodeTuple_append {A : Type*} (code : StackEncoding.BlockCode A)
    {d e : ℕ} (a : Fin d → A) (b : Fin e → A) :
    encodeTuple code (Fin.append a b) = encodeTuple code a ++ encodeTuple code b := by
  simp only [encodeTuple, List.ofFn_fin_append, StackEncoding.encodeDataStack_append]

theorem encodePair_injective {A : Type*} (code : StackEncoding.BlockCode A) (d e : ℕ) :
    Function.Injective (fun ab : (Fin d → A) × (Fin e → A) =>
      encodeTuple code ab.1 ++ encodeTuple code ab.2) := by
  intro a b hab
  have heq : Fin.append a.1 a.2 = Fin.append b.1 b.2 :=
    encodeTuple_injective code (d + e) (by simpa only [encodeTuple_append] using hab)
  apply Prod.ext
  · funext i
    simpa only [Fin.append_left] using congrFun heq (Fin.castAdd e i)
  · funext i
    simpa only [Fin.append_right] using congrFun heq (Fin.natAdd d i)

end SubexponentialSAT.SubexpTupleRefinement

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

def compareRoundRegs (regs : Fin 4 → Bool) (a b : Bool) : Fin 4 → Bool :=
  let r := readRegs (readRegs regs 0 1 (some a)) 2 1 (some b)
  let r := Function.update r 0 (!(a ^^ b))
  Function.update r 3 (regs 3 && !(a ^^ b))

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

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

open SubexponentialSAT.BinaryArithmetic

def scan : List Bool → List (List Bool) → List (List Bool)
  | _, [] => []
  | prior, old :: rest => add prior old :: scan old rest

def last : List Bool → List (List Bool) → List Bool
  | prior, [] => prior
  | _, old :: rest => last old rest

@[simp] theorem scan_length (prior : List Bool) (xs : List (List Bool)) :
    (scan prior xs).length = xs.length := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp [scan, ih]

def iterate : ℕ → List (List Bool) → List (List Bool)
  | 0, xs => xs
  | h + 1, xs => iterate h (scan [] xs)

@[simp] theorem iterate_length (h : ℕ) (xs : List (List Bool)) :
    (iterate h xs).length = xs.length := by
  induction h generalizing xs with
  | zero => rfl
  | succ h ih => simp [iterate, ih]

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-width normalization for signed-component matrix words. This uses
only the existing padding, clear and transfer bit programs. In particular,
normalizing a component never invokes modular integer arithmetic. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularArithmetic SubexponentialSAT.StackRoutines
open SubexponentialSAT.ModularRingPrograms

variable {s : ℕ}

def normalizedStacks (ports : Fin 8 ↪ Fin s) (d : State 8 s) : Stacks (Fin s) :=
  Function.update (Function.update d.stacks (ports 7) []) (ports 0)
    (padTo (d.stacks (ports 7)) (d.stacks (ports 0)))

@[simp] theorem normalized_length (ports : Fin 8 ↪ Fin s) (d : State 8 s) :
    ((normalizedStacks ports d) (ports 0)).length = (d.stacks (ports 7)).length := by
  simp [normalizedStacks, padTo_length]

end SubexponentialSAT.SqrtLog.LayoutProgram

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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

def firstProductPorts : Ports 12 where
  left := 0
  right := 1
  out := 4
  work := arithmeticWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

def secondProductPorts : Ports 12 where
  left := 2
  right := 3
  out := 5
  work := arithmeticWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

def productSumPorts : Ports 12 where
  left := 4
  right := 5
  out := 6
  work := arithmeticWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.PackingProgram

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

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls
open SubexponentialSAT.BinaryArithmetic

def addPositivePorts : Ports 15 where
  left := 0
  right := 2
  out := 6
  work := addWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

def addNegativePorts : Ports 15 where
  left := 1
  right := 3
  out := 9
  work := addWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

abbrev addCommand : Cmd 8 15 := .seq (addAt addPositivePorts) (addAt addNegativePorts)

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit framed input parsing for streams of signed binary word pairs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def pairLength (w : WordPair) : ℕ := w.1.length+w.2.length

def pairEncoding : List WordPair → List Bool
  | [] => [false]
  | a :: rest => true :: (Encoding.frame a.1.reverse ++
      (Encoding.frame a.2.reverse ++ pairEncoding rest))

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

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev workCall (c : Cmd 8 16) : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram (compiled c 0 1) id workPorts)

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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def pairPrefix (p n : List Bool) : List Bool :=
  true :: (Encoding.frame p.reverse ++ Encoding.frame n.reverse)

@[simp] theorem pairPrefix_cons (p : WordPair) (xs : List WordPair) :
    pairPrefix p.1 p.2 ++ pairEncoding xs = pairEncoding (p::xs) := by
  simp [pairPrefix, pairEncoding, List.append_assoc]

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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Code := Cmd 8 7

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

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

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def flatWords (width : List Bool) (xs : List (List Bool)) : List Bool :=
  xs.flatMap (ModularArithmetic.padTo width)

def flatZeros (width : List Bool) (xs : List (List Bool)) : List Bool :=
  xs.flatMap (fun _ => ModularArithmetic.padTo width [])

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

@[simp] theorem flatWords_length (width : List Bool) (xs : List (List Bool)) :
    (flatWords width xs).length = xs.length*width.length := by
  induction xs with
  | nil => simp [flatWords]
  | cons x xs ih =>
    change (ModularArithmetic.padTo width x ++ flatWords width xs).length = _
    simp only [List.length_append,ModularArithmetic.padTo_length,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

@[simp] theorem flatZeros_length (width : List Bool) (xs : List (List Bool)) :
    (flatZeros width xs).length = xs.length*width.length := by
  induction xs with
  | nil => simp [flatZeros]
  | cons x xs ih =>
    change (ModularArithmetic.padTo width [] ++ flatZeros width xs).length = _
    simp only [List.length_append,ModularArithmetic.padTo_length,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Value and shape contracts for the generic adapter and binomial row. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BinaryArithmetic

def normalizedWords (width : List Bool) (xs : List (List Bool)) : List (List Bool) :=
  xs.map (ModularArithmetic.padTo width)

@[simp] theorem normalizedWords_length (width : List Bool) (xs : List (List Bool)) :
    (normalizedWords width xs).length = xs.length := by simp [normalizedWords]

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutPullback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
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

section Ring

variable [CommRing R]

theorem row_dot (owner : I → V) (a : I → R) (x : V → R) :
    (∑ v, row owner a v * x v) = ∑ i, a i * duplicate owner x i := by
  classical
  simp only [row, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [duplicate]

omit [Fintype V] in
theorem row_map {S : Type*} [CommRing S] (f : R →+* S)
    (owner : I → V) (a : I → R) (v : V) :
    f (row owner a v) = row owner (fun i => f (a i)) v := by
  simp only [row, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

omit [Fintype V] in
theorem row_single [DecidableEq I] (owner : I → V) (i : I) (v : V) :
    row owner (Pi.single i (1 : R)) v = if v = owner i then 1 else 0 := by
  classical
  unfold row
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro j _ hji
    simp [ hji]
  · simp

end Ring

section Polynomial

variable [CommRing R]

omit [Fintype V] in
theorem row_eval (owner : I → V) (a : I → Polynomial R) (v : V) (z : R) :
    (row owner a v).eval z = row owner (fun i => (a i).eval z) v := by
  exact row_map (Polynomial.evalRingHom z) owner a v

omit [Fintype V] in
theorem row_origin [DecidableEq I] (owner : I → V)
    (a : I → Polynomial R) (i : I)
    (ha : ∀ j, (a j).eval 0 = (Pi.single i (1 : R) : I → R) j) (v : V) :
    (row owner a v).eval 0 = if v = owner i then 1 else 0 := by
  rw [row_eval]
  simp_rw [ha]
  exact row_single owner i v

omit [Fintype V] in
theorem row_degree (owner : I → V) (a : I → Polynomial R) (d : ℕ)
    (ha : ∀ i, (a i).natDegree ≤ d) (v : V) :
    (row owner a v).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  by_cases hi : owner i = v
  · simpa [hi] using ha i
  · simp [hi]

end Polynomial

end SubexponentialSAT.SqrtLog.LayoutPullback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutExactBuckets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
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

section Pullback

variable {I : Type*} [Fintype I] [DecidableEq V]

def pulledConstraints (owner : I → V) (C : J → I → ℤ) : J → V → ℤ :=
  fun j => row owner (C j)

theorem signature_pullback (owner : I → V) (C : J → I → ℤ)
    (x : V → ℤ) (j : J) :
    signature (pulledConstraints owner C) x j =
      signature C (duplicate owner x) j :=
  row_dot owner (C j) x

theorem value_pullback (owner : I → V) (a : I → R) (x : V → ℤ) :
    value (row owner a) x = value a (duplicate owner x) := by
  exact row_dot owner a (fun v => (x v : R))

theorem killsIntegerKernel_pullback (owner : I → V)
    (C : J → I → ℤ) (a : I → R) (ha : KillsIntegerKernel a C) :
    KillsIntegerKernel (row owner a) (pulledConstraints owner C) := by
  intro z hz
  rw [value_pullback]
  apply ha
  intro j
  rw [← signature_pullback]
  exact hz j

end Pullback

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramTupleCheckRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The raw natural-field reader. Its stopping delimiter is consumed, while
all subsequent fields and all other bank are preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read
open SubexponentialSAT.BitProgram

abbrev program {r s : ℕ} (src dst : Fin s) (value present : Fin r) : Program r s 4 where
  inputStack := src
  outputStack := dst
  entry := 0
  code q := match q.val with
    | 0 => .pop src value present 1
    | 1 => .branch value 2 3
    | 2 => .push dst value 0
    | _ => .halt

end SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read

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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

abbrev Code := Cmd 16 256

def readIndex : Code := .call (RowSelectionProgramTupleCheck.Read.program 214 253 0 1)

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutHeadPullback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
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

omit [DecidableEq I] [Fintype V] [Fintype G] in
/-- Pulling a row back and then restricting its columns to a head is the
same operation as pulling back along the restricted owner map. -/
theorem row_restrict (owner : I → V) (copyHead : I → G) (head : V → G)
    (hhead : ∀ i, copyHead i = head (owner i)) (g : G)
    (a : I → O) (v : {v : V // head v = g}) :
    row owner a v.val =
      row (headOwner owner copyHead head hhead g) (fun i => a i.val) v := by
  classical
  unfold row
  simp only [headOwner, Subtype.ext_iff]
  rw [sum_subtype_ite (fun i => copyHead i = g)
    (fun i => if owner i = v.val then a i else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : owner i = v.val
  · have hg : copyHead i = g := (hhead i).trans (hi ▸ v.property)
    simp [hi, hg]
  · simp [hi]

end SubexponentialSAT.SqrtLog.LayoutHeadPullback

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
open SubexponentialSAT BitProgram StructuredCalls

abbrev Code := Cmd 5 11

def popDecoded : Code := .base (.atom (.pop 4 0 1))

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls

def encodeIndices (is : List ℕ) : List Bool := is.flatMap Encoding.encodeNat

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls

def copySource : Code := .call (StackRoutines.copyProgram 1 2 6 0 1)

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

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

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 32 640

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay under replacement of syntactically untouched tapes. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls

variable {r s l : ℕ}

/-- Even a peek is excluded: this is a no-read and no-write condition. -/
abbrev AvoidsInstr (H : Fin s → Prop) : Instr r s l → Prop
  | .push i _ _ => ¬ H i
  | .peek i _ _ _ => ¬ H i
  | .pop i _ _ _ => ¬ H i
  | _ => True

abbrev AvoidsProgram (H : Fin s → Prop) (p : Program r s l) : Prop :=
  ∀ q, AvoidsInstr H (p.code q)

abbrev AvoidsAtom (H : Fin s → Prop) : StructuredProgram.Atom r s → Prop
  | .push i _ => ¬ H i
  | .peek i _ _ => ¬ H i
  | .pop i _ _ => ¬ H i
  | _ => True

abbrev AvoidsBase (H : Fin s → Prop) : StructuredProgram.Cmd r s → Prop
  | .skip => True
  | .atom a => AvoidsAtom H a
  | .seq a b => AvoidsBase H a ∧ AvoidsBase H b
  | .ite _ a b => AvoidsBase H a ∧ AvoidsBase H b
  | .while _ a => AvoidsBase H a

abbrev AvoidsCmd (H : Fin s → Prop) : StructuredCalls.Cmd r s → Prop
  | .base a => AvoidsBase H a
  | .call p => AvoidsProgram H p
  | .seq a b => AvoidsCmd H a ∧ AvoidsCmd H b
  | .ite _ a b => AvoidsCmd H a ∧ AvoidsCmd H b
  | .while _ a => AvoidsCmd H a

theorem atom_instr_avoids (H : Fin s → Prop) (a : StructuredProgram.Atom r s)
    (ha : AvoidsAtom H a) (next : Fin l) : AvoidsInstr H (a.instr next) := by
  cases a <;> exact ha

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayFootprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compositional certificates for the tape footprint of compiled finite programs. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l R S L : ℕ}

theorem avoidsInstr_of_all (H : Fin s → Prop) (h : ∀ i, ¬ H i) (op : Instr r s l) :
    AvoidsInstr H op := by
  cases op <;> simp_all [AvoidsInstr]

theorem avoids_relocate (H : Fin S → Prop) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L) (ret : Option (Fin L))
    (op : Instr r s l) (h : AvoidsInstr (H ∘ stack) op) :
    AvoidsInstr H (ProgramLinking.relocateInstr register stack label ret op) := by
  cases op <;> cases ret <;> exact h

theorem avoids_liftProgram (H : Fin S → Prop) (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (h : AvoidsProgram (H ∘ stack) p) :
    AvoidsProgram H (ProgramLinking.liftProgram p register stack) := by
  intro q
  exact avoids_relocate H register stack id none (p.code q) (h q)

/-- No inspection of the local program is necessary when every mapped tape is visible. -/
theorem avoids_liftProgram_of_range (H : Fin S → Prop) (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (h : ∀ i, ¬ H (stack i)) :
    AvoidsProgram H (ProgramLinking.liftProgram p register stack) :=
  avoids_liftProgram H p register stack (fun q => avoidsInstr_of_all (H ∘ stack) h (p.code q))

theorem avoids_call_lift_of_range (H : Fin S → Prop) (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (h : ∀ i, ¬ H (stack i)) :
    AvoidsCmd H (.call (ProgramLinking.liftProgram p register stack)) :=
  avoids_liftProgram_of_range H p register stack h

theorem avoids_base_code (H : Fin s → Prop) (c : StructuredProgram.Cmd r s)
    (hc : AvoidsBase H c) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (q : StructuredProgram.Site c) :
    AvoidsInstr H (StructuredProgram.code c embed exit q) := by
  induction c generalizing exit with
  | skip => exact q.elim
  | atom a => exact atom_instr_avoids H a hc exit
  | seq first second ih₁ ih₂ =>
    cases q with
    | inl q => exact ih₁ hc.1 _ _ q
    | inr q => exact ih₂ hc.2 _ _ q
  | ite test yes no ih₁ ih₂ =>
    cases q with
    | none => trivial
    | some q =>
      cases q with
      | inl q => exact ih₁ hc.1 _ _ q
      | inr q => exact ih₂ hc.2 _ _ q
  | «while» test body ih =>
    cases q with
    | none => trivial
    | some q => exact ih hc _ _ q

theorem avoids_code (H : Fin s → Prop) (c : StructuredCalls.Cmd r s)
    (hc : AvoidsCmd H c) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (q : StructuredCalls.Site c) :
    AvoidsInstr H (StructuredCalls.code c embed exit q) := by
  induction c generalizing exit with
  | base c => exact avoids_base_code H c hc embed exit q
  | call p => exact avoids_relocate H id id embed (some exit) (p.code q) (hc q)
  | seq first second ih₁ ih₂ =>
    cases q with
    | inl q => exact ih₁ hc.1 _ _ q
    | inr q => exact ih₂ hc.2 _ _ q
  | ite test yes no ih₁ ih₂ =>
    cases q with
    | none => trivial
    | some q =>
      cases q with
      | inl q => exact ih₁ hc.1 _ _ q
      | inr q => exact ih₂ hc.2 _ _ q
  | «while» test body ih =>
    cases q with
    | none => trivial
    | some q => exact ih hc _ _ q

theorem avoids_compiled (H : Fin s → Prop) (c : StructuredCalls.Cmd r s)
    (hc : AvoidsCmd H c) (input output : Fin s) :
    AvoidsProgram H (StructuredCalls.compiled c input output) := by
  intro q
  simp only [StructuredCalls.compiled]
  split
  · trivial
  · exact avoids_code H c hc _ _ _

theorem avoids_copyProgram (H : Fin s → Prop) (src dst tmp : Fin s) (value present : Fin r)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H tmp) :
    AvoidsProgram H (StackRoutines.copyProgram src dst tmp value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd,ht]

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end


