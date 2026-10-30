-- Prove2me | Definitions.Def_OAIQ081S001
-- name    : OAIQ081S001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:22:24.410985+00:00
-- url     : https://prove2.me/theorems/0d6956bc-ace2-463a-8f3b-e26388697d91
-- title:
--   Definitions bundle OAIQ081S001 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 218 declarations of OpenAI's Lean: 86 definitions, 4 inductive types or structures and 128 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.BitEvent`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.add`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.addCarry`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.addEvents`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.addRun`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.carryAdd`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.carryAddRun`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.carryBit`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.carryEvents`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.fullAdderEvents`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.mul`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.mulEvents`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.mulRun`, `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.sumBit`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Add.stackState`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.accumulate`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.addLabel`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.addStack`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.stackState`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.fastCarry`, `OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.binomialCoefficients`, `OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.coefficients`, `OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.extendCoefficients`, `OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients`, `OAI.Algorithms.SubexponentialSAT.BinomialMatrix.B`, `OAI.Algorithms.SubexponentialSAT.BinomialMatrix.L`, `OAI.Algorithms.SubexponentialSAT.BinomialMatrix.U`, `OAI.Algorithms.SubexponentialSAT.BitProgram.selectedStackBits`, `OAI.Algorithms.SubexponentialSAT.BitProgram.stackBits`, `OAI.Algorithms.SubexponentialSAT.BlockPacking.CompleteBlocks`, `OAI.Algorithms.SubexponentialSAT.BlockPacking.CompleteBlocks.blockEmbedding`, `OAI.Algorithms.SubexponentialSAT.BlockPacking.CompleteBlocks.covered`, `OAI.Algorithms.SubexponentialSAT.BlockPacking.CompleteBlocks.leftovers`, `OAI.Algorithms.SubexponentialSAT.BlockPacking.count`, `OAI.Algorithms.SubexponentialSAT.BranchTree.Tree`, `OAI.Algorithms.SubexponentialSAT.BranchTree.Tree.nodeCount`, `OAI.Algorithms.SubexponentialSAT.BranchTree.Tree.paths`, `OAI.Algorithms.SubexponentialSAT.BranchTree.bPositions`, `OAI.Algorithms.SubexponentialSAT.BranchTree.pathCode`, `OAI.Algorithms.SubexponentialSAT.BranchTree.positionSets` and 50 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ArrayUpdatePrograms`, `SubexponentialSAT_BinaryArithmetic`, `SubexponentialSAT_BinaryPrograms`, `SubexponentialSAT_BinomialInterpolation`, `SubexponentialSAT_BinomialMatrix`, `SubexponentialSAT_BitProgramSelectedSpace`, `SubexponentialSAT_BitProgramSpace`, `SubexponentialSAT_BlockPacking`, `SubexponentialSAT_BranchTree`, `SubexponentialSAT_CeilingDivisionPrograms`, `SubexponentialSAT_ChunkPartition`, `SubexponentialSAT_Computation`, `SubexponentialSAT_ConditionalExpectation`, `SubexponentialSAT_CoreMaskProgram`, `SubexponentialSAT_CounterConversions`, `SubexponentialSAT_CounterForPrograms`, `SubexponentialSAT_CounterNormalizeProgram`, `SubexponentialSAT_CounterPrograms`, `SubexponentialSAT_DensePolynomialLoop`, `SubexponentialSAT_Encoding`, `SubexponentialSAT_ModularDivisionPrograms`, `SubexponentialSAT_ModularPrograms`, `SubexponentialSAT_ModularRingCore`, `SubexponentialSAT_ModularRingPrograms`, `SubexponentialSAT_ProgramLinking`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SubexpFlatAdd`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpQuarticRing`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S034`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S041`, `OAIQ081S042` and `OAIQ081S043`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT

section
-- module Solutions.OAIQ081_SAT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

@[simp] theorem frame_nil : frame [] = [false] := rfl

@[simp] theorem frame_cons (b : Bool) (bits : List Bool) :
    frame (b :: bits) = true :: b :: frame bits := rfl

/-- Decode one escape frame and return its unconsumed suffix. -/
def readFrame : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: [] => none
  | true :: b :: rest => do
      let (bs, tail) ← readFrame rest
      pure (b :: bs, tail)

@[simp] theorem readFrame_frame_append (bits rest : List Bool) :
    readFrame (frame bits ++ rest) = some (bits, rest) := by
  induction bits with
  | nil => simp [readFrame]
  | cons b bits ih => simp [readFrame, ih]

@[simp] theorem length_frame (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp
  | cons b bits ih => simp only [frame_cons, List.length_cons, ih]; omega

@[simp] theorem length_encodeList_nil {α : Type*} (enc : α → List Bool) :
    (encodeList enc []).length = 1 := rfl

@[simp] theorem length_encodeList_cons {α : Type*} (enc : α → List Bool)
    (a : α) (as : List α) :
    (encodeList enc (a :: as)).length =
      2 * (enc a).length + 2 + (encodeList enc as).length := by
  simp only [encodeList, List.length_cons, List.length_append, length_frame]
  omega

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Computation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured machine execution for the candidate SAT theorem

The definitions here use the transition semantics of mathlib's finite TM2 machines.
A bound is accompanied by an actual execution certificate; no cost is assigned to
an arbitrary mathematical function. TM2 counts executions of finite statements.
Each fixed statement contains finitely many primitive stack operations.
-/

namespace SubexponentialSAT.Computation

universe u v w

/-- A runtime bound means that a transition trace within that bound exists. -/
def RunsIn {α : Type u} (step : α → Option α) (bound : ℕ) (a b : α) : Prop :=
  ∃ n ≤ bound, Trace step n a b

namespace Trace

variable {α : Type u} {step : α → Option α} {n m : ℕ} {a b c : α}

theorem to_reaches (h : Trace step n a b) : StateTransition.Reaches step a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | cons hs ht ih => exact Relation.ReflTransGen.head hs ih

end Trace

namespace RunsIn

variable {α : Type u} {step : α → Option α} {n m : ℕ} {a b c : α}

theorem mono (h : RunsIn step n a b) (hn : n ≤ m) : RunsIn step m a b := by
  obtain ⟨t, ht, tr⟩ := h
  exact ⟨t, ht.trans hn, tr⟩

/-- A deterministic transition function cannot produce two different terminal results. -/
theorem terminal_unique (h₁ : RunsIn step n a b) (h₂ : RunsIn step m a c)
    (hb : step b = none) (hc : step c = none) : b = c := by
  obtain ⟨_, _, tr₁⟩ := h₁
  obtain ⟨_, _, tr₂⟩ := h₂
  exact Part.mem_unique
    (StateTransition.mem_eval.mpr ⟨tr₁.to_reaches, hb⟩)
    (StateTransition.mem_eval.mpr ⟨tr₂.to_reaches, hc⟩)

end RunsIn

end SubexponentialSAT.Computation

end OAI.Algorithms
end

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

variable {r s l R S L : ℕ}

theorem extend_update {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (g : α → γ) (base : β → γ)
    (a : α) (value : γ) :
    Function.extend f (Function.update g a value) base =
      Function.update (Function.extend f g base) (f a) value := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨x, rfl⟩ := hb
    simp only [hf.extend_apply, Function.update_apply, hf.eq_iff]
  · have hne : b ≠ f a := by
      intro h
      exact hb ⟨a, h.symm⟩
    simp only [Function.extend_apply' _ _ _ hb, Function.update_of_ne hne]

/-! ## Concrete disjoint linking -/

end SubexponentialSAT.ProgramLinking

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

theorem uniform_flatten_length (earlier : List (List Bool)) (width : ℕ)
    (hrows : ∀ row ∈ earlier, row.length = width) :
    earlier.flatten.length = earlier.length * width := by
  induction earlier with
  | nil => simp
  | cons row earlier ih =>
      have hr := hrows row (by simp)
      have ht : ∀ x ∈ earlier, x.length = width := by
        intro x hx
        exact hrows x (by simp [hx])
      simp only [List.flatten_cons, List.length_append, List.length_cons, hr, ih ht]
      ring

end SubexponentialSAT.ArrayUpdatePrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BinaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Arithmetic on explicit little-endian bit lists

Natural numbers occur in the specification and in theorems about trace lengths.
The data routines inspect Boolean values and list constructors only.
-/

namespace SubexponentialSAT.BinaryArithmetic

@[simp] theorem bitVal_false : bitVal false = 0 := rfl
@[simp] theorem bitVal_true : bitVal true = 1 := rfl
@[simp] theorem toNat_nil : toNat [] = 0 := rfl
@[simp] theorem toNat_cons (b : Bool) (bs : List Bool) :
    toNat (b :: bs) = bitVal b + 2 * toNat bs := rfl

def sumBit (a b c : Bool) : Bool := (a.xor b).xor c
def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem fullAdder_correct (a b c : Bool) :
    bitVal (sumBit a b c) + 2 * bitVal (carryBit a b c) =
      bitVal a + bitVal b + bitVal c := by
  cases a <;> cases b <;> cases c <;> decide

def carryAdd (c : Bool) : List Bool → List Bool
  | [] => if c then [true] else []
  | b :: bs => sumBit false b c :: carryAdd (carryBit false b c) bs

def addCarry (c : Bool) : List Bool → List Bool → List Bool
  | [], ys => carryAdd c ys
  | a :: xs, [] => sumBit a false c :: addCarry (carryBit a false c) xs []
  | a :: xs, b :: ys => sumBit a b c :: addCarry (carryBit a b c) xs ys

def add (xs ys : List Bool) : List Bool := addCarry false xs ys

theorem toNat_carryAdd (c : Bool) (ys : List Bool) :
    toNat (carryAdd c ys) = toNat ys + bitVal c := by
  induction ys generalizing c with
  | nil => cases c <;> simp [carryAdd, bitVal]
  | cons b bs ih =>
      simp only [carryAdd, toNat_cons, ih]
      have h := fullAdder_correct false b c
      simp only [bitVal_false, zero_add] at h
      omega

theorem toNat_addCarry (c : Bool) (xs ys : List Bool) :
    toNat (addCarry c xs ys) = toNat xs + toNat ys + bitVal c := by
  induction xs generalizing c ys with
  | nil => simp [addCarry, toNat_carryAdd]
  | cons a xs ih =>
      cases ys with
      | nil =>
          simp only [addCarry, toNat_cons, ih, toNat_nil]
          have h := fullAdder_correct a false c
          simp only [bitVal_false, add_zero] at h
          omega
      | cons b ys =>
          simp only [addCarry, toNat_cons, ih]
          have h := fullAdder_correct a b c
          omega

@[simp]
theorem toNat_add (xs ys : List Bool) :
    toNat (add xs ys) = toNat xs + toNat ys := by
  simp [add, toNat_addCarry]

theorem length_carryAdd (c : Bool) (ys : List Bool) :
    (carryAdd c ys).length ≤ ys.length + 1 := by
  induction ys generalizing c with
  | nil => cases c <;> simp [carryAdd]
  | cons b bs ih =>
      simp only [carryAdd, List.length_cons]
      have h := ih (carryBit false b c)
      omega

theorem length_addCarry (c : Bool) (xs ys : List Bool) :
    (addCarry c xs ys).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing c ys with
  | nil => simpa [addCarry] using length_carryAdd c ys
  | cons a xs ih =>
      cases ys with
      | nil =>
          simp only [addCarry, List.length_cons, List.length_nil, Nat.max_zero]
          have h := ih (carryBit a false c) []
          simp only [List.length_nil, Nat.max_zero] at h
          omega
      | cons b ys =>
          simp only [addCarry, List.length_cons]
          have h := ih (carryBit a b c) ys
          omega

theorem length_add (xs ys : List Bool) :
    (add xs ys).length ≤ max xs.length ys.length + 1 :=
  length_addCarry false xs ys

/-- Shift-and-add multiplication; no natural-number arithmetic is executed
by this data routine. Leading zero bits are allowed in its output. -/
def mul : List Bool → List Bool → List Bool
  | [], _ => []
  | b :: bs, ys =>
      let shifted := false :: mul bs ys
      if b then add ys shifted else shifted

@[simp]
theorem toNat_mul (xs ys : List Bool) :
    toNat (mul xs ys) = toNat xs * toNat ys := by
  induction xs with
  | nil => simp [mul]
  | cons b bs ih =>
      cases b <;> simp [mul, ih] <;> ring

/-- A deliberately loose output-width bound that needs no normalization. -/
theorem length_mul (xs ys : List Bool) :
    (mul xs ys).length ≤ 2 * xs.length + ys.length := by
  induction xs with
  | nil => simp [mul]
  | cons b bs ih =>
      cases b with
      | false => simp only [mul, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      | true =>
          simp only [mul, ↓reduceIte]
          have h := length_add ys (false :: mul bs ys)
          simp only [List.length_cons] at h ⊢
          omega

open SubexponentialSAT.Computation

/-! A fixed finite TM2 program implementing exactly those adder blocks. -/

/-! Source-level bit-event traces for the recursive multiplication routine.
The lists below record inspections, Boolean gates, and constructed list cells.
They are not asserted to be PrimitiveMachine execution traces. -/

inductive BitEvent
  | inspect
  | gate
  | push
  | control
  deriving DecidableEq

def fullAdderEvents : List BitEvent :=
  [.gate, .gate, .gate, .gate, .gate, .gate, .gate]

def carryEvents (c : Bool) : List Bool → List BitEvent
  | [] => if c then [.inspect, .push] else [.inspect]
  | b :: bs => [.inspect] ++ fullAdderEvents ++ [.push] ++
      carryEvents (carryBit false b c) bs

def addEvents (c : Bool) : List Bool → List Bool → List BitEvent
  | [], ys => .inspect :: carryEvents c ys
  | a :: xs, [] => [.inspect, .inspect] ++ fullAdderEvents ++ [.push] ++
      addEvents (carryBit a false c) xs []
  | a :: xs, b :: ys => [.inspect, .inspect] ++ fullAdderEvents ++ [.push] ++
      addEvents (carryBit a b c) xs ys

theorem length_carryEvents (c : Bool) (ys : List Bool) :
    (carryEvents c ys).length ≤ 10 * (ys.length + 1) := by
  induction ys generalizing c with
  | nil => cases c <;> simp [carryEvents]
  | cons b bs ih =>
      simp only [carryEvents, List.length_append, List.length_cons, List.length_nil]
      have h := ih (carryBit false b c)
      change 1 + 7 + 1 + _ ≤ _
      omega

theorem length_addEvents (c : Bool) (xs ys : List Bool) :
    (addEvents c xs ys).length ≤ 12 * (max xs.length ys.length + 1) := by
  induction xs generalizing c ys with
  | nil =>
      simp only [addEvents, List.length_cons, List.length_nil, Nat.zero_max]
      have h := length_carryEvents c ys
      omega
  | cons a xs ih =>
      cases ys with
      | nil =>
          simp only [addEvents, List.length_append, List.length_cons, List.length_nil,
            Nat.max_zero]
          have h := ih (carryBit a false c) []
          simp only [List.length_nil, Nat.max_zero] at h
          change 2 + 7 + 1 + _ ≤ _
          omega
      | cons b ys =>
          simp only [addEvents, List.length_append, List.length_cons, List.length_nil]
          have h := ih (carryBit a b c) ys
          change 2 + 7 + 1 + _ ≤ _
          omega

def mulEvents : List Bool → List Bool → List BitEvent
  | [], _ => [.inspect]
  | b :: bs, ys =>
      [.inspect, .control] ++ mulEvents bs ys ++ [.push, .control] ++
        if b then addEvents false ys (false :: mul bs ys) else []

/-- Executable writer-style interpretation: result bits and primitive source
events are produced together, without using natural-number arithmetic. -/
def carryAddRun (c : Bool) : List Bool → List Bool × List BitEvent
  | [] => if c then ([true], [.inspect, .push]) else ([], [.inspect])
  | b :: bs =>
      let r := carryAddRun (carryBit false b c) bs
      (sumBit false b c :: r.1, [.inspect] ++ fullAdderEvents ++ [.push] ++ r.2)

def addRun (c : Bool) : List Bool → List Bool → List Bool × List BitEvent
  | [], ys =>
      let r := carryAddRun c ys
      (r.1, .inspect :: r.2)
  | a :: xs, [] =>
      let r := addRun (carryBit a false c) xs []
      (sumBit a false c :: r.1,
        [.inspect, .inspect] ++ fullAdderEvents ++ [.push] ++ r.2)
  | a :: xs, b :: ys =>
      let r := addRun (carryBit a b c) xs ys
      (sumBit a b c :: r.1,
        [.inspect, .inspect] ++ fullAdderEvents ++ [.push] ++ r.2)

def mulRun : List Bool → List Bool → List Bool × List BitEvent
  | [], _ => ([], [.inspect])
  | b :: bs, ys =>
      let r := mulRun bs ys
      if b then
        let s := addRun false ys (false :: r.1)
        (s.1, [.inspect, .control] ++ r.2 ++ [.push, .control] ++ s.2)
      else
        (false :: r.1, [.inspect, .control] ++ r.2 ++ [.push, .control])

theorem carryAddRun_eq (c : Bool) (ys : List Bool) :
    carryAddRun c ys = (carryAdd c ys, carryEvents c ys) := by
  induction ys generalizing c with
  | nil => cases c <;> rfl
  | cons b bs ih => simp [carryAddRun, carryAdd, carryEvents, ih]

theorem addRun_eq (c : Bool) (xs ys : List Bool) :
    addRun c xs ys = (addCarry c xs ys, addEvents c xs ys) := by
  induction xs generalizing c ys with
  | nil => simp [addRun, addCarry, addEvents, carryAddRun_eq]
  | cons a xs ih =>
      cases ys <;> simp [addRun, addCarry, addEvents, ih]

theorem mulRun_eq (xs ys : List Bool) :
    mulRun xs ys = (mul xs ys, mulEvents xs ys) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [mulRun, mul, mulEvents, ih, addRun_eq, add]

theorem length_mulEvents (xs ys : List Bool) :
    (mulEvents xs ys).length ≤ 40 * (xs.length + 1) * (xs.length + ys.length + 1) := by
  induction xs with
  | nil => simp [mulEvents]; omega
  | cons b bs ih =>
      have hw := length_mul bs ys
      cases b with
      | false =>
          simp only [mulEvents, Bool.false_eq_true, ↓reduceIte, List.length_append,
            List.length_cons, List.length_nil]
          nlinarith
      | true =>
          have ha := length_addEvents false ys (false :: mul bs ys)
          have hm : max ys.length (false :: mul bs ys).length ≤
              2 * bs.length + ys.length + 1 := by
            simp only [List.length_cons]
            omega
          simp only [mulEvents, ↓reduceIte, List.length_append,
            List.length_cons, List.length_nil]
          nlinarith

theorem addRun_correct_and_cost (c : Bool) (xs ys : List Bool) :
    toNat (addRun c xs ys).1 = toNat xs + toNat ys + bitVal c ∧
    (addRun c xs ys).2.length ≤ 12 * (max xs.length ys.length + 1) := by
  rw [addRun_eq]
  exact ⟨toNat_addCarry c xs ys, length_addEvents c xs ys⟩

theorem mulRun_correct_and_cost (xs ys : List Bool) :
    toNat (mulRun xs ys).1 = toNat xs * toNat ys ∧
    (mulRun xs ys).2.length ≤ 40 * (xs.length + 1) * (xs.length + ys.length + 1) := by
  rw [mulRun_eq]
  exact ⟨toNat_mul xs ys, length_mulEvents xs ys⟩

end SubexponentialSAT.BinaryArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BinaryPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control programs for binary arithmetic

Operands, their widths, and moduli are data. None of the programs in this file
have a control-state set depending on an operand length or numeric parameter.
-/

namespace SubexponentialSAT.BinaryPrograms

open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.Computation

/-- Carry generation using three gates after the shared input XOR. -/
def fastCarry (a b c : Bool) : Bool :=
  (a && b).xor ((a.xor b) && c)

theorem fastCarry_eq (a b c : Bool) : fastCarry a b c = carryBit a b c := by
  cases a <;> cases b <;> cases c <;> decide

namespace Add

def stackState (xs ys out : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then xs else if k = 1 then ys else out

@[simp] theorem stacks_zero (xs ys out : List Bool) : stackState xs ys out 0 = xs := rfl
@[simp] theorem stacks_one (xs ys out : List Bool) : stackState xs ys out 1 = ys := rfl
@[simp] theorem stacks_two (xs ys out : List Bool) : stackState xs ys out 2 = out := rfl

@[simp] theorem update_left (xs ys out next : List Bool) :
    Function.update (stackState xs ys out) 0 next = stackState next ys out := by
  funext k
  fin_cases k <;> simp [stackState]

@[simp] theorem update_right (xs ys out next : List Bool) :
    Function.update (stackState xs ys out) 1 next = stackState xs next out := by
  funext k
  fin_cases k <;> simp [stackState]

@[simp] theorem update_output (xs ys out next : List Bool) :
    Function.update (stackState xs ys out) 2 next = stackState xs ys next := by
  funext k
  fin_cases k <;> simp [stackState]

end Add

namespace Mul

/-- The accumulator specification matched by the fixed-control multiplier. -/
def accumulate : List Bool → List Bool → List Bool → List Bool
  | [], _, acc => acc
  | b :: bs, ys, acc =>
      accumulate bs (false :: ys) (if b then add acc ys else acc)

theorem accumulate_value (xs ys acc : List Bool) :
    BinaryArithmetic.toNat (accumulate xs ys acc) = BinaryArithmetic.toNat acc + BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys := by
  induction xs generalizing ys acc with
  | nil => simp [accumulate]
  | cons b bs ih =>
      cases b <;> simp [accumulate, ih] <;> ring

theorem accumulate_length (xs ys acc : List Bool) :
    (accumulate xs ys acc).length ≤ max acc.length ys.length + xs.length := by
  induction xs generalizing ys acc with
  | nil => simp [accumulate]
  | cons b bs ih =>
      have hi := ih (false :: ys) (if b then add acc ys else acc)
      cases b with
      | false =>
          simp only [accumulate, Bool.false_eq_true, ↓reduceIte, List.length_cons] at *
          omega
      | true =>
          have ha := length_add acc ys
          simp only [accumulate, ↓reduceIte, List.length_cons] at *
          omega

def stackState (xs ys acc cp tmp rev : List Bool) : Fin 6 → List Bool :=
  ![xs, ys, acc, cp, tmp, rev]

@[simp] theorem stack_0 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 0 = xs := rfl
@[simp] theorem stack_1 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 1 = ys := rfl
@[simp] theorem stack_2 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 2 = acc := rfl
@[simp] theorem stack_3 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 3 = cp := rfl
@[simp] theorem stack_4 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 4 = tmp := rfl
@[simp] theorem stack_5 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 5 = rev := rfl

@[simp] theorem update_0 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 0 next =
      stackState next ys acc cp tmp rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_1 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 1 next =
      stackState xs next acc cp tmp rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_2 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 2 next =
      stackState xs ys next cp tmp rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_3 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 3 next =
      stackState xs ys acc next tmp rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_4 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 4 next =
      stackState xs ys acc cp next rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_5 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 5 next =
      stackState xs ys acc cp tmp next := by
  funext k; fin_cases k <;> simp [stackState]

def addStack (k : Fin 3) : Fin 6 := ![2, 3, 5] k
def addLabel (k : Fin 13) : Fin 32 := ⟨k.val + 11, by omega⟩

theorem addStack_injective : Function.Injective addStack := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [addStack]

theorem extend_addStack (xs ys acc cp tmp rev : List Bool) :
    Function.extend addStack (Add.stackState acc cp rev) (stackState xs ys [] [] tmp []) =
      stackState xs ys acc cp tmp rev := by
  funext k
  fin_cases k
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨a, ha⟩; fin_cases a <;> simp [addStack] at ha
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨a, ha⟩; fin_cases a <;> simp [addStack] at ha
  · exact addStack_injective.extend_apply _ _ (0 : Fin 3)
  · exact addStack_injective.extend_apply _ _ (1 : Fin 3)
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨a, ha⟩; fin_cases a <;> simp [addStack] at ha
  · exact addStack_injective.extend_apply _ _ (2 : Fin 3)

end Mul

end SubexponentialSAT.BinaryPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BinomialMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Consecutive binomial matrices

The matrix with entries choose (A + d) j factors into a lower
unitriangular Pascal matrix and an upper unitriangular translation matrix.
The upper factor is explicitly zero below the diagonal: natural subtraction
alone would give the wrong entries there.

All identities are obtained by casting integer-valued binomial coefficients,
so the determinant calculation remains valid in arbitrary characteristic.
-/

namespace SubexponentialSAT.BinomialMatrix

open scoped BigOperators

/-- The consecutive-integer binomial evaluation matrix. -/
def B (K : Type*) [Semiring K] (A R : ℕ) : Matrix (Fin R) (Fin R) K :=
  fun d j => ((A + d.val).choose j.val : K)

/-- The lower unitriangular Pascal matrix. -/
def L (K : Type*) [Semiring K] (R : ℕ) : Matrix (Fin R) (Fin R) K :=
  fun d s => (d.val.choose s.val : K)

/-- The upper unitriangular translation matrix, with explicit zero extension. -/
def U (K : Type*) [Semiring K] (A R : ℕ) : Matrix (Fin R) (Fin R) K :=
  fun s j => if s.val ≤ j.val then (A.choose (j.val - s.val) : K) else 0

@[simp] theorem B_apply (K : Type*) [Semiring K] (A R : ℕ) (d j : Fin R) :
    B K A R d j = ((A + d.val).choose j.val : K) := rfl

@[simp] theorem L_apply (K : Type*) [Semiring K] (R : ℕ) (d s : Fin R) :
    L K R d s = (d.val.choose s.val : K) := rfl

@[simp] theorem U_apply (K : Type*) [Semiring K] (A R : ℕ) (s j : Fin R) :
    U K A R s j =
      if s.val ≤ j.val then (A.choose (j.val - s.val) : K) else 0 := rfl

/-- Vandermonde convolution, extended by zero to any range containing j. -/
theorem choose_add_sum (A d j R : ℕ) (hj : j < R) :
    (A + d).choose j =
      ∑ s ∈ Finset.range R, d.choose s *
        (if s ≤ j then A.choose (j - s) else 0) := by
  calc
    (A + d).choose j =
        ∑ s ∈ Finset.range (j + 1), d.choose s * A.choose (j - s) := by
      rw [Nat.add_comm A d, Nat.add_choose_eq]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun s t => d.choose s * A.choose t) j
    _ = ∑ s ∈ Finset.range (j + 1), d.choose s *
        (if s ≤ j then A.choose (j - s) else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hs))]
    _ = ∑ s ∈ Finset.range R, d.choose s *
        (if s ≤ j then A.choose (j - s) else 0) := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hj))
      intro s _ hs
      have hsj : ¬s ≤ j := fun h =>
        hs (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      simp [hsj]

/-- The factorization is valid already over an arbitrary semiring. -/
theorem factorization (K : Type*) [Semiring K] (A R : ℕ) :
    B K A R = L K R * U K A R := by
  ext d j
  change ((A + d.val).choose j.val : K) =
    ∑ s : Fin R, (d.val.choose s.val : K) *
      (if s.val ≤ j.val then (A.choose (j.val - s.val) : K) else 0)
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => (d.val.choose s : K) *
    (if s ≤ j.val then (A.choose (j.val - s) : K) else 0)) R]
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_zero] using
    congrArg (fun n : ℕ => (n : K)) (choose_add_sum A d.val j.val R j.isLt)

theorem L_lowerTriangular (K : Type*) [Semiring K] (R : ℕ) :
    (L K R).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have h : i.val < j.val := hij
  simp [L, Nat.choose_eq_zero_of_lt h]

theorem U_upperTriangular (K : Type*) [Semiring K] (A R : ℕ) :
    (U K A R).BlockTriangular id := by
  intro i j hij
  have h : ¬i.val ≤ j.val := Nat.not_le_of_lt hij
  simp [U, h]

@[simp] theorem det_L (K : Type*) [CommRing K] (R : ℕ) :
    (L K R).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (L_lowerTriangular K R)]
  simp [L]

@[simp] theorem det_U (K : Type*) [CommRing K] (A R : ℕ) :
    (U K A R).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (U_upperTriangular K A R)]
  simp [U]

/-- Consecutive binomial evaluation has determinant one in every
commutative ring, with no characteristic or size restriction. -/
@[simp] theorem det_B (K : Type*) [CommRing K] (A R : ℕ) :
    (B K A R).det = 1 := by
  rw [factorization, Matrix.det_mul, det_L, det_U, one_mul]

end SubexponentialSAT.BinomialMatrix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BinomialInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Interpolation at consecutive integer weights

The coefficient construction uses the inverse of an actual finite matrix.
It applies over any commutative ring whose evaluation matrix has unit determinant.
The binomial evaluation matrix has determinant one, including in small characteristic.
-/

namespace SubexponentialSAT.BinomialInterpolation

open scoped BigOperators
open Matrix

noncomputable section

variable {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The coefficients solving a square interpolation system. -/
def coefficients (M : Matrix n n K) (target : n → K) : n → K :=
  M⁻¹ *ᵥ target

/-- Inverting a matrix with unit determinant realizes any prescribed target. -/
theorem mulVec_coefficients (M : Matrix n n K) (hM : IsUnit M.det)
    (target : n → K) : M *ᵥ coefficients M target = target := by
  rw [coefficients, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM,
    Matrix.one_mulVec]

/-- The coefficient vector is the unique solution of the interpolation system. -/
theorem coefficients_unique (M : Matrix n n K) (hM : IsUnit M.det)
    (target c : n → K) (hc : M *ᵥ c = target) : c = coefficients M target := by
  calc
    c = M⁻¹ *ᵥ (M *ᵥ c) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
    _ = coefficients M target := by rw [hc, coefficients]

/-- The determinant-one binomial matrix is invertible in every characteristic. -/
theorem isUnit_det_binomial (A R : ℕ) :
    IsUnit (BinomialMatrix.B K A R).det := by
  rw [BinomialMatrix.det_B]
  exact isUnit_one

/-- Coefficients realizing a target on the consecutive integer weights
`A, ..., A + R - 1`. These are integer binomial evaluations, not ordinary
univariate evaluations at the residues of these weights. -/
def binomialCoefficients (A R : ℕ) (target : Fin R → K) : Fin R → K :=
  coefficients (BinomialMatrix.B K A R) target

theorem binomialCoefficients_spec (A R : ℕ) (target : Fin R → K) (d : Fin R) :
    ∑ j : Fin R, binomialCoefficients A R target j *
      ((A + d.val).choose j.val : K) = target d := by
  have h := congrFun
    (mulVec_coefficients (BinomialMatrix.B K A R) (isUnit_det_binomial A R) target) d
  simpa only [binomialCoefficients, Matrix.mulVec, dotProduct,
    BinomialMatrix.B_apply, mul_comm] using h

/-- Arbitrary target values admit a unique binomial-basis coefficient vector. -/
theorem existsUnique_binomial_interpolation (A R : ℕ) (target : Fin R → K) :
    ∃! c : Fin R → K, ∀ d : Fin R,
      ∑ j : Fin R, c j * ((A + d.val).choose j.val : K) = target d := by
  refine ⟨binomialCoefficients A R target, binomialCoefficients_spec A R target, ?_⟩
  intro c hc
  apply coefficients_unique (BinomialMatrix.B K A R) (isUnit_det_binomial A R) target c
  funext d
  simpa only [Matrix.mulVec, dotProduct, BinomialMatrix.B_apply, mul_comm] using hc d

/-- The coefficient vector used for the alternating target in equation (5.3). -/
def parityCoefficients (A R : ℕ) : Fin R → K :=
  binomialCoefficients A R (fun d => (-1 : K) ^ (A + d.val))

theorem parityCoefficients_spec (A R : ℕ) (d : Fin R) :
    ∑ j : Fin R, parityCoefficients (K := K) A R j *
      ((A + d.val).choose j.val : K) = (-1 : K) ^ (A + d.val) :=
  binomialCoefficients_spec A R (fun d => (-1 : K) ^ (A + d.val)) d

/-- Extend a finite coefficient vector by zero outside its specified range. -/
def extendCoefficients {R : ℕ} (c : Fin R → K) (j : ℕ) : K :=
  if h : j < R then c ⟨j, h⟩ else 0

@[simp] theorem extendCoefficients_fin {R : ℕ} (c : Fin R → K) (j : Fin R) :
    extendCoefficients c j.val = c j := by
  simp [extendCoefficients, j.isLt]

end

end SubexponentialSAT.BinomialInterpolation

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

def stackBits {s : ℕ} (stk : Fin s → List Bool) : ℕ :=
  ∑ k, (stk k).length

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

def selectedStackBits {s : ℕ} (ports : Finset (Fin s))
    (stk : Fin s → List Bool) : ℕ :=
  ∑ k ∈ ports, (stk k).length

theorem selectedStackBits_update_le {s : ℕ} (ports : Finset (Fin s))
    (stk : Fin s → List Bool) (k : Fin s) (word : List Bool)
    (hword : word.length ≤ (stk k).length + 1) :
    selectedStackBits ports (Function.update stk k word) ≤ selectedStackBits ports stk + 1 := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold selectedStackBits
  rw [lengths]
  by_cases hk : k ∈ ports
  · rw [Finset.sum_update_of_mem hk, Finset.sdiff_singleton_eq_erase]
    have hsum := Finset.sum_erase_add ports (fun i => (stk i).length) hk
    omega
  · rw [Finset.sum_update_of_notMem hk]
    omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BlockPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Packing complete type blocks

The squared-deviation bound and the threshold from Section 5.4 imply a lower
bound for every type count. Enumerating the finite fibers then constructs
pairwise disjoint complete blocks. The construction from supplied enumerations
is explicit; no running-time theorem is asserted here.
-/

namespace SubexponentialSAT.BlockPacking

open scoped BigOperators

/-- A collection of complete blocks is an injective placement of block/type pairs,
preserving the assigned type. This also allows factors to cross block boundaries. -/
structure CompleteBlocks {α τ : Type*} (label : α → τ) (b : ℕ) where
  embed : Fin b × τ ↪ α
  type_eq : ∀ (i : Fin b) (u : τ), label (embed (i, u)) = u

section FiniteFibers

variable {α τ : Type*} [Fintype α] [Fintype τ] [DecidableEq τ]

/-- The actual number of coordinates of a given type. -/
def count (label : α → τ) (u : τ) : ℕ :=
  Fintype.card {v : α // label v = u}

end FiniteFibers

namespace CompleteBlocks

variable {α τ : Type*} {label : α → τ} {b : ℕ}

/-- Embedding of the type universe into an individual complete block. -/
def blockEmbedding (P : CompleteBlocks label b) (i : Fin b) : τ ↪ α where
  toFun := fun u => P.embed (i, u)
  inj' := fun _ _ h => congrArg Prod.snd (P.embed.injective h)

variable [Fintype τ]

/-- All packed coordinates; coordinates outside this set are the leftovers. -/
def covered (P : CompleteBlocks label b) : Finset α :=
  Finset.univ.map P.embed

@[simp] theorem card_covered (P : CompleteBlocks label b) :
    P.covered.card = b * Fintype.card τ := by
  simp [covered, Fintype.card_prod]

variable [Fintype α] [DecidableEq α]

/-- Coordinates not assigned to any complete block. -/
def leftovers (P : CompleteBlocks label b) : Finset α :=
  Finset.univ \ P.covered

end CompleteBlocks

end SubexponentialSAT.BlockPacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BranchTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Counting binary branch-tree paths

False labels an A edge and true labels a B edge. A word is encoded injectively
by its length and the finite set of positions occupied by B. This proves the
finite counting step in Appendix A.3 without any analytic hypotheses.
-/

namespace SubexponentialSAT.BranchTree

open Finset
open scoped BigOperators

/-- The zero-based positions of B edges in an actual binary path. -/
def bPositions (p : List Bool) : Finset ℕ :=
  (range p.length).filter fun i => p[i]? = some true

@[simp] theorem mem_bPositions (p : List Bool) (i : ℕ) :
    i ∈ bPositions p ↔ i < p.length ∧ p[i]? = some true := by
  simp [bPositions]

/-- The concrete code used in the manuscript. -/
def pathCode (p : List Bool) : ℕ × Finset ℕ := (p.length, bPositions p)

/-- All possible B-position sets of size at most R in a D-position ambient set. -/
def positionSets (D R : ℕ) : Finset (Finset ℕ) :=
  (range (R + 1)).biUnion fun r => (range D).powersetCard r

/-- A finite rooted binary tree, with A as its left edge and B as its right edge. -/
inductive Tree where
  | leaf : Tree
  | branch : Tree → Tree → Tree

/-- All root-to-node paths, including the empty path to the root. -/
def Tree.paths : Tree → Finset (List Bool)
  | .leaf => {[]}
  | .branch A B => insert []
      ((A.paths.image (List.cons false)) ∪ (B.paths.image (List.cons true)))

/-- The number of actual nodes of this finite tree. -/
def Tree.nodeCount : Tree → ℕ
  | .leaf => 1
  | .branch A B => 1 + A.nodeCount + B.nodeCount

@[simp] theorem Tree.card_paths (t : Tree) : t.paths.card = t.nodeCount := by
  induction t with
  | leaf => simp [Tree.paths, Tree.nodeCount]
  | branch A B ihA ihB =>
    have hd : Disjoint (A.paths.image (List.cons false))
        (B.paths.image (List.cons true)) := by
      apply disjoint_left.mpr
      intro p hpA hpB
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hpA
      obtain ⟨b, hb, he⟩ := mem_image.mp hpB
      cases he
    have hAinj : Function.Injective (List.cons false : List Bool → List Bool) := by
      intro a b h
      exact List.cons.inj h |>.2
    have hBinj : Function.Injective (List.cons true : List Bool → List Bool) := by
      intro a b h
      exact List.cons.inj h |>.2
    simp only [Tree.paths, Tree.nodeCount]
    rw [Finset.card_insert_of_notMem (by simp), card_union_of_disjoint hd,
      card_image_of_injective _ hAinj, card_image_of_injective _ hBinj, ihA, ihB]
    omega

end SubexponentialSAT.BranchTree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ChunkPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit ceiling-based partition into Boolean chunks

For positive `ell`, the number of chunks is `(n + ell - 1) / ell`.
The `i`th chunk contains the consecutive indices starting at `i * ell` and
has size `min ell (n - i * ell)`. Quotient and remainder give an actual
equivalence between the original indices and chunk/offset pairs.
-/

namespace SubexponentialSAT.ChunkPartition

open scoped BigOperators

/-- The natural-number ceiling of `n / ell` for positive `ell`. -/
def count (n ell : ℕ) : ℕ := (n + ell - 1) / ell

end SubexponentialSAT.ChunkPartition

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

/-- The unsigned value of a little-endian Boolean stack. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_false_cons (bs : List Bool) : value (false :: bs) = 2 * value bs := by
  simp [value]
@[simp] theorem value_true_cons (bs : List Bool) : value (true :: bs) = 1 + 2 * value bs := rfl

/-- Compatibility with the arithmetic module's identical little-endian convention. -/
theorem value_eq_toNat (bs : List Bool) : value bs = BinaryArithmetic.toNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [value, BinaryArithmetic.toNat, BinaryArithmetic.bitVal, ih]

/-- The same finite carry/borrow control works in both directions.  `true` is
increment; `false` is decrement, whose value contract requires positive input. -/
def ripple (carry : Bool) : List Bool → List Bool
  | [] => [carry]
  | b :: bs => if b = carry then (!carry) :: ripple carry bs else carry :: bs

@[simp] theorem ripple_nil (carry : Bool) : ripple carry [] = [carry] := rfl

theorem value_increment (bs : List Bool) : value (ripple true bs) = value bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [ripple, value] at * <;> omega

theorem value_decrement {bs : List Bool} (h : 0 < value bs) :
    value (ripple false bs) + 1 = value bs := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
      cases b with
      | false =>
          have hb : 0 < value bs := by simpa using h
          have hi := ih hb
          simp [ripple, value] at *
          omega
      | true => simp [ripple, value]; omega

theorem ripple_length_le (carry : Bool) (bs : List Bool) :
    (ripple carry bs).length ≤ bs.length + 1 := by
  induction bs with
  | nil => simp [ripple]
  | cons b bs ih =>
      simp only [ripple, List.length_cons]
      split_ifs <;> simp_all only [List.length_cons] <;> omega

theorem decrement_length {bs : List Bool} (h : 0 < value bs) :
    (ripple false bs).length = bs.length := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
      cases b with
      | false =>
          have hb : 0 < value bs := by simpa using h
          simp [ripple, ih hb]
      | true => simp [ripple]

/-- A direct finite Boolean zero test, valid even for noncanonical encodings. -/
def isZero : List Bool → Bool
  | [] => true
  | b :: bs => (!b) && isZero bs

@[simp] theorem isZero_eq_true_iff (bs : List Bool) : isZero bs = true ↔ value bs = 0 := by
  induction bs with
  | nil => simp [isZero]
  | cons b bs ih => cases b <;> simp [isZero, value, ih]

theorem isZero_eq_false_iff (bs : List Bool) : isZero bs = false ↔ 0 < value bs := by
  rw [Bool.eq_false_iff]
  change ¬ (isZero bs = true) ↔ _
  rw [isZero_eq_true_iff]
  exact Nat.pos_iff_ne_zero.symm


open SubexponentialSAT.BitProgram

/-- Three fixed Boolean registers: current bit, presence bit, and an accumulator. -/
def counterRegs (b p z : Bool) : Fin 3 → Bool :=
  fun i => if i = 0 then b else if i = 1 then p else z

/-- The value stack and one scratch stack; neither stack is part of finite control. -/
def counterStacks (xs ys : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then xs else ys

@[simp] theorem counterRegs_zero (b p z : Bool) : counterRegs b p z 0 = b := rfl
@[simp] theorem counterRegs_one (b p z : Bool) : counterRegs b p z 1 = p := rfl
@[simp] theorem counterRegs_two (b p z : Bool) : counterRegs b p z 2 = z := rfl
@[simp] theorem counterStacks_zero (xs ys : List Bool) : counterStacks xs ys 0 = xs := rfl
@[simp] theorem counterStacks_one (xs ys : List Bool) : counterStacks xs ys 1 = ys := rfl

@[simp] theorem update_counterRegs_zero (b p z v : Bool) :
    Function.update (counterRegs b p z) 0 v = counterRegs v p z := by
  funext i
  fin_cases i <;> simp [counterRegs]

@[simp] theorem update_counterRegs_one (b p z v : Bool) :
    Function.update (counterRegs b p z) 1 v = counterRegs b v z := by
  funext i
  fin_cases i <;> simp [counterRegs]

@[simp] theorem update_counterRegs_two (b p z v : Bool) :
    Function.update (counterRegs b p z) 2 v = counterRegs b p v := by
  funext i
  fin_cases i <;> simp [counterRegs]

@[simp] theorem update_counterStacks_zero (xs ys vs : List Bool) :
    Function.update (counterStacks xs ys) 0 vs = counterStacks vs ys := by
  funext i
  fin_cases i <;> simp [counterStacks]

@[simp] theorem update_counterStacks_one (xs ys vs : List Bool) :
    Function.update (counterStacks xs ys) 1 vs = counterStacks xs vs := by
  funext i
  fin_cases i <;> simp [counterStacks]

/-- Exact instruction count, ending at the halt label before executing halt. -/
def rippleCost (c : Bool) : List Bool → ℕ
  | [] => 6
  | b :: bs => if b = c then rippleCost c bs + 8 else 7

theorem rippleCost_le (c : Bool) (xs : List Bool) :
    rippleCost c xs ≤ 8 * xs.length + 7 := by
  induction xs with
  | nil => simp [rippleCost]
  | cons a xs ih =>
      simp only [rippleCost, List.length_cons]
      split_ifs <;> omega


/-! ## Deriving a binary counter from an input list -/

/-- Input data, binary count, and increment scratch, all on Boolean stacks. -/
def lengthStacks (data count scratch : List Bool) : Fin 3 → List Bool :=
  fun i => if i = 0 then data else if i = 1 then count else scratch

@[simp] theorem lengthStacks_zero (a b c : List Bool) : lengthStacks a b c 0 = a := rfl
@[simp] theorem lengthStacks_one (a b c : List Bool) : lengthStacks a b c 1 = b := rfl
@[simp] theorem lengthStacks_two (a b c : List Bool) : lengthStacks a b c 2 = c := rfl

@[simp] theorem update_lengthStacks_zero (a b c d : List Bool) :
    Function.update (lengthStacks a b c) 0 d = lengthStacks d b c := by
  funext i
  fin_cases i <;> simp [lengthStacks]

def lengthLabel (i : Fin 11) : Fin 14 := ⟨2 + i.val, by omega⟩

theorem extend_lengthStacks (data count scratch : List Bool) :
    Function.extend (Fin.succ : Fin 2 → Fin 3) (counterStacks count scratch)
      (lengthStacks data [] []) = lengthStacks data count scratch := by
  funext i
  fin_cases i
  · have hn : ¬ ∃ j : Fin 2, j.succ = (0 : Fin 3) := by simp
    change Function.extend (Fin.succ : Fin 2 → Fin 3) (counterStacks count scratch)
      (lengthStacks data [] []) 0 = data
    rw [Function.extend_apply' _ _ _ hn]
    rfl
  · exact (Fin.succ_injective 2).extend_apply _ _ 0
  · exact (Fin.succ_injective 2).extend_apply _ _ 1

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

open SubexponentialSAT.BitProgram SubexponentialSAT.CounterPrograms

/-- Fixed ports, independent of the represented counter value. -/
structure Ports (R S : ℕ) where
  register : Fin 3 ↪ Fin R
  counter : Fin S
  scratch : Fin S
  counter_ne_scratch : counter ≠ scratch

variable {R S : ℕ}

def stackPorts (p : Ports R S) : Fin 2 ↪ Fin S where
  toFun i := if i = 0 then p.counter else p.scratch
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [p.counter_ne_scratch, Ne.symm p.counter_ne_scratch]

@[simp] theorem stackPorts_zero (p : Ports R S) : stackPorts p 0 = p.counter := rfl
@[simp] theorem stackPorts_one (p : Ports R S) : stackPorts p 1 = p.scratch := rfl

theorem extend_restrict {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ h => congrArg g h) g a
  · exact Function.extend_apply' _ _ _ h

/-- Sum of the successive callback budgets; a specification, not program data. -/
abbrev budgetSum (cost : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, fuel + 1 => cost start + budgetSum cost (start + 1) fuel


theorem budgetSum_le (cost : ℕ → ℕ) (start fuel bound : ℕ)
    (h : ∀ i, start ≤ i → i < start + fuel → cost i ≤ bound) :
    budgetSum cost start fuel ≤ fuel * bound := by
  induction fuel generalizing start with
  | zero => simp [budgetSum]
  | succ fuel ih =>
      have hs : cost start ≤ bound := h start le_rfl (by omega)
      have ht : budgetSum cost (start + 1) fuel ≤ fuel * bound :=
        ih (start + 1) (by intro i hlow hhigh; exact h i (by omega) (by omega))
      simpa [budgetSum, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hs ht

theorem budgetSum_le_mono (cost : ℕ → ℕ) (h : Monotone cost) (fuel : ℕ) :
    budgetSum cost 0 fuel ≤ fuel * cost fuel :=
  budgetSum_le cost 0 fuel (cost fuel) (fun _ _ hi => h (by omega))

theorem budgetSum_const (bound start fuel : ℕ) :
    budgetSum (fun _ => bound) start fuel = fuel * bound := by
  induction fuel generalizing start with
  | zero => simp [budgetSum]
  | succ fuel ih => simp [budgetSum, ih, Nat.succ_mul, Nat.add_comm]

end SubexponentialSAT.CounterForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CeilingDivisionPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Ceiling division by fixed finite bit programs

The rounding suffix tests the actual remainder word and increments the actual
quotient word precisely when that remainder is nonzero. Natural division is
used only in the semantic statement of the full routine.
-/

namespace SubexponentialSAT.CeilingDivisionPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.CounterPrograms

def registers : Fin 3 ↪ Fin 8 where
  toFun i := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

end SubexponentialSAT.CeilingDivisionPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ConditionalExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite conditional expectation by executable sequential search

An alphabet is given as an explicit nonempty list. With a duplicate-free list,
the averages below are uniform averages on words over that alphabet. No choice
oracle is used: `chooseMin` and `assign` are recursive finite algorithms.
-/

namespace SubexponentialSAT.ConditionalExpectation

open scoped BigOperators

variable {α : Type*}

/-- The arithmetic mean of a score on an explicitly enumerated alphabet. -/
def mean (alphabet : List α) (score : α → ℚ) : ℚ :=
  (alphabet.map score).sum / (alphabet.length : ℚ)

/-- Deterministic finite search; ties favor the first candidate. -/
def chooseMin (score : α → ℚ) (a : α) : List α → α
  | [] => a
  | b :: bs =>
      let c := chooseMin score b bs
      if score a ≤ score c then a else c

/-- Conditional uniform mean over all assignments of the remaining variables.
The list `fixed` records coordinates already fixed, in reverse order. -/
def conditionalMean (alphabet : List α) (objective : List α → ℚ) :
    ℕ → List α → ℚ
  | 0, fixed => objective fixed
  | n + 1, fixed =>
      mean alphabet (fun a => conditionalMean alphabet objective n (a :: fixed))

/-- The same executable search accepts a separately implemented conditional
mean evaluator. Its computation cost is not hidden in the correctness theorem. -/
def assignWithEvaluator (a : α) (tail : List α)
    (evaluate : ℕ → List α → ℚ) : ℕ → List α → List α
  | 0, fixed => fixed
  | n + 1, fixed =>
      let next := chooseMin (fun x => evaluate n (x :: fixed)) a tail
      assignWithEvaluator a tail evaluate n (next :: fixed)

end SubexponentialSAT.ConditionalExpectation

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

def select : List Bool → List (List Bool) → List (List Bool)
  | _, [] => []
  | mask, item :: rest =>
      if mask.headD false then item :: select mask.tail rest else select mask.tail rest

def framePrefix : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: framePrefix bs

def recordPrefix : List (List Bool) → List Bool
  | [] => []
  | item :: rest => true :: (Encoding.frame item ++ recordPrefix rest)

def regs (tag present keep bit : Bool) : Fin 4 → Bool := ![tag, present, keep, bit]
def stackData (source mask accum output : List Bool) : Fin 4 → List Bool :=
  ![source, mask, accum, output]

@[simp] theorem stackData_zero (s m a o : List Bool) : stackData s m a o 0 = s := rfl
@[simp] theorem stackData_one (s m a o : List Bool) : stackData s m a o 1 = m := rfl
@[simp] theorem stackData_two (s m a o : List Bool) : stackData s m a o 2 = a := rfl
@[simp] theorem stackData_three (s m a o : List Bool) : stackData s m a o 3 = o := rfl

@[simp] theorem update_regs_zero (t p k b x : Bool) :
    Function.update (regs t p k b) 0 x = regs x p k b := by
  funext j; fin_cases j <;> simp [regs]
@[simp] theorem update_regs_one (t p k b x : Bool) :
    Function.update (regs t p k b) 1 x = regs t x k b := by
  funext j; fin_cases j <;> simp [regs]
@[simp] theorem update_regs_two (t p k b x : Bool) :
    Function.update (regs t p k b) 2 x = regs t p x b := by
  funext j; fin_cases j <;> simp [regs]
@[simp] theorem update_regs_three (t p k b x : Bool) :
    Function.update (regs t p k b) 3 x = regs t p k x := by
  funext j; fin_cases j <;> simp [regs]

@[simp] theorem update_stacks_zero (s m a o x : List Bool) :
    Function.update (stackData s m a o) 0 x = stackData x m a o := by
  funext j; fin_cases j <;> simp [stackData]
@[simp] theorem update_stacks_one (s m a o x : List Bool) :
    Function.update (stackData s m a o) 1 x = stackData s x a o := by
  funext j; fin_cases j <;> simp [stackData]
@[simp] theorem update_stacks_two (s m a o x : List Bool) :
    Function.update (stackData s m a o) 2 x = stackData s m x o := by
  funext j; fin_cases j <;> simp [stackData]
@[simp] theorem update_stacks_three (s m a o x : List Bool) :
    Function.update (stackData s m a o) 3 x = stackData s m a x := by
  funext j; fin_cases j <;> simp [stackData]

def emitCost (keep : Bool) : ℕ := if keep then 2 else 1

def recordCost (records : List (List Bool)) : ℕ :=
  7 * (records.map List.length).sum + 9 * records.length + 1

def runtimeBound (records : List (List Bool)) : ℕ :=
  10 * (Encoding.encodeList id records).length + 10

end SubexponentialSAT.CoreMaskProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterConversions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual binary-to-unary conversion

The finite controller consumes a little-endian binary counter on stack 0.
Each positive iteration pushes one true bit onto stack 1. Stack 2 is counter
scratch. The cleanup empties the counter and resets every Boolean register.
The numeric value controls execution through stack instructions only.
-/

namespace SubexponentialSAT.CounterConversions

open BitProgram CounterPrograms CounterForPrograms

def zeroRegs : Fin 3 → Bool := fun _ => false

def coreBound (bits : List Bool) : ℕ :=
  2 * value bits + (value bits + 1) * (16 * bits.length + 16) + 2 * bits.length + 6

def runtimeBound (bits : List Bool) : ℕ := 32 * (value bits + 1) * (bits.length + 1)

theorem coreBound_le (bits : List Bool) : coreBound bits + 3 ≤ runtimeBound bits := by
  dsimp [coreBound, runtimeBound]
  nlinarith [Nat.zero_le (value bits * bits.length)]

end SubexponentialSAT.CounterConversions

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

/-- Consume leading zeroes and the first one of a most-significant-first word. -/
def trimTail : List Bool → List Bool
  | [] => []
  | false :: xs => trimTail xs
  | true :: xs => xs

/-! ## Consume a most-significant zero prefix and the leading one -/

/-! ## Concrete input reversal -/

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

open BitProgram CounterPrograms

def normalized (bits : List Bool) : List Bool :=
  (true :: SubexpParameterProgram.trimTail bits.reverse).reverse

def zeroRegs : Fin 3 → Bool := fun _ => false

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

open SubexponentialSAT.BinaryArithmetic

/-- The type stores the width invariant; its alphabet remains `Bool`. -/
abbrev Word (B : ℕ) := { xs : List Bool // xs.length = B }

end BinaryInstance

end SubexponentialSAT.SubexpQuarticRing

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

open BitProgram
open SubexpQuarticRing

def stackArray (x y modulus left right width counter tmp packed : List Bool)
    (frame : Fin 6 → List Bool) : Fin 20 → List Bool :=
  fun i => Fin.addCases (m := 14) (n := 6) (motive := fun _ => List Bool)
    (![x,y,[],[],[],modulus,[],[],left,right,width,counter,tmp,packed] : Fin 14 → List Bool) frame i

def flatten {B : ℕ} (xs : List (Word B)) : List Bool := (xs.map Subtype.val).flatten

@[simp] theorem flatten_length {B : ℕ} (xs : List (Word B)) :
    (flatten xs).length = xs.length * B := by
  induction xs with
  | nil => simp [flatten]
  | cons x xs ih =>
      change (x.val ++ flatten xs).length = (xs.length + 1) * B
      rw [List.length_append, x.property, ih]
      ring

variable {B : ℕ}

@[simp] theorem flatten_append {B : ℕ} (xs ys : List (Word B)) :
    flatten (xs ++ ys) = flatten xs ++ flatten ys := by simp [flatten]


end SubexponentialSAT.DensePolynomialLoop

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

open SubexponentialSAT.BitProgram

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

def subtractionPorts : Fin 3 → Fin 5 := ![2, 1, 3]

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

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularPrograms
open SubexponentialSAT.ProgramLinking

/-- Ports 5 and 6 hold the preserved modulus and unprocessed dividend.
Ports 1--4 are reusable work stacks. -/
abbrev seven (candidate modulus input work1 work2 work3 work4 : List Bool) :
    Fin 7 → List Bool := ![candidate, work1, work2, work3, work4, modulus, input]

abbrev resting (candidate modulus input : List Bool) : Fin 7 → List Bool :=
  seven candidate modulus input [] [] [] []

@[simp] theorem resting_candidate (candidate modulus input : List Bool) :
    resting candidate modulus input 0 = candidate := rfl

@[simp] theorem resting_input (candidate modulus input : List Bool) :
    resting candidate modulus input 6 = input := rfl

def paddingPorts : Fin 3 → Fin 7 := ![2, 1, 3]
def conditionalPorts : Fin 5 → Fin 7 := ![0, 1, 2, 3, 4]

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

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularDivisionPrograms

def scalarInput (xs ys modulus : List Bool) : Fin 7 → List Bool :=
  seven xs modulus [] ys [] [] []

def addPorts : Fin 3 → Fin 7 := ![0, 1, 2]


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

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularDivisionPrograms

/-! ## Restore a runtime-specified output width -/

open SubexponentialSAT.ModularPrograms

def extendSeven (base : Fin 7 → List Bool) (shape : List Bool) : Fin 8 → List Bool :=
  ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, shape]

def sevenPorts : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]
def normalizePorts : Fin 3 → Fin 8 := ![7, 0, 2]

end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

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

open OAI.Algorithms.SubexponentialSAT.BitProgram

namespace Filter

def emitReg : Fin 3 → Fin 16 := ![13, 14, 15]


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
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

open BitProgram
open SubexpQuarticRing

def «stacks» (x y modulus left right width counter tmp packed : List Bool)
    (frame : Fin 6 → List Bool) : Fin 20 → List Bool :=
  fun i => Fin.addCases (m := 14) (n := 6) (motive := fun _ => List Bool)
    (![x,y,[],[],[],modulus,[],[],left,right,width,counter,tmp,packed] :
      Fin 14 → List Bool) frame i

def scalarPorts : Fin 8 → Fin 20 := Fin.castAdd 12

theorem scalarPorts_injective : Function.Injective scalarPorts := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 20 => x.val) h

end SubexponentialSAT.SubexpFlatAdd

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

open BitProgram

def doneExit : Fin 20 := 18

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end


