-- Prove2me | Definitions.Def_OAIQ081S013
-- name    : OAIQ081S013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:23:49.087051+00:00
-- url     : https://prove2.me/theorems/1b5cac68-2de3-4a42-b714-77af4181bc11
-- title:
--   Definitions bundle OAIQ081S013 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 168 declarations of OpenAI's Lean: 116 definitions, 9 inductive types or structures and 43 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanupPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.comparePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emitterDestinations`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emitterPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emitterRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literalPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literalRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.lookupPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.lookupRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.lowPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.lowRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.mismatchPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.vectorPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.frameRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.frameStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.numeratorPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.numeratorRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.dimStacks`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.reverseRegisters`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.reverseStacks`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.reversedRegs`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.unary`, `OAI.Algorithms.SubexponentialSAT.Subexp.BlockZeroProgram.isZero`, `OAI.Algorithms.SubexponentialSAT.Subexp.BlockZeroProgram.skipCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram.callbackCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.arrayPort`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.emitRegs`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.emitStacks`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.equalityRegs`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.equalityStacks`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.lookupPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.reverseStacks`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.rowPort`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingAddressSemantics.addressRows`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.bucketPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.bucketRegs`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.countPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.merged`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.minimumPorts` and 85 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramSourceBank`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCore`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramPorts`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpRepresentedRows`, `SubexponentialSAT_SubexpVertexIndexProgram`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_BlockZeroProgram`, `SubexponentialSAT_Subexp_GatherProgram`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_PackingAddressSemantics`, `SubexponentialSAT_Subexp_PackingBucketCalls`, `SubexponentialSAT_Subexp_PackingBucketExecution`, `SubexponentialSAT_Subexp_PackingBucketFold`, `SubexponentialSAT_Subexp_PackingBucketTable`, `SubexponentialSAT_Subexp_PackingEntryEmitter`, `SubexponentialSAT_Subexp_PackingExtractionBlock`, `SubexponentialSAT_Subexp_PackingExtractionCallback`, `SubexponentialSAT_Subexp_PackingExtractionEmit`, `SubexponentialSAT_Subexp_PackingExtractionSemantics`, `SubexponentialSAT_Subexp_PackingExtractionState`, `SubexponentialSAT_Subexp_PackingFrameCount`, `SubexponentialSAT_Subexp_PackingFrameSkip`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PackingMetadata`, `SubexponentialSAT_Subexp_PackingOutputSemantics`, `SubexponentialSAT_Subexp_PackingPlumbing`, `SubexponentialSAT_Subexp_PackingProgram`, `SubexponentialSAT_Subexp_PackingProgramAuxiliary`, `SubexponentialSAT_Subexp_PackingProgramInput`, `SubexponentialSAT_Subexp_PackingProgramSupport`, `SubexponentialSAT_Subexp_PackingVertexLabels`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_SelectorOutput`, `SubexponentialSAT_Subexp_SelectorProgram`, `SubexponentialSAT_Subexp_UniversalRowEmitCall`, `SubexponentialSAT_Subexp_UniversalRowFactorLoop`, `SubexponentialSAT_Subexp_UniversalRowFactors`, `SubexponentialSAT_Subexp_UniversalRowGather`, `SubexponentialSAT_Subexp_UniversalRowGuard`, `SubexponentialSAT_Subexp_UniversalRowLoop`, `SubexponentialSAT_Subexp_UniversalRowMismatchProgram`, `SubexponentialSAT_Subexp_UniversalRowMismatchTypes`, `SubexponentialSAT_Subexp_UniversalRowProgram`, `SubexponentialSAT_Subexp_UniversalRowSourceBound`, `SubexponentialSAT_Subexp_UniversalRowTermFraming`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S041`, `OAIQ081S042` and `OAIQ081S043`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
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

/-! ## Fixed source-constructor control -/

def registerMap (i : Fin 2) : Fin 3 := Fin.castAdd 1 i
def pairMap (a b : Fin 8) (i : Fin 2) : Fin 8 := if i = 0 then a else b
def tripleMap (a b c : Fin 8) (i : Fin 3) : Fin 8 :=
  if i = 0 then a else if i = 1 then b else c

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-code lookup with fallback for local read plans

The table is a raw sequence of framed key/payload pairs. The query and table
are runtime bit strings. The program reuses the verified key comparison and
record parsing routines, retaining the first matching payload.
-/

namespace SubexponentialSAT.Subexp.SelectorProgram

theorem lookup_cons_eq (query value : List Bool) (rest : List (List Bool × List Bool)) :
    ((query, value) :: rest).lookup query = some value := by simp

theorem lookup_cons_ne (query key value : List Bool)
    (rest : List (List Bool × List Bool)) (h : key ≠ query) :
    ((key, value) :: rest).lookup query = rest.lookup query := by
  simp [List.lookup_cons, beq_false_of_ne (Ne.symm h)]

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The output boundary for the fixed first-match selector. A matching payload
is parsed onto the output port; an absent key copies the original query. -/

namespace SubexponentialSAT.Subexp.SelectorProgram

def materializeBudget (query : List Bool) : Option (List Bool) → ℕ
  | none => 7 * query.length + 6
  | some value => 6 * value.length + 5

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem lookup_graph_encoded {A B : Type*} [DecidableEq A]
    (xs : List A) (key : A → List Bool) (f : A → B)
    (hkey : Function.Injective key) (a : A) (ha : a ∈ xs) :
    (xs.map (fun x => (key x, f x))).lookup (key a) = some (f a) := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases h : a = x
    · subst x
      simp
    · have hk : key a ≠ key x := fun he => h (hkey he)
      simpa [List.lookup_cons, beq_false_of_ne hk] using
        ih (List.mem_of_ne_of_mem h ha)

theorem lookup_graph_encoded_none {A B : Type*} [DecidableEq A]
    (xs : List A) (key : A → List Bool) (f : A → B)
    (hkey : Function.Injective key) (a : A) :
    (xs.map (fun x => (key x, f x))).lookup (key a) = none ↔ a ∉ xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : a = x
    · subst x
      simp
    · have hk : key a ≠ key x := fun he => h (hkey he)
      simp [List.lookup_cons, beq_false_of_ne hk, h, ih]

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

def lowRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def lowStacks : Fin 6 → Fin 9 := Fin.castAdd 3

theorem lowRegs_injective : Function.Injective lowRegs := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)

theorem lowStacks_injective : Function.Injective lowStacks := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin 9 => x.val) h)

abbrev mergeRegs (base : Fin 8 → Bool) (localRegs : Fin 5 → Bool) : Fin 8 → Bool :=
  ![localRegs 0, localRegs 1, localRegs 2, localRegs 3, localRegs 4, base 5, base 6, base 7]

def selected (records : List (List Bool × List Bool)) (query : List Bool) : List Bool :=
  (records.lookup query).getD query

def mappedRecords (records : List (List Bool × List Bool)) (queries : List (List Bool)) :=
  (queries.map (selected records)).reverse

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingAddressSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The emitted storage-address table is the graph of the actual packed
coordinate order. Its lookups produce the existing reordering read plan. -/

namespace SubexponentialSAT.Subexp.PackingAddressSemantics

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

/-- The physical address emitter increments a unary counter once per key. -/
def addressRows (vertices : List (List Bool)) (start : ℕ) : List (List Bool × List Bool) :=
  vertices.zipWith (fun v i => (v, List.replicate i true))
    (List.range' start vertices.length)

@[simp] theorem addressRows_nil (start : ℕ) : addressRows [] start = [] := rfl

theorem addressRows_cons (v : List Bool) (vertices : List (List Bool)) (start : ℕ) :
    addressRows (v :: vertices) start =
      (v, List.replicate start true) :: addressRows vertices (start + 1) := by
  simp only [addressRows, List.length_cons, List.range'_succ, List.zipWith_cons_cons]

theorem addressRows_append (left right : List (List Bool)) (start : ℕ) :
    addressRows (left ++ right) start =
      addressRows left start ++ addressRows right (start + left.length) := by
  induction left generalizing start with
  | nil => simp
  | cons v left ih =>
    simp only [List.cons_append, addressRows_cons, ih, List.length_cons]
    simp only [ Nat.add_comm, Nat.add_left_comm]

@[simp] theorem addressRows_length (vertices : List (List Bool)) (start : ℕ) :
    (addressRows vertices start).length = vertices.length := by
  simp [addressRows]

end SubexponentialSAT.Subexp.PackingAddressSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgramSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact finite-port framing for the physical packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgramSupport

def stackPorts {s : ℕ} (h : s ≤ 48) : Fin s → Fin 48 := Fin.castLE h

theorem stackPorts_injective {s : ℕ} (h : s ≤ 48) : Function.Injective (stackPorts h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin 48 => x.val) hij)

end SubexponentialSAT.Subexp.PackingProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingPlumbing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Verified stack moves used between the fixed packing subroutines. -/

namespace SubexponentialSAT.Subexp.PackingPlumbing

open PackingProgramSupport

inductive Op where
  | copy (src dst tmp : Fin 48)
  | transfer (src dst : Fin 48)
  | clear (src : Fin 48)
  | push (dst : Fin 48) (bit : Bool)

/-- Two real transfers preserve the source word's order. -/
def move (src dst tmp : Fin 48) : List Op := [.transfer src tmp, .transfer tmp dst]

end SubexponentialSAT.Subexp.PackingPlumbing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpVertexIndexProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed generator for exactly the vertex indices below unary D. -/
namespace SubexponentialSAT.SubexpVertexIndexProgram

abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.SubexpVertexIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GatherProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program gathering runtime-selected rows

The packed assignment is on stack 0 and its unary row width on stack 3.
Stack 8 contains `ProgramEncoding.encodeRecords` of unary index words.
The program preserves the assignment and width and writes the selected rows,
in plan order, to stack 1. All widths and indices are stack data.
-/

namespace SubexponentialSAT.Subexp.GatherProgram

theorem row_decomposition (rows : List (List Bool)) (i : ℕ) (hi : i < rows.length) :
    rows.flatten = (rows.take i).flatten ++
      (rows.getD i [] ++ (rows.drop (i + 1)).flatten) := by
  have hs : rows.take i ++ rows.getD i [] :: rows.drop (i + 1) = rows := by
    rw [List.getD_eq_getElem rows [] hi, List.cons_getElem_drop_succ]
    exact List.take_append_drop i rows
  simpa only [List.flatten_append, List.flatten_cons] using congrArg List.flatten hs.symm

/-- An exact per-record callback budget in actual bit-program instructions. -/
def callbackCost (width : ℕ) (bits : List Bool) : ℕ :=
  bits.length * (14 * width + 10) + 18 * width + 20

theorem any_false (records : List (List Bool)) :
    records.any (fun _ => false) = false := by
  induction records with
  | nil => rfl
  | cons bits rest ih => exact ih

end SubexponentialSAT.Subexp.GatherProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingVertexLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Gathering the actual assignment type at every vertex before packing. -/

namespace SubexponentialSAT.Subexp.PackingVertexLabels

def parserRegs (regs : Fin 8 → Bool) (tag present found : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 tag) 6 present) 7 found

theorem parserRegs_self (regs : Fin 8 → Bool) (tag present found : Bool)
    (h5 : regs 5 = tag) (h6 : regs 6 = present) (h7 : regs 7 = found) :
    parserRegs regs tag present found = regs := by
  funext i
  by_cases h : i = 7
  · subst i; simp [parserRegs, h7]
  by_cases h' : i = 6
  · subst i; simp [parserRegs, h6]
  by_cases h'' : i = 5
  · subst i; simp [parserRegs, h5]
  simp [parserRegs, h, h', h'']

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgramInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input preparation stages of the fixed physical packing controller. -/
namespace SubexponentialSAT.Subexp.PackingProgram

open PackingProgramSupport

abbrev Op := PackingPlumbing.Op

structure Input where
  assignment : List Bool
  width : List Bool
  dimension : List Bool
  degree : List Bool
  scopes : List Bool
  alphabet : List Bool

def labelsSetup : List Op := [.copy 40 0 39, .copy 41 3 39] ++ PackingPlumbing.move 25 10 39
def labelsSave : List Op := PackingPlumbing.move 13 26 39 ++ [.clear 0, .clear 3, .clear 12]
def typesSetup : List Op := [.copy 45 1 39, .copy 43 8 39]
def typesSave : List Op := PackingPlumbing.move 0 27 39 ++ [.clear 1, .clear 5]

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrameCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame counter for the complete-block packing controller. -/

namespace SubexponentialSAT.Subexp.PackingFrameCount

def budget (xs : List (List Bool)) : ℕ :=
  (xs.map fun bits => 8 * bits.length + 11).sum + 1

end SubexponentialSAT.Subexp.PackingFrameCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical subroutine calls for the all-type packing fold. -/

namespace SubexponentialSAT.Subexp.PackingBucketCalls

def bucketRegs (i : Fin 5) : Fin 8 := Fin.castAdd 3 i
def bucketPorts (i : Fin 6) : Fin 15 := Fin.castAdd 9 i
def countPorts : Fin 3 → Fin 15 := ![9, 1, 13]
def minimumPorts : Fin 3 → Fin 15 := ![10, 13, 14]

theorem bucketRegs_injective : Function.Injective bucketRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 8 => z.val) h)

theorem bucketPorts_injective : Function.Injective bucketPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 15 => z.val) h)

theorem countPorts_injective : Function.Injective countPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [countPorts]

theorem minimumPorts_injective : Function.Injective minimumPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [minimumPorts]

def merged (base : Fin 8 → Bool) (localRegs : Fin 5 → Bool) : Fin 8 → Bool :=
  ![localRegs 0, localRegs 1, localRegs 2, localRegs 3, localRegs 4, base 5, base 6, base 7]

theorem merged_restrict (regs : Fin 8 → Bool) :
    merged regs (fun i => regs (bucketRegs i)) = regs := by
  first | done | (funext i; fin_cases i <;> rfl)

end SubexponentialSAT.Subexp.PackingBucketCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed all-key bucket/minimum controller. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open PackingBucketCalls

/-- The actual subroutine costs fit one uniform bound in the encoded table
and query lengths. The minimum never exceeds its current unary cap. -/
theorem callback_arithmetic (L q m n B scan : ℕ)
    (hm : m ≤ L) (hn : n ≤ L) (hB : B ≤ L)
    (hs : scan ≤ 9 * L + L * (9 * q + 20) + 3) :
    (7 * L + 5) + (scan + ((7 * B + 5) + ((11 * B + 3) +
      ((9 * (m + n) + 12) + ((6 * min m n + 6) + ((3 * q + 3) +
        ((8 * q + 8) + ((8 * (2 * q + 1 + B) + 8) +
          (2 + ((3 * (2 * (2 * q + 1 + B) + 2) + 3) + 3)))))))))) ≤
      100 * (L + 1) * (q + 1) := by
  have hmin : min m n ≤ L := (min_le_left _ _).trans hm
  ring_nf at *
  omega

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured execution of the physical all-key packing fold. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open PackingBucketCalls

def finishRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 false) 6 true) 7 false

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual all-type scan and minimum fold, preserving the supplied type order. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open PackingBucketCalls

def parserRegs (regs : Fin 8 → Bool) (tag present found : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 tag) 6 present) 7 found

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgramAuxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Independent fixed bucket and inverse-address stages. -/
namespace SubexponentialSAT.Subexp.PackingProgram

open PackingProgramSupport

def bucketsSetup : List Op := PackingPlumbing.move 26 6 39 ++
  PackingPlumbing.move 27 7 39 ++ [.copy 42 10 39]
def bucketsSave : List Op := [.clear 6] ++ PackingPlumbing.move 5 15 39 ++
  PackingPlumbing.move 10 16 39
def queriesSetup : List Op := [.copy 42 0 39]
def queriesSave : List Op := PackingPlumbing.move 3 6 39 ++ [.clear 1, .copy 33 7 39]
def inverseSave : List Op := PackingPlumbing.move 8 35 39 ++ [.clear 7]


end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingEntryEmitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed emission of one covered packing vertex

The three accumulators are real runtime stacks. Storage receives one reversed
outer record; the two lookup streams receive raw pairs of framed words.
All payloads and counters are data, and every frame is built by fixed programs.
-/
namespace SubexponentialSAT.Subexp.PackingEntryEmitter

/-- Exact structured instruction count, independent of accumulator lengths. -/
def commandCost (vertex typeBytes block address : List Bool) : ℕ :=
  44*vertex.length + 24*typeBytes.length + 31*block.length + 15*address.length + 115

end SubexponentialSAT.Subexp.PackingEntryEmitter


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockZeroProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program testing whether all payload bits in a sequence of
frames are zero. Frame delimiters are ignored; no scalar arithmetic is hidden
inside this program. -/

namespace SubexponentialSAT.Subexp.BlockZeroProgram

@[simp] theorem update3_0 {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (0 : Fin 3) x = ![x,b,c] := by
  first | done | (funext i; fin_cases i <;> simp)

@[simp] theorem update3_1 {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (1 : Fin 3) x = ![a,x,c] := by
  first | done | (funext i; fin_cases i <;> simp)

@[simp] theorem update3_2 {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (2 : Fin 3) x = ![a,b,x] := by
  first | done | (funext i; fin_cases i <;> simp)

@[simp] theorem update2_0 {A : Type*} (a b x : A) :
    Function.update ![a,b] (0 : Fin 2) x = ![x,b] := by
  first | done | (funext i; fin_cases i <;> simp)

@[simp] theorem update2_1 {A : Type*} (a b x : A) :
    Function.update ![a,b] (1 : Fin 2) x = ![a,x] := by
  first | done | (funext i; fin_cases i <;> simp)

def isZero (words : List (List Bool)) : Bool := words.all (fun bits => bits.all (! ·))

@[simp] theorem isZero_nil : isZero [] = true := rfl

def skipCost (words : List (List Bool)) : ℕ :=
  3 + (words.map (fun bits => 3 * bits.length + 4)).sum

end SubexponentialSAT.Subexp.BlockZeroProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrameSkip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual framed-pre skip call with arbitrary surrounding packing data. -/

namespace SubexponentialSAT.Subexp.PackingFrameSkip

variable {s : ℕ}

def registers (i : Fin 3) : Fin 8 := Fin.castAdd 5 i
def stackPorts (count source : Fin s) : Fin 2 → Fin s := ![count, source]

theorem registers_injective : Function.Injective registers := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

theorem stacks_injective (count source : Fin s) (h : count ≠ source) :
    Function.Injective (stackPorts count source) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [stackPorts]

end SubexponentialSAT.Subexp.PackingFrameSkip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical ports for block-major extraction and its bucket reader. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

structure Context where
  keys : List Bool
  payload : List Bool
  block : List Bool
  address : List Bool
  storage : List Bool
  metadata : List Bool
  addresses : List Bool
  buckets : List Bool
  remaining : List Bool

def selectPorts (i : Fin 5) : Fin 19 := Fin.castAdd 14 i

theorem selectPorts_injective : Function.Injective selectPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 19 => z.val) h)

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the actual covered-entry emitter into the extraction controller. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

def emitPorts : Fin 10 → Fin 19 := ![3, 1, 10, 11, 12, 13, 14, 9, 17, 18]

theorem emitPorts_injective : Function.Injective emitPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitPorts]

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionCallback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual bucket-record callback: select its indexed vertex and emit it. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

def finishRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 false) 6 true) 7 false

def callbackBudget (payload block address : List Bool) : ℕ :=
  100 * (payload.length + block.length + address.length + 2)

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scan the ordered type buckets for one complete block. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

abbrev Entry := List Bool × List (List Bool)

def entryVertex (i : ℕ) (e : Entry) : List Bool := e.2.getD i []

def parserRegs (regs : Fin 8 → Bool) (tag present found : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 tag) 6 present) 7 found

theorem parserRegs_self (regs : Fin 8 → Bool) :
    parserRegs regs (regs 5) (regs 6) (regs 7) = regs := by
  funext j
  fin_cases j <;> simp [parserRegs]

theorem parserRegs_finish (regs : Fin 8 → Bool) :
    parserRegs (finishRegs regs) false true false = finishRegs regs := by
  funext j
  fin_cases j <;> simp [parserRegs, finishRegs]

theorem entry_split (i : ℕ) (e : Entry) (hi : i < e.2.length) :
    e.2.take i ++ entryVertex i e :: e.2.drop (i + 1) = e.2 := by
  rw [entryVertex, List.getD_eq_getElem e.2 [] hi, ← List.drop_eq_getElem_cons hi,
    List.take_append_drop]

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The records emitted by block extraction have the exact computed packing order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

def coverVertices (entries : List Entry) (n start : ℕ) : List (List Bool) :=
  (List.range' start n).flatMap fun i => entries.map (entryVertex i)

theorem coverVertices_succ (entries : List Entry) (n i : ℕ) :
    coverVertices entries (n + 1) i =
      entries.map (entryVertex i) ++ coverVertices entries n (i + 1) := by
  simp [coverVertices, List.range'_succ]

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentSeedRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ascending framed unary seed indices from a runtime unary seed count. -/

namespace SubexponentialSAT.Subexp.AssignmentSeedRange

abbrev unary (n : ℕ) := List.replicate n true

def dimStacks : Fin 5 → Fin 6 := Fin.castAdd 1
theorem dimStacks_injective : Function.Injective dimStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 6 => x.val) h)

def reverseRegisters : Fin 3 → Fin 5 := Fin.castAdd 2
def reverseStacks : Fin 4 → Fin 6 := ![3, 4, 5, 2]
theorem reverseRegisters_injective : Function.Injective reverseRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 5 => x.val) h)
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

def reversedRegs (regs : Fin 5 → Bool) : Fin 5 → Bool :=
  fun j => if j = 0 then false else if j = 1 then true else if j = 2 then false else regs j

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverEmitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/
namespace SubexponentialSAT.Subexp.PackingLeftoverEmitter

def commandCost (vertex rank address : List Bool) : ℕ :=
  44*vertex.length+31*rank.length+15*address.length+101

end SubexponentialSAT.Subexp.PackingLeftoverEmitter


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

def queryStacks : Fin 6 → Fin 18 := Fin.castAdd 12
theorem queryStacks_injective : Function.Injective queryStacks := Fin.castAdd_injective 6 12

def mergeRegs (base : Fin 8 → Bool) (localRegs : Fin 5 → Bool) : Fin 8 → Bool :=
  fun i => if h : i.val < 5 then localRegs ⟨i.val,h⟩ else base i

def emitterStacks : Fin 9 → Fin 18 := ![15,10,11,12,13,14,9,16,17]
theorem emitterStacks_injective : Function.Injective emitterStacks := by decide

def parserRegs (regs : Fin 8 → Bool) (tag present found : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 tag) 6 present) 7 found

structure Snapshot where
  rank : ℕ
  address : ℕ
  storage : List Bool
  metadata : List Bool
  addresses : List Bool

theorem parserRegs_self (regs : Fin 8 → Bool) (tag present found : Bool)
    (h5 : regs 5=tag) (h6 : regs 6=present) (h7 : regs 7=found) :
    parserRegs regs tag present found=regs := by
  funext i
  by_cases h : i=7
  · subst i; simp [parserRegs,h7]
  by_cases h' : i=6
  · subst i; simp [parserRegs,h6]
  by_cases h'' : i=5
  · subst i; simp [parserRegs,h5]
  simp [parserRegs,h,h',h'']

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed physical packing controller. Every alphabet, bucket, selected
vertex, leftover, and inverse-address query is produced by actual programs. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open PackingProgramSupport

def extractionSave : List Op := PackingPlumbing.move 10 30 39 ++
  [.clear 15, .copy 13 6 39]
def verticesSetup : List Op := [.copy 42 0 39]
def verticesSave : List Op := PackingPlumbing.move 5 7 39
def leftoversSave : List Op := PackingPlumbing.move 10 31 39 ++
  PackingPlumbing.move 13 32 39 ++ PackingPlumbing.move 14 33 39 ++
  [.push 12 false, .transfer 12 34, .clear 6, .clear 11]

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingOutputSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual leftover scan completes the metadata, storage order, and
address table produced by complete-block extraction. -/

namespace SubexponentialSAT.Subexp.PackingOutputSemantics

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

def snapshotOf (c : PackingExtraction.Context) : PackingLeftovers.Snapshot :=
  ⟨0, c.address.length, c.storage, c.metadata, c.addresses⟩

end SubexponentialSAT.Subexp.PackingOutputSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRepresentedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Polynomial rows generated from represented field operations

The producer uses code words, finite expression constructors, and the supplied
arithmetic callbacks. It never extracts coefficients from an abstract field
value. Inverse constants are computed by finite-field powering. The canonical
coefficient lift is applied only after compiling the source polynomial.
-/

namespace SubexponentialSAT.SubexpRepresentedRows

variable {C E : Type*} {Q : ℕ}

structure NodeCache (C : Type*) (Q : ℕ) where
  node : Fin Q → C
  inverse : Fin Q → C
  difference : Fin Q → Fin Q → C

end SubexponentialSAT.SubexpRepresentedRows

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the actual mismatch-index records and compare their count with R. -/

namespace SubexponentialSAT.Subexp.UniversalRowGuard

def countRegs : Fin 2 → Fin 8 := Fin.castAdd 6
def countStacks : Fin 2 → Fin 32 := ![17, 14]

def compareRegs : Fin 4 → Fin 8 := ![0, 1, 2, 7]
def compareStacks : Fin 2 → Fin 32 := ![14, 11]

end SubexponentialSAT.Subexp.UniversalRowGuard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGather
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Reading actual scalar and difference-row data for universal rows

All tables are packed runtime arrays. The selected index is unary data on
stack 16. The three fixed reads preserve their source tables and index and
produce the correction scalar, inverse node, and complete difference row.
-/

namespace SubexponentialSAT.Subexp.UniversalRowGather

abbrev Word := List Bool

inductive Field where
  | value | inverse | difference
  deriving DecidableEq

def arrayPort : Field → Fin 32
  | .value => 24
  | .inverse => 25
  | .difference => 27

def outputPort : Field → Fin 32
  | .value => 19
  | .inverse => 20
  | .difference => 0

def widthPort : Field → Fin 32
  | .value | .inverse => 29
  | .difference => 30

def readPorts (field : Field) : Fin 8 → Fin 32 :=
  ![arrayPort field, outputPort field, 2, widthPort field, 4, 5, 6, 7]

end SubexponentialSAT.Subexp.UniversalRowGather

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

structure Factor (C : Type*) where
  inverseDifference : C
  negativeNode : C

structure Term (C : Type*) where
  value : C
  inverseNode : C
  factors : List (Factor C)

def literalPorts : Fin 3 → Fin 8 := ![5, 3, 4]

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed array reads and framing for one interpolation factor. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactors

open UniversalRowGather (Word)

def differencePorts : Equiv.Perm (Fin 32) :=
  (Equiv.swap 0 24).trans ((Equiv.swap 1 19).trans (Equiv.swap 9 16))

def negativePorts : Equiv.Perm (Fin 32) :=
  (Equiv.swap 24 26).trans ((Equiv.swap 12 19).trans (Equiv.swap 9 16))

end SubexponentialSAT.Subexp.UniversalRowFactors

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactorLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open UniversalRowGather (Word)

def equalityRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def equalityStacks : Fin 13 → Fin 32 := Fin.castAdd 19

def factor (differences negatives : List Word) (j : ℕ) : UniversalRowProgram.Factor Word :=
  ⟨differences.getD j [], negatives.getD j []⟩

def callbackCost (width outer : ℕ) (index : Word) : ℕ :=
  (28 * width + 60) * index.length + 9 * outer + 80 * width + 140

def indexWord (i : ℕ) : Word := List.replicate i true

@[simp] theorem indexWord_length (i : ℕ) : (indexWord i).length = i := by
  simp [indexWord]

@[simp] theorem indexWord_reverse (i : ℕ) : (indexWord i).reverse = indexWord i := by
  simp [indexWord]

@[simp] theorem indexWord_inj (i j : ℕ) : indexWord i = indexWord j ↔ i = j := by
  constructor
  · intro h
    simpa using congrArg List.length h
  · rintro rfl
    rfl

def factors (differences negatives : List Word) (i : ℕ) (positions : List ℕ) :
    List (UniversalRowProgram.Factor Word) :=
  (positions.filter fun j => decide (j ≠ i)).map (factor differences negatives)

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermFraming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical framing of a gathered correction term and the final row. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermFraming

abbrev Word := List Bool

def termCost (value inverse factorBytes : Word) : ℕ :=
  24 * (value.length + inverse.length) + 8 * factorBytes.length + 42

end SubexponentialSAT.Subexp.UniversalRowTermFraming

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open UniversalRowGather (Word)
open UniversalRowFactorLoop (indexWord)

structure Tables where
  values : List Word
  inverses : List Word
  negatives : List Word
  differences : List (List Word)

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowEmitCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed call to the actual row source emitter inside the row workspace. -/

namespace SubexponentialSAT.Subexp.UniversalRowEmitCall

def regs : Fin 3 → Fin 8 := Fin.castAdd 5
def stackMap : Fin 8 → Fin 32 := ![31, 3, 10, 1, 2, 4, 5, 6]

end SubexponentialSAT.Subexp.UniversalRowEmitCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port maps and the persistent ring-cache frame for source-table
callbacks. These lemmas are independent of the integer numerator evaluator. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def numeratorRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def numeratorPorts (i : Fin 64) : Fin 256 :=
  if i = 50 then 253 else if i = 51 then 254 else Fin.castAdd 192 i

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

def arrayPort (right : Bool) : Fin 16 := if right then 10 else 0
def rowPort (right : Bool) : Fin 16 := if right then 12 else 1
def lookupPorts (right : Bool) : Fin 8 → Fin 16 :=
  ![arrayPort right, rowPort right, 2, 3, 4, 5, 6, 7]

def equalityRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def equalityStacks : Fin 13 → Fin 16 := Fin.castAdd 3

def emitRegs : Fin 3 → Fin 8 := ![0, 1, 7]
def emitStacks : Fin 4 → Fin 16 := ![8, 3, 13, 9]

def reverseStacks : Fin 4 → Fin 16 := ![13, 3, 14, 9]

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generate all positions on tape, then retain the mismatches.  The output
is in descending position order, as required by the prepend-based row loops. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchProgram

def rangeMap : Fin 10 → Fin 17 := ![0, 1, 10, 2, 3, 5, 6, 8, 9, 7]

def filterRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def filterStacks : Fin 16 → Fin 17 := Fin.castAdd 1

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

def inputRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def inputStacks : Fin 29 → Fin 49 := Fin.castAdd 20

def filterStacks : Fin 17 → Fin 49 := ![19, 0, 1, 21, 2, 3, 4, 5, 6, 7, 18, 8, 9, 10, 45, 11, 22]

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.Subexp

def lookupRegs : Fin 6 → Fin 16 := Fin.castAdd 10
def lookupPorts : Fin 16 → Fin 320 := ![306,304,305,288,289,290,291,292,293,294,295,296,297,298,299,300]
def lowRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def lowPorts : Fin 64 → Fin 320 := Fin.castAdd 256
def vectorPorts : Fin 256 → Fin 320 := Fin.castAdd 64

def mismatchPorts : Fin 49 → Fin 320 :=
  fun j => if h : j.val < 42 then ⟨j.val,by omega⟩ else ⟨j.val+26,by omega⟩
def emitterRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def emitterPorts : Fin 32 → Fin 320 := fun j=>⟨256+j.val,by omega⟩
def comparePorts (left right : Fin 320) : Fin 32 → Fin 320 :=
  ![left,right,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,301,15,16,17,18,19,20,21,22,23,303,302,24,25,307]

def literalRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def literalPorts (src : Fin 320) : Fin 4 → Fin 320 := ![src,315,316,287]

def cleanupPorts : List (Fin 320) :=
  [23,24,67,68,69,70,71,72,73,74] ++
  (List.ofFn fun j : Fin 31 => (⟨256+j.val,by omega⟩ : Fin 320)) ++
  (List.ofFn fun j : Fin 16 => (⟨288+j.val,by omega⟩ : Fin 320)) ++ [307,315,316]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured staging and exact caller-store frames for the fixed source bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.Subexp

def emitterDestinations : List (Fin 320) := [280,281,282,283,284,285,286,259,266,269]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT


def frameRegisters : Fin 3 → Fin 16 := Fin.castAdd 13
def frameStacks : Fin 2 → Fin 340 := ![330,334]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested row-data and source emitters. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceBound

open UniversalRowProgram
open UniversalRowFactorLoop (indexWord)

def indicesBound (S : ℕ) := 1 + (2 * S + 2) * S

end SubexponentialSAT.Subexp.UniversalRowSourceBound

end OAI.Algorithms
end


