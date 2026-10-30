-- Prove2me | Definitions.Def_OAIQ081S002
-- name    : OAIQ081S002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:22:17.881523+00:00
-- url     : https://prove2.me/theorems/de98c448-18bb-4cfe-9db5-1ea06cdcf67f
-- title:
--   Definitions bundle OAIQ081S002 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 300 declarations of OpenAI's Lean: 157 definitions, 5 inductive types or structures, 3 instances and 135 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.DyadicWidth.width`, `OAI.Algorithms.SubexponentialSAT.Encoding.readNat`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.Bank`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.Front`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.Regs`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.bankPort`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.emitReg`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.frontPort`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.outputPort`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.Formula`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.absorb`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.clauseSet`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.cleanLiterals`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.contains`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.dedupClauses`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.dedupLiterals`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.equivalent`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.eraseClauses`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.formulaSet`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.normalize`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.removeTautologies`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.strictSubset`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.subset`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.tautology`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.perRecordCost`, `OAI.Algorithms.SubexponentialSAT.ExecCNFRecords.ports`, `OAI.Algorithms.SubexponentialSAT.ExecCNFRecords.regs`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.memberReg`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.memberStack`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.fixedBits`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer.bumpWord`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer.bumpWords`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.Measured`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.bitStacks`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.membershipEqReg`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.membershipEqStack`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.notM`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.workPort`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFilterReverse.Regs` and 122 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_DyadicWidth`, `SubexponentialSAT_Encoding`, `SubexponentialSAT_ExecBranchControllerSupport`, `SubexponentialSAT_ExecCNF`, `SubexponentialSAT_ExecCNFMembership`, `SubexponentialSAT_ExecCNFRecords`, `SubexponentialSAT_ExecCNFSubset`, `SubexponentialSAT_ExecCNFTupleEnumeration`, `SubexponentialSAT_ExecCNFTupleOdometer`, `SubexponentialSAT_ExecClauseCost`, `SubexponentialSAT_ExecClauseCost39Lift`, `SubexponentialSAT_ExecClauseDedupProgram`, `SubexponentialSAT_ExecClauseFilterReverse`, `SubexponentialSAT_ExecClauseFiltersProgram`, `SubexponentialSAT_ExecClauseRelationScan`, `SubexponentialSAT_ExecClauseRelationScanEncoding`, `SubexponentialSAT_ExecClauseRelationScanPreserve`, `SubexponentialSAT_ExecClauseRelationsProgram`, `SubexponentialSAT_ExecCleanLiteralsProgram`, `SubexponentialSAT_ExecLiteralDedupProgram`, `SubexponentialSAT_ExecPetalChildProgram`, `SubexponentialSAT_ExecPetalFamilyProgram`, `SubexponentialSAT_ExecPetalProgram`, `SubexponentialSAT_ExecSunflowerSearch`, `SubexponentialSAT_ExecWorklistProgram`, `SubexponentialSAT_Factor`, `SubexponentialSAT_FiniteField`, `SubexponentialSAT_FixedParameters`, `SubexponentialSAT_FrontendProgram`, `SubexponentialSAT_Incidence`, `SubexponentialSAT_JetCRT`, `SubexponentialSAT_LiftRing`, `SubexponentialSAT_LocalExpectation`, `SubexponentialSAT_LocalSpectrum`, `SubexponentialSAT_ModularArithmetic`, `SubexponentialSAT_ModularDivisionPrograms`, `SubexponentialSAT_ModularPrograms`, `SubexponentialSAT_ModularQuotientPrograms`, `SubexponentialSAT_ModularRingCore`, `SubexponentialSAT_ModularRingPrograms`, `SubexponentialSAT_MulticolorTypes`, `SubexponentialSAT_ParserProgram`, `SubexponentialSAT_PowerPrograms`, `SubexponentialSAT_ProgramEncoding`, `SubexponentialSAT_RecordPrograms`, `SubexponentialSAT_SAT`, `SubexponentialSAT_SubexpFlatAdd`, `SubexponentialSAT_SubexpLiftRing`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpQuarticRing`, `SubexponentialSAT_SunflowerBranch`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S034`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S041`, `OAIQ081S042` and `OAIQ081S043`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DyadicWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive dyadic width for bounded tuple enumeration, including zero. -/

namespace SubexponentialSAT.DyadicWidth

def width (m : ℕ) : ℕ := Nat.log 2 m + 1

end SubexponentialSAT.DyadicWidth

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete finite CNF syntax and semantics for the candidate SAT argument. -/

namespace SubexponentialSAT.SAT

universe u

variable {V : Type u}

def Literal.negate (l : Literal V) : Literal V :=
  ⟨l.variable, !l.positive⟩

@[simp] theorem Literal.eval_eq_true (a : Assignment V) (l : Literal V) :
    l.eval a = true ↔ a l.variable = l.positive := by
  simp [Literal.eval]

@[simp] theorem Literal.negate_negate (l : Literal V) : l.negate.negate = l := by
  cases l with
  | mk v p => cases p <;> rfl

@[simp] theorem Literal.eval_negate (a : Assignment V) (l : Literal V) :
    l.negate.eval a = !(l.eval a) := by
  cases l with
  | mk v p => cases p <;> cases h : a v <;> simp [Literal.eval, Literal.negate, h]

variable [DecidableEq V]

omit [DecidableEq V] in
@[simp] theorem Clause.eval_eq_true (a : Assignment V) (C : Clause V) :
    C.eval a = true ↔ ∃ l ∈ C, l.eval a = true := by
  simp [Clause.eval]

omit [DecidableEq V] in
@[simp] theorem CNF.eval_eq_true (a : Assignment V) (F : CNF V) :
    F.eval a = true ↔ ∀ C ∈ F, C.eval a = true := by
  simp [CNF.eval]

omit [DecidableEq V] in
@[simp] theorem Clause.eval_empty (a : Assignment V) :
    (∅ : Clause V).eval a = false := by simp [Clause.eval]

omit [DecidableEq V] in
@[simp] theorem CNF.eval_empty (a : Assignment V) :
    (∅ : CNF V).eval a = true := by simp [CNF.eval]

section Decidable

@[simp] theorem Clause.eval_insert (a : Assignment V) (l : Literal V) (C : Clause V) :
    (insert l C).eval a = (l.eval a || C.eval a) := by
  apply Bool.eq_iff_iff.mpr
  simp [Clause.eval]

@[simp] theorem CNF.eval_insert (a : Assignment V) (C : Clause V) (F : CNF V) :
    (insert C F).eval a = (C.eval a && F.eval a) := by
  apply Bool.eq_iff_iff.mpr
  simp [CNF.eval]

section Finite

variable [Fintype V]

@[simp] theorem mem_satisfyingAssignments (a : Assignment V) (F : CNF V) :
    a ∈ satisfyingAssignments F ↔ F.eval a = true := by
  simp [satisfyingAssignments]

end Finite
end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
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

/-- Read a unary field and return the unconsumed suffix. -/
def readNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readNat rest
      pure (n + 1, tail)

@[simp] theorem readNat_encodeNat_append (n : ℕ) (rest : List Bool) :
    readNat (encodeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [encodeNat, readNat]
  | succ n ih =>
      change (do
        let (v, tail) ← readNat (encodeNat n ++ rest)
        pure (v + 1, tail)) = some (n + 1, rest)
      rw [ih]
      rfl

@[simp] theorem readNat_encodeNat (n : ℕ) : readNat (encodeNat n) = some (n, []) := by
  simpa using readNat_encodeNat_append n []

@[simp] theorem length_encodeNat (n : ℕ) : (encodeNat n).length = n + 1 := by
  simp [encodeNat]

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro n m h
  have hr := congrArg (fun bits => readNat (bits ++ [])) h
  simpa using hr

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_FixedParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite programs and measured expansion of TM2 statements

This module expands TM2's finite statement blocks into actual one-constructor
stack transitions.  The execution theorem counts those transitions.  It does
not identify a stack operation with a primitive binary tape operation; that
additional encoding is a separate compiler layer.
-/

namespace SubexponentialSAT.FixedParameters

open SubexponentialSAT.Computation
open Turing.TM2

instance labelFintype (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
instance variableFintype (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin


open SubexponentialSAT.Computation
open Turing


open SubexponentialSAT.Computation Turing


open SubexponentialSAT.Computation Turing

end SubexponentialSAT.FixedParameters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

def pair {α : Type*} (a b : α) : Fin 2 → α := fun i => if i = 0 then a else b

@[simp] theorem pair_zero {α : Type*} (a b : α) : pair a b 0 = a := rfl
@[simp] theorem pair_one {α : Type*} (a b : α) : pair a b 1 = b := rfl

@[simp] theorem update_pair_zero {α : Type*} (a b c : α) :
    Function.update (pair a b) 0 c = pair c b := by
  funext i
  fin_cases i <;> simp [pair]

@[simp] theorem update_pair_one {α : Type*} (a b c : α) :
    Function.update (pair a b) 1 c = pair a c := by
  funext i
  fin_cases i <;> simp [pair]

/-! ## In-place removal of one escape frame -/

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control skipping of framed CNF records

The program below has three Boolean registers, one Boolean stack, and eleven
fixed labels. It consumes an escaped frame or one tagged list item without
materializing the payload. The payload may itself encode a list of literals,
a clause, or a more deeply nested record. Every bound is proved for actual
`BitProgram.step` traces, rather than assigned to a semantic list operation.
-/

namespace SubexponentialSAT.ExecCNFRecords

/-- Registers 0, 1, 2 hold the last bit, presence flag, and item-found flag. -/
def regs (value present found : Bool) : Fin 3 → Bool :=
  fun i => if i = 0 then value else if i = 1 then present else found

@[simp] theorem regs_zero (v p f : Bool) : regs v p f 0 = v := rfl
@[simp] theorem regs_one (v p f : Bool) : regs v p f 1 = p := rfl
@[simp] theorem regs_two (v p f : Bool) : regs v p f 2 = f := rfl

@[simp] theorem update_regs_zero (v p f b : Bool) :
    Function.update (regs v p f) 0 b = regs b p f := by
  funext i
  fin_cases i <;> simp [regs]

@[simp] theorem update_regs_one (v p f b : Bool) :
    Function.update (regs v p f) 1 b = regs v b f := by
  funext i
  fin_cases i <;> simp [regs]

@[simp] theorem update_regs_two (v p f b : Bool) :
    Function.update (regs v p f) 2 b = regs v p b := by
  funext i
  fin_cases i <;> simp [regs]

@[simp] theorem update_stack (input output : List Bool) :
    Function.update (fun _ : Fin 1 => input) 0 output = fun _ : Fin 1 => output := by
  funext i
  fin_cases i
  simp

end SubexponentialSAT.ExecCNFRecords

namespace SubexponentialSAT.ExecCNFRecords

/-- Source, destination and scratch are fixed ports 0, 1 and 2. -/
def ports {α : Type*} (source destination scratch : α) : Fin 3 → α :=
  fun i => if i = 0 then source else if i = 1 then destination else scratch

@[simp] theorem ports_zero {α : Type*} (a b c : α) : ports a b c 0 = a := rfl
@[simp] theorem ports_one {α : Type*} (a b c : α) : ports a b c 1 = b := rfl
@[simp] theorem ports_two {α : Type*} (a b c : α) : ports a b c 2 = c := rfl

@[simp] theorem update_ports_zero {α : Type*} (a b c d : α) :
    Function.update (ports a b c) 0 d = ports d b c := by
  funext i
  fin_cases i <;> simp [ports]
@[simp] theorem update_ports_one {α : Type*} (a b c d : α) :
    Function.update (ports a b c) 1 d = ports a d c := by
  funext i
  fin_cases i <;> simp [ports]
@[simp] theorem update_ports_two {α : Type*} (a b c d : α) :
    Function.update (ports a b c) 2 d = ports a b d := by
  funext i
  fin_cases i <;> simp [ports]

end SubexponentialSAT.ExecCNFRecords

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SunflowerBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal-set sunflower branching

Concrete CNF children and their semantic union, together with the absorption
invariants used by the cumulative-insertion argument. Opposite polarities are
distinct literals; no variable-disjointness premise is used.
-/

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
open scoped BigOperators
universe u
variable {V : Type u} [DecidableEq V]

/-- A finite structural measure for recursive branching; no runtime assertion. -/
def literalMass (F : CNF V) : ℕ := ∑ C ∈ F, C.card

omit [DecidableEq V] in
@[simp] theorem literalMass_singleton (C : Clause V) : literalMass ({C} : CNF V) = C.card := by
  simp [literalMass]

end SubexponentialSAT.SunflowerBranch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF

universe u
abbrev Clause (α : Type u) := List α
abbrev Formula (α : Type u) := List (Clause α)

variable {α : Type u} [DecidableEq α]

def clauseSet (C : Clause α) : Finset α := C.toFinset

def formulaSet (F : Formula α) : Finset (Finset α) := (F.map clauseSet).toFinset

@[simp] theorem mem_clauseSet {x : α} {C : Clause α} : x ∈ clauseSet C ↔ x ∈ C := by
  simp [clauseSet]

@[simp] theorem mem_formulaSet {C : Finset α} {F : Formula α} :
    C ∈ formulaSet F ↔ ∃ D ∈ F, clauseSet D = C := by
  simp [formulaSet]

@[simp] theorem clauseSet_nil : clauseSet ([] : Clause α) = ∅ := rfl
@[simp] theorem clauseSet_cons (x : α) (C : Clause α) :
    clauseSet (x :: C) = insert x (clauseSet C) := by simp [clauseSet]
@[simp] theorem clauseSet_append (C D : Clause α) :
    clauseSet (C ++ D) = clauseSet C ∪ clauseSet D := by simp [clauseSet]
@[simp] theorem formulaSet_nil : formulaSet ([] : Formula α) = ∅ := rfl
@[simp] theorem formulaSet_cons (C : Clause α) (F : Formula α) :
    formulaSet (C :: F) = insert (clauseSet C) (formulaSet F) := by simp [formulaSet]
@[simp] theorem formulaSet_append (F G : Formula α) :
    formulaSet (F ++ G) = formulaSet F ∪ formulaSet G := by simp [formulaSet]

/-- A left-to-right linear literal-membership scan. -/
def contains (x : α) : List α → Bool
  | [] => false
  | y :: ys => if x = y then true else contains x ys

@[simp] theorem contains_true (x : α) (L : List α) : contains x L = true ↔ x ∈ L := by
  induction L with
  | nil => simp [contains]
  | cons y ys ih =>
    by_cases h : x = y
    · simp [contains, h]
    · simp [contains, h, ih]

/-- Every literal of the first list is searched for in the second. -/
def subset : Clause α → Clause α → Bool
  | [], _ => true
  | x :: xs, D => contains x D && subset xs D

@[simp] theorem subset_true (C D : Clause α) :
    subset C D = true ↔ clauseSet C ⊆ clauseSet D := by
  induction C with
  | nil => simp [subset]
  | cons x xs ih => simp [subset, ih, Finset.insert_subset_iff]

def equivalent (C D : Clause α) : Bool := subset C D && subset D C

@[simp] theorem equivalent_true (C D : Clause α) :
    equivalent C D = true ↔ clauseSet C = clauseSet D := by
  simp only [equivalent, Bool.and_eq_true, subset_true]
  exact ⟨fun h => Finset.Subset.antisymm h.1 h.2,
    fun h => ⟨h ▸ Finset.Subset.refl _, h ▸ Finset.Subset.refl _⟩⟩

def strictSubset (C D : Clause α) : Bool := subset C D && !(subset D C)

@[simp] theorem strictSubset_true (C D : Clause α) :
    strictSubset C D = true ↔ clauseSet C ⊂ clauseSet D := by
  simp only [strictSubset, Bool.and_eq_true, subset_true]
  constructor
  · rintro ⟨hCD, hf⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hCD, ?_⟩
    intro heq
    have ht : subset D C = true := subset_true D C |>.mpr (heq ▸ Finset.Subset.refl _)
    simp [ht] at hf
  · intro h
    obtain ⟨hCD, hne⟩ := Finset.ssubset_iff_subset_ne.mp h
    refine ⟨hCD, ?_⟩
    cases hb : subset D C with
    | false => rfl
    | true => exact False.elim (hne (Finset.Subset.antisymm hCD ((subset_true D C).mp hb)))

/-- Keep the last occurrence of each literal, preserving that order. -/
def dedupLiterals : Clause α → Clause α
  | [] => []
  | x :: xs => if contains x xs = true then dedupLiterals xs else x :: dedupLiterals xs

@[simp] theorem mem_dedupLiterals (x : α) (C : Clause α) :
    x ∈ dedupLiterals C ↔ x ∈ C := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons y ys ih =>
    by_cases h : contains y ys = true
    · have hy : y ∈ ys := (contains_true y ys).mp h
      simp only [dedupLiterals, h, ite_true, if_true, List.mem_cons, ih]
      exact ⟨Or.inr, fun hx => hx.elim (fun heq => heq ▸ hy) id⟩
    · simp [dedupLiterals, h, ih]

@[simp] theorem clauseSet_dedupLiterals (C : Clause α) :
    clauseSet (dedupLiterals C) = clauseSet C := by
  ext x
  simp

/-- Remove duplicate clauses using set equality, including permutations. -/
def dedupClauses : Formula α → Formula α
  | [] => []
  | C :: F => if F.any (fun D => equivalent C D) = true then dedupClauses F
      else C :: dedupClauses F

@[simp] theorem any_equivalent_true (C : Clause α) (F : Formula α) :
    F.any (fun D => equivalent C D) = true ↔ clauseSet C ∈ formulaSet F := by
  simp only [List.any_eq_true, equivalent_true, mem_formulaSet]
  constructor
  · rintro ⟨D, hD, heq⟩
    exact ⟨D, hD, heq.symm⟩
  · rintro ⟨D, hD, heq⟩
    exact ⟨D, hD, heq.symm⟩

@[simp] theorem formulaSet_dedupClauses (F : Formula α) :
    formulaSet (dedupClauses F) = formulaSet F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simp only [dedupClauses, h, ite_true, if_true, formulaSet_cons, ih]
      exact (Finset.insert_eq_of_mem ((any_equivalent_true C F).mp h)).symm
    · simp [dedupClauses, h, ih]

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

@[simp] theorem not_true_iff (b : Bool) : (!b) = true ↔ ¬ b = true := by
  cases b <;> simp

@[simp] theorem any_strictSubset_true (C : Clause α) (F : Formula α) :
    F.any (fun D => strictSubset D C) = true ↔ ∃ D ∈ formulaSet F, D ⊂ clauseSet C := by
  simp only [List.any_eq_true, strictSubset_true, mem_formulaSet]
  constructor
  · rintro ⟨D, hD, hsub⟩
    exact ⟨clauseSet D, ⟨D, hD, rfl⟩, hsub⟩
  · rintro ⟨D, ⟨E, hE, rfl⟩, hsub⟩
    exact ⟨E, hE, hsub⟩

/-- Test whether a clause contains a literal together with its designated opposite. -/
def tautology (neg : α → α) (C : Clause α) : Bool :=
  C.any fun x => contains (neg x) C

@[simp] theorem tautology_true (neg : α → α) (C : Clause α) :
    tautology neg C = true ↔ ∃ x ∈ clauseSet C, neg x ∈ clauseSet C := by
  simp [tautology, List.any_eq_true]

def removeTautologies (neg : α → α) (F : Formula α) : Formula α :=
  F.filter fun C => !(tautology neg C)

/-- Strict-superset deletion; semantic duplicate clauses are removed first. -/
def absorb (F : Formula α) : Formula α :=
  (dedupClauses F).filter fun C => !(F.any fun D => strictSubset D C)

/-- Literal deduplication is separate from clause deduplication. -/
def cleanLiterals (F : Formula α) : Formula α := F.map dedupLiterals

@[simp] theorem formulaSet_cleanLiterals (F : Formula α) :
    formulaSet (cleanLiterals F) = formulaSet F := by
  simp [cleanLiterals, formulaSet, List.map_map, Function.comp_def]

def normalize (neg : α → α) (F : Formula α) : Formula α :=
  absorb (removeTautologies neg (cleanLiterals F))

/-- Remove every clause equal as a set to a selected clause. -/
def eraseClauses (F S : Formula α) : Formula α :=
  F.filter fun C => !(S.any fun D => equivalent C D)

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

@[simp] theorem core_nonempty_iff (H : Clause α) :
    (clauseSet H).Nonempty ↔ H.isEmpty = false := by
  cases H with
  | nil => simp
  | cons x xs => simp


@[simp] theorem clauseSet_difference (C H : Clause α) :
    clauseSet (C.filter (fun x => !(contains x H))) = clauseSet C \ clauseSet H := by
  ext x
  simp [Bool.eq_false_iff]

/-- Raw list-width assumption used in the enumeration bounds. -/
def RawWidthAtMost (k : ℕ) (F : Formula α) : Prop := ∀ C ∈ F, C.length ≤ k

end SubexponentialSAT.ExecSunflowerSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit costs for the executable clause loops

These routines return their result together with the number of charged events
in the displayed recursive execution. A recursive list-case inspection costs
one event; a literal equality test costs one further event. These are list-loop
and comparison units, **not** primitive bit-machine transitions. In particular,
`DecidableEq α` is an equality interface, not a unit-cost bit implementation.
No cost is attached to an arbitrary uninstrumented function.
-/

namespace SubexponentialSAT.ExecClauseCost

universe u v
variable {α : Type u} {β : Type v}

abbrev Measured (α : Type u) := α × ℕ

/-- Negation adds one Boolean operation. -/
def notM (p : Measured Bool) : Measured Bool := (!p.1, p.2 + 1)

@[simp] theorem notM_value (p : Measured Bool) : (notM p).1 = !p.1 := rfl

def bitStacks (xs ys : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then xs else ys


end SubexponentialSAT.ExecClauseCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseCost39Lift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms
namespace SubexponentialSAT.ExecClauseCost

/-- Fixed register ports for the membership routine's equality subroutine. -/
def membershipEqReg (i : Fin 5) : Fin 7 := Fin.castAdd 2 i

/-- Compare caller stack 1 with caller stack 3. -/
def membershipEqStack (i : Fin 2) : Fin 5 := if i = 0 then 1 else 3

theorem membershipEqReg_injective : Function.Injective membershipEqReg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 7 => x.val) h

theorem membershipEqStack_injective : Function.Injective membershipEqStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [membershipEqStack]

end SubexponentialSAT.ExecClauseCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared record representation for executable programs

A scalar is stored as a Boolean payload (little-endian bits for natural
numbers; the scalar module specifies any fixed padding). A record list uses
the existing `Encoding.encodeList id`: false terminates the list; true starts
an escaped frame. Matrices and other fixed-depth schemas nest this same
representation. These are executable decoders and exact size identities,
not assertions that a machine has run them.
-/

namespace SubexponentialSAT.ProgramEncoding

abbrev Records := List (List Bool)

end SubexponentialSAT.ProgramEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RecordPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A reusable actual iterator over the project's framed-record representation.
The callback is a fixed structured program, whose executions are measured in the
same semantics as the parser and iterator. It is never an atomic semantic oracle.
-/

namespace SubexponentialSAT.RecordPrograms

structure Ports (r s : ℕ) where
  tag : Fin r
  present : Fin r
  found : Fin r
  source : Fin s
  payload : Fin s
  tag_ne_present : tag ≠ present
  found_ne_tag : found ≠ tag
  found_ne_present : found ≠ present
  source_ne_payload : source ≠ payload

def budget (cost : List Bool → ℕ) : List (List Bool) → ℕ
  | [] => 0
  | bits :: rest => 6 * bits.length + cost bits + 7 + budget cost rest

theorem extend_pair {α β : Type} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    (a b : β) (base : α → β) :
    Function.extend (ParserProgram.pair x y) (ParserProgram.pair a b) base =
      Function.update (Function.update base x a) y b := by
  classical
  have hinj : Function.Injective (ParserProgram.pair x y) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [ParserProgram.pair, Ne.symm hxy]
  funext z
  by_cases hx : z = x
  · subst z
    have h := hinj.extend_apply (ParserProgram.pair a b) base (0 : Fin 2)
    simpa [ParserProgram.pair, hxy] using h
  · by_cases hy : z = y
    · subst z
      have h := hinj.extend_apply (ParserProgram.pair a b) base (1 : Fin 2)
      simpa [ParserProgram.pair] using h
    · have hout : ¬ ∃ i, ParserProgram.pair x y i = z := by
        rintro ⟨i, hi⟩
        fin_cases i <;> simp [ParserProgram.pair] at hi <;> subst z <;> contradiction
      rw [Function.extend_apply' _ _ _ hout]
      simp [hx, hy]

end SubexponentialSAT.RecordPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFMembership
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded CNF membership building blocks

Fixed ports: source 0, reversed current payload 1, preserved reversed query 2,
query copy 3, and temporary stack 4. Register 4 is the answer; registers 5 and
6 are the outer-list tag and presence flag. Registers 0--3 are work bits.
-/

namespace SubexponentialSAT.ExecCNFMembership

def perRecordCost (query bits : List Bool) : ℕ := 20 * (bits.length + query.length + 1)

theorem any_eq_membership (query : List Bool) (records : List (List Bool)) :
    records.any (fun bits => decide (bits = query)) = decide (query ∈ records) := by
  induction records with
  | nil => simp
  | cons bits rest ih =>
      rw [List.any_cons, ih]
      simp [eq_comm]

end SubexponentialSAT.ExecCNFMembership

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded clause subset testing

The fixed program uses ten Boolean registers and eight Boolean stacks. The
source clause is scanned destructively on stack 0. Stack 2 preserves the entire
encoded target clause. All comparisons use the proved encoded membership
program, after a real preserving copy of the target.
-/
namespace SubexponentialSAT.ExecCNFSubset

def memberReg (i : Fin 7) : Fin 10 := Fin.castAdd 3 i

def memberStack (i : Fin 5) : Fin 8 :=
  match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 1
  | 3 => 5
  | _ => 6

theorem memberReg_injective : Function.Injective memberReg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 10 => i.val) h

theorem memberStack_injective : Function.Injective memberStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [memberStack]

end SubexponentialSAT.ExecCNFSubset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

def regPort (i : Fin 10) : Fin 12 := Fin.castAdd 2 i
def stackPort (i : Fin 8) : Fin 10 := Fin.castAdd 2 i
def original (i : Fin 2) : Fin 10 := Fin.natAdd 8 i

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clause-relation scans over encoded formulas

All modes use a fixed finite Boolean program. An outer record iterator parses
each encoded clause, then invokes the concrete preserving clause-relation
program. The query clause is preserved for callers that subsequently emit it.
-/
namespace SubexponentialSAT.ExecClauseRelationScan

abbrev Clause := List (List Bool)
abbrev Formula := List Clause

inductive Mode
  | equivalent
  | strictSubset
  | missingCore
  deriving DecidableEq

def test (mode : Mode) (C Q : Clause) : Bool :=
  match mode with
  | .equivalent => ExecCNF.equivalent C Q
  | .strictSubset => ExecCNF.strictSubset C Q
  | .missingCore => !(ExecCNF.subset Q C)

def resultRegister : Mode → Fin 15
  | .equivalent => 10
  | .strictSubset => 11
  | .missingCore => 9

def regPort (i : Fin 12) : Fin 15 := Fin.castAdd 3 i
def stackPort (i : Fin 10) : Fin 12 := Fin.castAdd 2 i

end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScanPreserve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A preserving wrapper for repeated clause-vs-formula scans. A real copy of
the full formula is scanned, and its residual copy is explicitly cleared. -/
namespace SubexponentialSAT.ExecClauseRelationScan.Preserving

def stackPort (i : Fin 12) : Fin 13 := Fin.castAdd 1 i

end SubexponentialSAT.ExecClauseRelationScan.Preserving

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScanEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact natural-code interfaces for the fixed encoded relation scanner. -/
namespace SubexponentialSAT.ExecClauseRelationScan

def codeClause (C : List ℕ) : Clause := C.map Encoding.encodeNat
def codeFormula (F : List (List ℕ)) : Formula := F.map codeClause

def codeTest (mode : Mode) (C Q : List ℕ) : Bool :=
  match mode with
  | .equivalent => ExecCNF.equivalent C Q
  | .strictSubset => ExecCNF.strictSubset C Q
  | .missingCore => !(ExecCNF.subset Q C)

end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_JetCRT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Reconstruction from formal polynomial jets over a commutative ring

These results use unit differences of nodes, not a field assumption. Jets are
formal Taylor polynomials modulo `X ^ D`; no factorial divisions occur.
-/

noncomputable section

namespace SubexponentialSAT.JetCRT

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- The local modulus for an order-`D` jet at `a`. -/
def nodePower (a : A) (D : ℕ) : A[X] := (X - C a) ^ D

/-- The formal order-`D` Taylor polynomial, using `X` as the local coordinate. -/
noncomputable def jet (a : A) (D : ℕ) (f : A[X]) : A[X] :=
  (f.comp (X + C a)) %ₘ (X ^ D)

variable {ι : Type*} [Fintype ι]

/-- The product of all powered linear local moduli. -/
def modulus (θ : ι → A) (D : ℕ) : A[X] := ∏ i, nodePower (θ i) D

section ExplicitFormula

variable [DecidableEq ι]

/-- The product of all local moduli except the one at index `i`. -/
def cofactor (θ : ι → A) (D : ℕ) (i : ι) : A[X] :=
  ∏ j ∈ Finset.univ.erase i, nodePower (θ j) D

end ExplicitFormula

end SubexponentialSAT.JetCRT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LiftRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The finite free ring used for prime-power counting

This file constructs the quotient by a monic polynomial, proves that a
positive-degree quotient retains the base ring, and constructs coefficient
reduction maps between these polynomial quotient rings.
-/

namespace SubexponentialSAT.LiftRing

noncomputable section

open Polynomial

section General

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Quotient by the principal ideal of the defining polynomial. -/
abbrev Extension (F : R[X]) := R[X] ⧸ Ideal.span {F}

/-- The polynomial quotient map. -/
def mk (F : R[X]) : R[X] →+* Extension F := Ideal.Quotient.mk _

/-- The constant-polynomial map into the extension ring. -/
def of (F : R[X]) : R →+* Extension F := (mk F).comp C

@[simp]
theorem mk_eq_zero {F q : R[X]} : mk F q = 0 ↔ F ∣ q :=
  Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

@[simp]
theorem mk_eq_mk {F q r : R[X]} : mk F q = mk F r ↔ F ∣ q - r :=
  Ideal.Quotient.eq.trans Ideal.mem_span_singleton

/-- The unique remainder is a linear function on the quotient. -/
def remainder {F : R[X]} (hF : F.Monic) : Extension F →ₗ[R] R[X] :=
  (Submodule.liftQ _ (Polynomial.modByMonicHom F)
      fun _ hq => (mem_ker_modByMonic hF).mpr (Ideal.mem_span_singleton.mp hq)).comp
    (Submodule.Quotient.restrictScalarsEquiv R
      (Ideal.span {F} : Ideal R[X])).symm.toLinearMap

@[simp]
theorem remainder_mk {F : R[X]} (hF : F.Monic) (q : R[X]) :
    remainder hF (mk F q) = q %ₘ F := rfl

theorem mk_remainder {F : R[X]} (hF : F.Monic) (x : Extension F) :
    mk F (remainder hF x) = x := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change mk F (remainder hF (mk F q)) = mk F q
  rw [remainder_mk, mk_eq_mk, modByMonic_eq_sub_mul_div,
    sub_sub_cancel_left, dvd_neg]
  exact dvd_mul_right _ _

theorem remainder_of {F : R[X]} (hF : F.Monic) (hdeg : 0 < F.natDegree)
    (a : R) : remainder hF (of F a) = C a := by
  nontriviality R
  change C a %ₘ F = C a
  apply (modByMonic_eq_self_iff hF).mpr
  exact degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hdeg)

/-- Change the coefficient ring in the quotient. -/
def reduction (φ : R →+* S) (F : R[X]) :
    Extension F →+* Extension (F.map φ) :=
  Ideal.Quotient.lift _ ((mk (F.map φ)).comp (Polynomial.mapRingHom φ))
    (by
      intro q hq
      apply mk_eq_zero.mpr
      exact map_dvd φ (Ideal.mem_span_singleton.mp hq))

@[simp]
theorem reduction_mk (φ : R →+* S) (F q : R[X]) :
    reduction φ F (mk F q) = mk (F.map φ) (q.map φ) := rfl

@[simp]
theorem reduction_of (φ : R →+* S) (F : R[X]) (a : R) :
    reduction φ F (of F a) = of (F.map φ) (φ a) := by
  change mk (F.map φ) ((C a).map φ) = _
  simp only [map_C]
  rfl

theorem remainder_reduction (φ : R →+* S) {F : R[X]} (hF : F.Monic)
    (x : Extension F) :
    remainder (hF.map φ) (reduction φ F x) = (remainder hF x).map φ := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change remainder (hF.map φ) (reduction φ F (mk F q)) =
    (remainder hF (mk F q)).map φ
  rw [reduction_mk, remainder_mk, remainder_mk, map_modByMonic φ hF]

/-- A principal kernel in the coefficient ring stays the same principal
kernel after adjoining a root of a monic polynomial. -/
theorem reduction_eq_zero_iff (φ : R →+* S) {F : R[X]} (hF : F.Monic)
    {c : R} (hker : ∀ a : R, φ a = 0 ↔ c ∣ a) (x : Extension F) :
    reduction φ F x = 0 ↔ of F c ∣ x := by
  constructor
  · intro hx
    have hm : (remainder hF x).map φ = 0 := by
      rw [← remainder_reduction φ hF x, hx, map_zero]
    have hd : C c ∣ remainder hF x := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      apply (hker _).mp
      have hi := congrArg (fun q : S[X] => q.coeff i) hm
      simpa only [coeff_map, coeff_zero] using hi
    obtain ⟨q, hq⟩ := hd
    refine ⟨mk F q, ?_⟩
    rw [← mk_remainder hF x, hq, map_mul]
    rfl
  · rintro ⟨y, rfl⟩
    rw [map_mul, reduction_of, (hker c).mpr (dvd_refl c), map_zero, zero_mul]

end General

/-- Over a field, an irreducible defining polynomial makes the concrete
polynomial quotient a field. -/
@[instance_reducible]
noncomputable def extensionField {K : Type*} [Field K] {g : K[X]}
    (hg : Irreducible g) : Field (Extension g) := by
  letI : (Ideal.span {g} : Ideal K[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hg
  exact Ideal.Quotient.field _

/-- The prime-power coefficient ring. -/
abbrev Base (p μ : ℕ) := ZMod (p ^ μ)

/-- The ring Lambda in Section 4.1. -/
abbrev Lambda (p μ : ℕ) (F : (Base p μ)[X]) := Extension F

/-- Reduction of prime-power coefficients modulo p.  Primality is not
needed for this ring homomorphism. -/
def baseReduction (p μ : ℕ) (hμ : 0 < μ) : Base p μ →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hμ)) (ZMod p)

theorem baseReduction_eq_zero_iff (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    (a : Base p μ) :
    baseReduction p μ hμ a = 0 ↔ (p : Base p μ) ∣ a := by
  constructor
  · intro ha
    have hv : (a.val : ZMod p) = 0 := by
      rw [← ZMod.natCast_zmod_val a] at ha
      simpa only [map_natCast] using ha
    obtain ⟨b, hb⟩ := (ZMod.natCast_eq_zero_iff a.val p).mp hv
    refine ⟨(b : Base p μ), ?_⟩
    rw [← Nat.cast_mul, ← hb, ZMod.natCast_zmod_val]
  · rintro ⟨b, rfl⟩
    simp only [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- The residue-ring map induced by coefficientwise reduction. -/
def residue (p μ : ℕ) (hμ : 0 < μ) (F : (Base p μ)[X]) :
    Lambda p μ F →+* Extension (F.map (baseReduction p μ hμ)) :=
  reduction (baseReduction p μ hμ) F

theorem residue_eq_zero_iff (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    {F : (Base p μ)[X]} (hF : F.Monic) (x : Lambda p μ F) :
    residue p μ hμ F x = 0 ↔ (p : Lambda p μ F) ∣ x := by
  unfold residue
  simpa only [map_natCast] using
    reduction_eq_zero_iff (baseReduction p μ hμ) hF
      (baseReduction_eq_zero_iff p μ hμ) x

theorem prime_power_zero (p μ : ℕ) (F : (Base p μ)[X]) :
    (p : Lambda p μ F) ^ μ = 0 := by
  rw [← Nat.cast_pow]
  have h : ((p ^ μ : ℕ) : Base p μ) = 0 := ZMod.natCast_self _
  have hm := congrArg (of F) h
  simpa only [map_natCast, map_zero] using hm

/-- Read the constant coefficient as its standard nonnegative residue. -/
def decodeCount (p μ : ℕ) {F : (Base p μ)[X]} (hF : F.Monic)
    (x : Lambda p μ F) : ℕ :=
  ((remainder hF x).coeff 0).val

end

end SubexponentialSAT.LiftRing

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

abbrev triple {α : Type*} (a b c : α) : Fin 3 → α :=
  fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem triple_zero {α : Type*} (a b c : α) : triple a b c 0 = a := rfl
@[simp] theorem triple_one {α : Type*} (a b c : α) : triple a b c 1 = b := rfl
@[simp] theorem triple_two {α : Type*} (a b c : α) : triple a b c 2 = c := rfl

/-- Entry to a payload parser followed by a framed operand push. -/
def pushService : Fin 20 := 15
/-- Entry to the scalar addition service on the top two framed operands. -/
def addService : Fin 20 := 16
/-- Entry to the scalar multiplication service on the top two framed operands. -/
def mulService : Fin 20 := 17
def errorExit : Fin 20 := 19

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

abbrev quadruple {α : Type*} (a b c d : α) : Fin 4 → α :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

def parserRegister : Fin 2 → Fin 3 := Fin.castAdd 1
def parserStack (i : Fin 2) : Fin 4 := if i = 0 then 0 else 3
def parserLabel : Fin 7 → Fin 17 := Fin.castAdd 10

/-- The control program retains its label range; the literal service follows it. -/
def controlLabel : Fin 20 → Fin 37 := Fin.castAdd 17
def controlStack : Fin 3 → Fin 4 := Fin.castAdd 1
def literalLabel : Fin 17 → Fin 37 := Fin.natAdd 20

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFilterReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared actual record reversal for the clause-filter storage layout. -/

namespace SubexponentialSAT.ExecClauseFilterReverse

abbrev Regs := Fin 15 → Bool

def flags (regs : Regs) (value present found : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 0 value) 1 present) 14 found

def regPort : Fin 3 → Fin 15 := ![0, 1, 14]
def stackPort : Fin 4 → Fin 16 := ![14, 9, 13, 15]

end SubexponentialSAT.ExecClauseFilterReverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFiltersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact-order clause filters on encoded formulas

The relation scanner occupies stacks 0--12. The outer record pass uses stack
13 for unread records, stack 14 for the reversed output record list, and stack
15 for the reversed current payload. Two stack transfers put a clause into the
scanner and return it to the existing frame emitter.
-/


namespace SubexponentialSAT.ExecClauseFiltersProgram

open ExecClauseRelationScan (Clause Formula Mode test)

abbrev Regs := Fin 15 → Bool

def scanStack (i : Fin 13) : Fin 16 := Fin.castAdd 3 i

def flags (regs : Regs) (value present selected : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 0 value) 1 present) 14 selected

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 0) (regs 1) (regs 14) = regs := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h14 : i = 14 <;>
    simp_all [flags]

def emitRegs : Fin 3 → Fin 15 := ![0, 1, 14]
def emitStacks : Fin 4 → Fin 16 := ![13, 9, 14, 15]

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecLiteralDedupProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual stable literal deduplication

The fixed program tests each record against the remaining records, retains its
last occurrence, and restores record order. All membership, copy, emission,
and reversal calls are concrete finite programs with measured executions.
-/

namespace SubexponentialSAT.ExecLiteralDedupProgram

def emitReg (i : Fin 3) : Fin 10 := if i = 0 then 7 else if i = 1 then 8 else 9
def emitStack (i : Fin 4) : Fin 8 :=
  if i = 0 then 0 else if i = 1 then 7 else if i = 2 then 2 else 1

def reverseStack (i : Fin 4) : Fin 8 :=
  if i = 0 then 2 else if i = 1 then 7 else if i = 2 then 0 else 1

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseDedupProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program for last-occurrence clause deduplication

The current clause is compared with the unread suffix using actual set
equivalence of its literal records. The suffix copy is cleared after each
query, and the final record reversal restores the prescribed clause order.
-/

namespace SubexponentialSAT.ExecClauseDedupProgram

open ExecClauseRelationScan (Clause Formula )
open ExecClauseFiltersProgram (Regs flags)

def workPort (i : Fin 13) : Fin 16 := Fin.castAdd 3 i

@[simp] theorem workPort_ne_source (i : Fin 13) : workPort i ≠ 13 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 13 at hv
  omega

@[simp] theorem workPort_ne_output (i : Fin 13) : workPort i ≠ 14 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 14 at hv
  omega

@[simp] theorem workPort_ne_payload (i : Fin 13) : workPort i ≠ 15 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 15 at hv
  omega

end SubexponentialSAT.ExecClauseDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCleanLiteralsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clausewise literal cleanup

Each framed clause is decoded, passed to the fixed literal-deduplication
program, and framed again. An outer record reversal restores clause order.
The finite control is independent of the input formula and its clause sizes.
-/

namespace SubexponentialSAT.ExecCleanLiteralsProgram

def bankReg (i : Fin 10) : Fin 13 := Fin.castAdd 3 i
def bankStack (i : Fin 8) : Fin 11 := Fin.natAdd 3 i

@[simp] theorem bankStack_zero : bankStack 0 = 3 := rfl
@[simp] theorem bankStack_eq_zero (i : Fin 8) : bankStack i = 3 ↔ i = 0 := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [bankStack] at hv
    omega
  · rintro rfl
    rfl

@[simp] theorem bankStack_ne_zero (i : Fin 8) : bankStack i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  simp [bankStack] at hv

@[simp] theorem bankStack_ne_one (i : Fin 8) : bankStack i ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp [bankStack] at hv
  omega

@[simp] theorem bankStack_ne_two (i : Fin 8) : bankStack i ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  simp [bankStack] at hv
  omega

def emitReg (i : Fin 3) : Fin 13 := Fin.natAdd 10 i
def emitStack (i : Fin 4) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 10 else if i = 2 then 2 else 1

def reverseStack (i : Fin 4) : Fin 11 :=
  if i = 0 then 2 else if i = 1 then 10 else if i = 2 then 0 else 1

end SubexponentialSAT.ExecCleanLiteralsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecWorklistProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Local encoded worklist updates by a fixed Boolean-stack program

The branch decision and child records are supplied as data. No formula search
or splitting callback is an instruction. Pending work, accumulated leaves, and
both child sources may have arbitrary suffixes; only the current records are
read. The five stack ports are pending, leaves, child A, child B, and scratch.
-/

namespace SubexponentialSAT.ExecWorklistProgram

def workRegs : Fin 2 → Fin 4 := ![0, 1]
def copyPorts (src dst : Fin 5) : Fin 3 → Fin 5 := ![src, dst, 4]

end SubexponentialSAT.ExecWorklistProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecBranchControllerSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual copying, child calls, and framed output for the two-child controller.
Ports 0--6 hold pending work, leaves, both outputs, parent, core, and selection.
Ports 7--22 are a reusable 16-stack child workspace. -/

namespace SubexponentialSAT.ExecBranchControllerSupport


abbrev Regs := Fin 15 → Bool
abbrev Front := Fin 7 → List Bool
abbrev Bank := Fin 16 → List Bool

def frontPort (i : Fin 7) : Fin 23 := Fin.castAdd 16 i
def bankPort (i : Fin 16) : Fin 23 := Fin.natAdd 7 i

@[simp] theorem frontPort_inj {i j : Fin 7} : frontPort i = frontPort j ↔ i = j :=
  Fin.castAdd_inj
@[simp] theorem bankPort_inj {i j : Fin 16} : bankPort i = bankPort j ↔ i = j := by
  simp [bankPort, Fin.ext_iff]

@[simp] theorem front_ne_bank (i : Fin 7) (j : Fin 16) : frontPort i ≠ bankPort j := by
  intro h
  have he := congrArg Fin.val h
  change i.val = 7 + j.val at he
  omega

@[simp] theorem bank_ne_front (i : Fin 16) (j : Fin 7) : bankPort i ≠ frontPort j :=
  (front_ne_bank j i).symm

def outputPort (i : Fin 2) : Fin 7 := ⟨2 + i.val, by omega⟩

def emitReg (i : Fin 3) : Fin 15 := Fin.castAdd 12 i

end SubexponentialSAT.ExecBranchControllerSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control increment of framed binary tuples

Tuple components are little-endian Boolean words carried by
`Encoding.encodeList id`. The finite table below skips framing bits and
increments only payload bits, with carry continuing into the next component.
Neither the number of components nor their widths enters the control table.
-/

namespace SubexponentialSAT.ExecCNFTupleOdometer

/-- Fixed-width increment. The first component reports carry beyond the word. -/
def bumpWord : List Bool → Bool × List Bool
  | [] => (true, [])
  | false :: bs => (false, true :: bs)
  | true :: bs => let next := bumpWord bs; (next.1, false :: next.2)

/-- Carry travels through successive records in their encoded order. -/
def bumpWords : List (List Bool) → Bool × List (List Bool)
  | [] => (true, [])
  | word :: words =>
    let next := bumpWord word
    if next.1 then
      let tail := bumpWords words
      (tail.1, next.2 :: tail.2)
    else (false, next.2 :: words)

@[simp] theorem bumpWord_length (word : List Bool) :
    (bumpWord word).2.length = word.length := by
  induction word with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [bumpWord, ih]

@[simp] theorem bumpWords_lengths (words : List (List Bool)) :
    (bumpWords words).2.map List.length = words.map List.length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [bumpWords]
    split <;> simp [ih]

end SubexponentialSAT.ExecCNFTupleOdometer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual overflow-controlled enumeration of framed binary tuples

The callback is fixed executable code. Every iteration invokes it and then
invokes the concrete framed odometer, including the final overflow increment.
The number and widths of records are never part of finite control.
-/

namespace SubexponentialSAT.ExecCNFTupleEnumeration

open ExecCNFTupleOdometer

variable {R S : ℕ}

/-- A mathematical witness used for coverage: exactly w little-endian bits.
The executable enumerator does not call this function or decode a rank. -/
def fixedBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => decide (n % 2 = 1) :: fixedBits w (n / 2)

end SubexponentialSAT.ExecCNFTupleEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual stable subtraction of a core from an encoded clause. Membership
tests, core copies, record emission, and order restoration use finite code. -/
namespace SubexponentialSAT.ExecPetalProgram

abbrev Regs := Fin 10 → Bool

def lowStack (i : Fin 8) : Fin 9 := Fin.castAdd 1 i

end SubexponentialSAT.ExecPetalProgram
namespace SubexponentialSAT.ExecPetalProgram

def flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 7 v) 8 p) 9 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 7) (regs 8) (regs 9) = regs := by
  funext i
  by_cases h7 : i = 7 <;> by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;>
    simp_all [flags ]

def keep (H : List (List Bool)) (bits : List Bool) : Bool := !decide (bits ∈ H)

def result {α : Type*} [DecidableEq α] (C H : List α) : List α :=
  C.filter (fun x => !decide (x ∈ H))

end SubexponentialSAT.ExecPetalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalFamilyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ExecPetalFamilyProgram
open ExecClauseRelationScan (Clause Formula )

abbrev Regs := Fin 13 → Bool

def bankReg (i : Fin 10) : Fin 13 := Fin.castAdd 3 i
def bankStack (i : Fin 9) : Fin 12 := Fin.natAdd 3 i

def emitReg : Fin 3 → Fin 13 := ![10, 11, 12]
def emitStack : Fin 4 → Fin 12 := ![0, 3, 2, 1]

def flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 10 v) 11 p) 12 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 10) (regs 11) (regs 12) = regs := by
  funext i
  by_cases h10 : i = 10 <;> by_cases h11 : i = 11 <;> by_cases h12 : i = 12 <;>
    simp_all [flags]

end SubexponentialSAT.ExecPetalFamilyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalChildProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual construction of the petal child. The core, selected family, and
parent occupy the same three ports as the core-child program. -/
namespace SubexponentialSAT.ExecPetalChildProgram
open ExecClauseRelationScan (Clause Formula )
open ExecClauseFiltersProgram

def familyReg (i : Fin 13) : Fin 15 := Fin.castAdd 2 i
def familyStack : Fin 12 → Fin 16 := ![0, 15, 14, 1, 2, 3, 4, 5, 6, 7, 8, 9]

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Factor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean-valued factor systems

This module formalizes the finite sum of products in Sections 2 and 3 of the
candidate exposition.  Factor tables have genuine local domains, so dependence
only on a scope is enforced by their type.  Counting is an actual finite sum of
natural-number products.  No running-time assertion is made here.
-/

namespace SubexponentialSAT.Factor

open scoped BigOperators

/-- A finite-scope pattern.  Finiteness of the index types is requested only by
those constructions which enumerate them. -/
structure Pattern (V E : Type*) [DecidableEq V] where
  scope : E → Finset V

end SubexponentialSAT.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_FiniteField
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The finite extension and its defining polynomial

For each prime `p` and positive `h`, the field is constructed as mathlib's
`GaloisField p h`. Its size and extension degree are proved, not assumed.
A primitive element provides a monic irreducible polynomial of degree `h`,
and its polynomial quotient is identified with the same field.

The chosen primitive element and finite enumeration are noncomputable choices
of fixed finite objects. This module proves their mathematical existence and
properties; it does not claim an executable field-construction complexity bound.
-/

noncomputable section
namespace SubexponentialSAT.FiniteField

open Polynomial

/-- The actual finite extension used for interpolation nodes. -/
abbrev E (p h : ℕ) [Fact p.Prime] := GaloisField p h

instance fieldFintype (p h : ℕ) [Fact p.Prime] : Fintype (E p h) :=
  Fintype.ofFinite _

variable (p h : ℕ) [Fact p.Prime]

theorem extension_finrank (hh : h ≠ 0) :
    Module.finrank (ZMod p) (E p h) = h :=
  GaloisField.finrank p hh

/-- A primitive element of the constructed field, chosen once for `p,h`. -/
def primitiveElement : E p h :=
  (Field.exists_primitive_element_of_finite_top (ZMod p) (E p h)).choose

theorem primitiveElement_adjoin :
    IntermediateField.adjoin (ZMod p) ({primitiveElement p h} : Set (E p h)) = ⊤ :=
  (Field.exists_primitive_element_of_finite_top (ZMod p) (E p h)).choose_spec

theorem primitiveElement_integral : IsIntegral (ZMod p) (primitiveElement p h) :=
  IsIntegral.of_finite (ZMod p) _

/-- The monic irreducible polynomial defining the same extension. -/
def definingPolynomial : (ZMod p)[X] :=
  minpoly (ZMod p) (primitiveElement p h)

theorem definingPolynomial_monic : (definingPolynomial p h).Monic :=
  minpoly.monic (primitiveElement_integral p h)

theorem definingPolynomial_irreducible : Irreducible (definingPolynomial p h) :=
  minpoly.irreducible (primitiveElement_integral p h)

theorem definingPolynomial_natDegree (hh : h ≠ 0) :
    (definingPolynomial p h).natDegree = h := by
  change (minpoly (ZMod p) (primitiveElement p h)).natDegree = h
  rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p)
    (primitiveElement p h)).mp (primitiveElement_adjoin p h)]
  exact extension_finrank p h hh

/-- In particular the needed defining polynomial exists for every positive
extension degree; it is not an assumption about the construction. -/
theorem exists_monic_irreducible (hh : h ≠ 0) :
    ∃ f : (ZMod p)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = h :=
  ⟨definingPolynomial p h, definingPolynomial_monic p h,
    definingPolynomial_irreducible p h, definingPolynomial_natDegree p h hh⟩

end SubexponentialSAT.FiniteField

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_FrontendProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual initialization of the canonical SAT input

The nineteen-label program splits the variable-count header and counts its
unary marks into a binary stack word. The untouched encoded CNF body remains
on stack 0. All growing values live on Boolean stacks, not in finite control.
-/

namespace SubexponentialSAT.FrontendProgram

/-- Body, unary work, binary variable count, and counter scratch. -/
def storage (body unary binary scratch : List Bool) : Fin 4 → List Bool :=
  fun i => if i = 0 then body else if i = 1 then unary else if i = 2 then binary else scratch

@[simp] theorem storage_zero (a b c d : List Bool) : storage a b c d 0 = a := rfl
@[simp] theorem storage_one (a b c d : List Bool) : storage a b c d 1 = b := rfl
@[simp] theorem storage_two (a b c d : List Bool) : storage a b c d 2 = c := rfl
@[simp] theorem storage_three (a b c d : List Bool) : storage a b c d 3 = d := rfl

/-- The direct sum of the two checked instruction bounds. -/
def initializeBound (n : ℕ) : ℕ := (4 * n + 4) + (n * (8 * n + 10) + 3)

end SubexponentialSAT.FrontendProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Incidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite factor incidence bounds

Scopes are finite sets: a coordinate occurs at most once in any single factor,
while distinct factors may have equal scopes.  The results below count actual
incidences, bound the neighbors sharing a factor, and account for packing
Boolean variables into chunks followed by one unary validity factor per chunk.
-/

namespace SubexponentialSAT.Incidence

open scoped BigOperators

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

/-- The factors whose scope contains a given coordinate. -/
def incident (scope : E → Finset V) (v : V) : Finset E :=
  Finset.univ.filter fun e => v ∈ scope e

/-- Number of distinct factors containing a coordinate. -/
def degree (scope : E → Finset V) (v : V) : ℕ :=
  (incident scope v).card

omit [DecidableEq E] in
@[simp] theorem mem_incident (scope : E → Finset V) (v : V) (e : E) :
    e ∈ incident scope v ↔ v ∈ scope e := by
  simp [incident]

omit [DecidableEq E] in
theorem degree_eq_sum (scope : E → Finset V) (v : V) :
    degree scope v = ∑ e, if v ∈ scope e then 1 else 0 := by
  simp [degree, incident]

end SubexponentialSAT.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LocalExpectation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Conditional expectations of local objectives

A local term is evaluated only on the still-unassigned coordinates in its
support. The resulting evaluator is proved equal to exhaustive conditional
expectation. Instrumentation counts calls to local terms, separately from
arithmetic and data-structure costs.
-/

namespace SubexponentialSAT.LocalExpectation

open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

/-- A term reads only the coordinates in `support`. -/
def DependsOn (support : Finset I) (f : (I → W) → ℚ) : Prop :=
  ∀ ω ω', (∀ i ∈ support, ω i = ω' i) → f ω = f ω'

/-- Indices still free and actually read by a local term. -/
def active (support : Finset I) (remaining : List I) : List I :=
  remaining.filter (fun i => decide (i ∈ support))

/-- A sum of local terms with a constant offset, including the collision form
of the sum of squared type-count deviations. -/
def objective (terms : List J) (f : J → (I → W) → ℚ) (offset : ℚ)
    (ω : I → W) : ℚ := (terms.map (fun j => f j ω)).sum - offset

/-- A repetition-free remaining-index list has at most `support.card` active
indices. No bound on the total number of remaining indices is needed. -/
theorem active_length_le (support : Finset I) (remaining : List I)
    (hremaining : remaining.Nodup) :
    (active support remaining).length ≤ support.card := by
  have hn : (active support remaining).Nodup := hremaining.filter _
  rw [← List.toFinset_card_of_nodup hn]
  apply Finset.card_le_card
  intro i hi
  have hi' : i ∈ active support remaining := by simpa using hi
  exact of_decide_eq_true (List.mem_filter.mp hi').2

section Sequential

/-- Decode the reverse list of chosen values into numbered word variables. -/
def decode (default : W) : List W → ℕ → W
  | [] => fun _ => default
  | w :: fixed => Function.update (decode default fixed) fixed.length w

end Sequential

section Reindex

/-- Numbering through an explicit enumeration, using the supplied decidable
equality uniformly across generic and concrete index types. -/
def indexCode (indices : List I) (i : I) : ℕ := indices.idxOf i

/-- Pull a local term back to numbered coordinates. -/
def reindexTerm (code : I → ℕ) (f : (I → W) → ℚ) (ξ : ℕ → W) : ℚ :=
  f (fun i => ξ (code i))

theorem idxOf_injective (indices : List I) (hcomplete : ∀ i, i ∈ indices) :
    Function.Injective (fun i => indexCode indices i) := by
  intro i j h
  exact (List.idxOf_inj (hcomplete i)).mp h

theorem map_idxOf_eq_range (indices : List I) (hn : indices.Nodup) :
    indices.map (fun i => indexCode indices i) = List.range indices.length := by
  apply List.ext_getElem
  · simp
  · intro n hn₁ hn₂
    simp only [List.getElem_map, List.getElem_range]
    exact hn.idxOf_getElem n (by simpa using hn₁)

end Reindex

end SubexponentialSAT.LocalExpectation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LocalSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The four-state involution in the interpolation layout

This file constructs the operator rather than assuming a spectral decomposition.
The only characteristic hypothesis on the field is that `2 ≠ 0`.
-/

namespace SubexponentialSAT.LocalSpectrum

abbrev PairState := Bool × Bool

/-- The local permutation swaps `00` and `11`, fixing `01` and `10`. -/
def swapPair (x : PairState) : PairState := (!x.2, !x.1)

@[simp] theorem swapPair_involutive (x : PairState) :
    swapPair (swapPair x) = x := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> rfl

section Field

variable (K : Type*) [Field K]

/-- Pullback by the actual four-state permutation. -/
def localMap : Module.End K (PairState → K) where
  toFun f x := f (swapPair x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem localMap_apply (f : PairState → K) (x : PairState) :
    localMap K f x = f (swapPair x) := rfl

@[simp] theorem localMap_involutive (f : PairState → K) :
    localMap K (localMap K f) = f := by
  ext x
  simp

end Field

end SubexponentialSAT.LocalSpectrum

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

/-- One complete binary subtraction cell. -/
def differenceBit (a b borrow : Bool) : Bool := (a ^^ b) ^^ borrow

def borrowBit (a b borrow : Bool) : Bool :=
  ((!a) && (b || borrow)) || (b && borrow)

/-- Fixed-width subtraction. Its specifications require equal input widths.
The unmatched cases only make the executable function total. -/
def subCarry : Bool → List Bool → List Bool → List Bool × Bool
  | c, [], _ => ([], c)
  | c, _ :: _, [] => ([], c)
  | c, a :: as, b :: bs =>
    let tail := subCarry (borrowBit a b c) as bs
    (differenceBit a b c :: tail.1, tail.2)

theorem subCarry_length (c : Bool) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    (subCarry c xs ys).1.length = xs.length := by
  induction xs generalizing ys c with
  | nil => simp [subCarry]
  | cons a as ih =>
    cases ys with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simpa [subCarry] using congrArg Nat.succ (ih (borrowBit a b c) bs hlen)

/-- Copy the given bits into a word with the requested shape, adding zero
bits at the most significant end. No lengths are calculated by the routine. -/
def padTo : List Bool → List Bool → List Bool
  | [], _ => []
  | _ :: shape, [] => false :: padTo shape []
  | _ :: shape, b :: bs => b :: padTo shape bs

theorem padTo_length (shape xs : List Bool) :
    (padTo shape xs).length = shape.length := by
  induction shape generalizing xs with
  | nil => rfl
  | cons b shape ih =>
    cases xs <;> simp [padTo, ih]

/-- Shift the current remainder, then use one fixed-width subtraction and
its final borrow bit to select the new remainder. -/
def shiftReduce (modulus remainder : List Bool) (b : Bool) : List Bool :=
  let shifted := b :: remainder
  let difference := subCarry false shifted (padTo shifted modulus)
  if difference.2 then shifted else difference.1

theorem shiftReduce_length (m r : List Bool) (b : Bool) :
    (shiftReduce m r b).length = r.length + 1 := by
  dsimp only [shiftReduce]
  split
  · rfl
  · simpa using subCarry_length false (b :: r) (padTo (b :: r) m)
      (padTo_length (b :: r) m).symm

/-- Long division processes the most significant input bit first by recursion
on the tail of a little-endian word. The remainder width grows harmlessly. -/
def reduce (modulus : List Bool) : List Bool → List Bool
  | [] => padTo modulus []
  | b :: bs => shiftReduce modulus (reduce modulus bs) b

theorem reduce_length (m xs : List Bool) :
    (reduce m xs).length = m.length + xs.length := by
  induction xs with
  | nil => simp [reduce, padTo_length]
  | cons b bs ih => simp [reduce, shiftReduce_length, ih, Nat.add_assoc]

/-! A measured finite-control subtraction transducer. -/

/-! Instrumentation with events carrying only finitely many Boolean values.
The logs record every padding/subtraction cell and each shift/selection.
They are not a primitive-machine simulation certificate. -/

inductive Event where
  | pad (bit : Bool)
  | subtract (left right borrow : Bool)
  | shift (bit : Bool)
  | select (borrow : Bool)
  deriving DecidableEq

def padEvents : List Bool → List Bool → List Event
  | [], _ => []
  | _ :: shape, [] => Event.pad false :: padEvents shape []
  | _ :: shape, b :: bs => Event.pad b :: padEvents shape bs

def subEvents : Bool → List Bool → List Bool → List Event
  | _, [], _ => []
  | _, _ :: _, [] => []
  | c, a :: as, b :: bs =>
    Event.subtract a b c :: subEvents (borrowBit a b c) as bs

def shiftLogged (m r : List Bool) (b : Bool) : List Bool × List Event :=
  let shifted := b :: r
  let padded := padTo shifted m
  let difference := subCarry false shifted padded
  (if difference.2 then shifted else difference.1,
    [Event.shift b] ++ padEvents shifted m ++ subEvents false shifted padded ++
      [Event.select difference.2])

theorem shiftLogged_value (m r : List Bool) (b : Bool) :
    (shiftLogged m r b).1 = shiftReduce m r b := rfl

/-- A complete binary-reduction execution with its finite-operation log. -/
def reduceLogged (m : List Bool) : List Bool → List Bool × List Event
  | [] => (padTo m [], padEvents m [])
  | b :: bs =>
    let tail := reduceLogged m bs
    let head := shiftLogged m tail.1 b
    (head.1, tail.2 ++ head.2)

theorem reduceLogged_value (m xs : List Bool) :
    (reduceLogged m xs).1 = reduce m xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [reduceLogged, shiftLogged_value, ih, reduce]

/-! Modular addition and multiplication combine the concrete binary
arithmetic runs with the concrete long-division run. -/

/-! An explicit finite ring expression for geometric correction. Its
operation-node count is a ring-operation bound, separately from bit costs. -/

end SubexponentialSAT.ModularArithmetic

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

open SubexponentialSAT.ModularArithmetic

/-- A full subtractor using only the Boolean gates in BitProgram.
The two product terms are disjoint, so XOR implements their disjunction. -/
theorem borrowBit_gate_form (a b c : Bool) :
    SubexponentialSAT.ModularArithmetic.borrowBit a b c =
      (((!a) && b) ^^ ((!(a ^^ b)) && c)) := by
  cases a <;> cases b <;> cases c <;> decide

abbrev operandStacks (left right output : List Bool) (k : Fin 3) : List Bool :=
  if k = 0 then left else if k = 1 then right else output

@[simp] theorem operandStacks_left (left right output : List Bool) :
    operandStacks left right output 0 = left := rfl

@[simp] theorem operandStacks_right (left right output : List Bool) :
    operandStacks left right output 1 = right := rfl

@[simp] theorem operandStacks_output (left right output : List Bool) :
    operandStacks left right output 2 = output := rfl

theorem stacks_update_left (left right output next : List Bool) :
    Function.update (operandStacks left right output) 0 next =
      operandStacks next right output := by
  funext k
  fin_cases k <;> simp [operandStacks]

theorem stacks_update_right (left right output next : List Bool) :
    Function.update (operandStacks left right output) 1 next =
      operandStacks left next output := by
  funext k
  fin_cases k <;> simp [operandStacks]

theorem stacks_update_output (left right output next : List Bool) :
    Function.update (operandStacks left right output) 2 next =
      operandStacks left right next := by
  funext k
  fin_cases k <;> simp [operandStacks]

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

abbrev wideStacks (saved left right output : List Bool) (k : Fin 5) : List Bool :=
  if k = 0 then saved else if k = 1 then right else if k = 2 then left
  else if k = 3 then output else []

def conditionalDifference (candidate modulus : List Bool) : List Bool :=
  let d := subCarry false candidate modulus
  if d.2 then candidate else d.1

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

open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms

/-- The mathematical fold executed by the loop on its MSB-first input stack. -/
def reduceFrom (modulus candidate : List Bool) : List Bool → List Bool
  | [] => candidate
  | b :: bs => reduceFrom modulus (shiftReduce modulus candidate b) bs

theorem reduceFrom_append (modulus candidate xs ys : List Bool) :
    reduceFrom modulus candidate (xs ++ ys) =
      reduceFrom modulus (reduceFrom modulus candidate xs) ys := by
  induction xs generalizing candidate with
  | nil => rfl
  | cons b bs ih => exact ih (shiftReduce modulus candidate b)

end SubexponentialSAT.ModularDivisionPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularQuotientPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Binary quotient and remainder from a fixed finite Boolean-stack program. -/

namespace SubexponentialSAT.ModularQuotientPrograms

open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularDivisionPrograms

def quotientPorts : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]

end SubexponentialSAT.ModularQuotientPrograms

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

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

theorem add_cost_bound (m a b s k : ℕ) (hs : s ≤ k + 1) (hk : k ≤ a + b) :
    2 + 16 * (k + 1) + (6 * s + 6) + 100 * (m + s + 1) ^ 2 ≤
      600 * (m + a + b + 1) ^ 2 := by
  let T := m + a + b + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hsT : s ≤ T := by dsimp [T]; omega
  have hkT : k + 1 ≤ T := by dsimp [T]; omega
  have hn : m + s + 1 ≤ 2 * T := by dsimp [T] at *; omega
  have hlinear : 2 + 16 * (k + 1) + (6 * s + 6) ≤ 30 * T := by omega
  have hquadratic : 100 * (m + s + 1) ^ 2 ≤ 400 * T ^ 2 := by
    calc
      _ ≤ 100 * (2 * T) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2)
      _ = _ := by ring
  have hTsq : T ≤ T ^ 2 := by
    have h := Nat.mul_le_mul_left T hT
    simpa only [Nat.mul_one, pow_two] using h
  change _ ≤ 600 * T ^ 2
  omega


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

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

/-! ## Restore a runtime-specified output width -/

open SubexponentialSAT.ModularPrograms

theorem update_operand_left (left right output next : List Bool) :
    Function.update (operandStacks left right output) 0 next =
      operandStacks next right output := by
  funext i; fin_cases i <;> simp [operandStacks]

abbrev normalizationState (input shape output modulus : List Bool) : Fin 8 → List Bool :=
  ![input, [], output, [], [], modulus, [], shape]

theorem normalizationState_apply (input shape output modulus : List Bool) :
    normalizationState input shape output modulus = fun i =>
      if i = 0 then input else if i = 2 then output else
      if i = 5 then modulus else if i = 7 then shape else [] := by
  first | done | (funext i; fin_cases i <;> rfl)

theorem word_cost_bound (m x y o B : ℕ)
    (hx : x = B) (hy : y = B) (hm : m ≤ B + 1) (ho : o ≤ m + x + y + 1) :
    600 * (m + x + y + 1) ^ 2 + 14 * x + 2 * o + 14 ≤
      6000 * (B + 1) ^ 2 := by
  have hs : m + x + y + 1 ≤ 3 * (B + 1) := by omega
  have hq : 600 * (m + x + y + 1) ^ 2 ≤ 5400 * (B + 1) ^ 2 := by
    calc
      _ ≤ 600 * (3 * (B + 1)) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
      _ = _ := by ring
  have hl : 14 * x + 2 * o + 14 ≤ 20 * (B + 1) := by omega
  have hsq : B + 1 ≤ (B + 1) ^ 2 := by
    have h := Nat.mul_le_mul_left (B + 1) (Nat.le_add_left 1 B)
    simpa only [Nat.mul_one, pow_two] using h
  omega

end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_MulticolorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multicolor universal types and consistent incidence slots

The number `r` of colors is an explicit natural parameter throughout. No
finiteness instance or cardinality identity treats it as a fixed constant.
The joint fiber uses a head color different from the selected slot color,
as required by Sections 3.1 and 3.4 of the subexponential construction.
-/

namespace SubexponentialSAT.MulticolorTypes

abbrev Word (r Q : ℕ) := Fin Q → Fin r

end SubexponentialSAT.MulticolorTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_PowerPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Variable exponentiation with finite Boolean control

The exponent is a binary stack word.  The multiplication callback below uses
only fixed finite programs and leaves the countdown ports untouched.
-/

namespace SubexponentialSAT.PowerPrograms

open SubexponentialSAT.BinaryArithmetic

abbrev Regs := Fin 8 → Bool

end SubexponentialSAT.PowerPrograms

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

/-- Fixed-width little-endian binary expansion. -/
def fixedBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | B + 1, n => decide (n % 2 = 1) :: fixedBits B (n / 2)

@[simp] theorem fixedBits_length (B n : ℕ) : (fixedBits B n).length = B := by
  induction B generalizing n with
  | zero => rfl
  | succ B ih => simp [fixedBits, ih]

def baseWidth (p μ : ℕ) : ℕ := μ * (Nat.log 2 p + 1)

theorem modulus_le_width (p μ : ℕ) : p ^ μ ≤ 2 ^ baseWidth p μ := by
  calc
    p ^ μ ≤ (2 ^ (Nat.log 2 p + 1)) ^ μ :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two p)) _
    _ = 2 ^ baseWidth p μ := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _

section ResidueEncoding

variable (p μ : ℕ) [Fact p.Prime]

/-- Canonical binary encoding of a base coefficient. -/
def encodeBase (x : ZMod (p ^ μ)) : List Bool := fixedBits (baseWidth p μ) x.val

omit [Fact (Nat.Prime p)] in
@[simp] theorem encodeBase_length (x : ZMod (p ^ μ)) :
    (encodeBase p μ x).length = baseWidth p μ := fixedBits_length _ _

end ResidueEncoding

/-- Bounded list operations restore the canonical output width. -/
def normalizeBits (B : ℕ) (xs : List Bool) : List Bool :=
  ModularArithmetic.padTo (List.replicate B false) (xs.take B)

@[simp] theorem normalizeBits_length (B : ℕ) (xs : List Bool) :
    (normalizeBits B xs).length = B := by simp [normalizeBits, ModularArithmetic.padTo_length]

end SubexponentialSAT.SubexpLiftRing

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

structure Quad (A : Type*) where
  c0 : A
  c1 : A
  c2 : A
  c3 : A
  deriving DecidableEq

namespace Quad

def map {A B : Type*} (f : A → B) (a : Quad A) : Quad B :=
  ⟨f a.c0, f a.c1, f a.c2, f a.c3⟩

@[simp] theorem map_map {A B C : Type*} (g : B → C) (f : A → B) (a : Quad A) :
    (a.map f).map g = a.map (g ∘ f) := rfl

end Quad

/-! These loops execute exactly the displayed scalar calls. -/

end SubexponentialSAT.SubexpQuarticRing

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

open SubexpLiftRing SubexpQuarticRing

variable (p μ : ℕ)
  [Fact p.Prime]

def wordCost (B : ℕ) : ℕ := 6000 * (B+1)^2 + 31*B + 25

end SubexponentialSAT.SubexpFlatAdd

end OAI.Algorithms
end


