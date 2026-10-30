-- Prove2me | Definitions.Def_OAIQ081S000
-- name    : OAIQ081S000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:22:18.309877+00:00
-- url     : https://prove2.me/theorems/26f72432-5fab-4942-8561-5f410a56a9a7
-- title:
--   Definitions bundle OAIQ081S000 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 117 declarations of OpenAI's Lean: 65 definitions, 11 inductive types or structures and 41 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.compile`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.eval`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.map`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.product`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.size`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.sum`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Instr`, `OAI.Algorithms.SubexponentialSAT.Algorithm.WeightedTerm`, `OAI.Algorithms.SubexponentialSAT.Algorithm.WeightedTerm.expression`, `OAI.Algorithms.SubexponentialSAT.Annihilation.extendRow`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.Data`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.Ports`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.Valid`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.addAt`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.addPorts`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.addRaw`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.addReady`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.afterCopy`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.copyAt`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Add.Regs`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Add.littleEndianProgram`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Add.program`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.Regs`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Instr`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.BitProgram.execInstr`, `OAI.Algorithms.SubexponentialSAT.BitProgram.initial`, `OAI.Algorithms.SubexponentialSAT.BitProgram.readRegs`, `OAI.Algorithms.SubexponentialSAT.BitProgram.step`, `OAI.Algorithms.SubexponentialSAT.BitProgram.terminal`, `OAI.Algorithms.SubexponentialSAT.ListRegisterProgram.Run`, `OAI.Algorithms.SubexponentialSAT.ProgramLinking.embedCfg`, `OAI.Algorithms.SubexponentialSAT.ProgramLinking.liftProgram`, `OAI.Algorithms.SubexponentialSAT.ProgramLinking.link`, `OAI.Algorithms.SubexponentialSAT.ProgramLinking.linkInto`, `OAI.Algorithms.SubexponentialSAT.ProgramLinking.relabelCfg`, `OAI.Algorithms.SubexponentialSAT.ProgramLinking.relocateInstr` and 36 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_Algorithm`, `SubexponentialSAT_Annihilation`, `SubexponentialSAT_ArithmeticCalls`, `SubexponentialSAT_BinaryPrograms`, `SubexponentialSAT_BitProgram`, `SubexponentialSAT_Computation`, `SubexponentialSAT_LeanCompat`, `SubexponentialSAT_ListRegisterProgram`, `SubexponentialSAT_ProgramLinking`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_StackRoutines`, `SubexponentialSAT_StructuredCalls`, `SubexponentialSAT_StructuredProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S034`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S041`, `OAIQ081S042` and `OAIQ081S043`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LeanCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe u v

/-!
Compatibility names for the Lean and Mathlib version used by this repository.
These are direct aliases of renamed library lemmas; they do not change any
definitions or proof obligations in the imported development.
-/

namespace List

theorem map_coe_finRange (n : ℕ) : (finRange n).map Fin.val = range n := by
  rw [← ofFn_eq_map]
  simp [ofFn_eq_pmap]

end List

namespace Function

theorem update_same {α : Sort u} {β : α → Sort v} [DecidableEq α]
    (a : α) (value : β a) (f : (a : α) → β a) :
    update f a value a = value :=
  update_self a value f

theorem update_noteq {α : Sort u} {β : α → Sort v} [DecidableEq α]
    {a a' : α} (h : a ≠ a') (value : β a') (f : (a : α) → β a) :
    update f a' value a = f a :=
  update_of_ne h value f

end Function

namespace Nat

theorem le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} :
    x ≤ b ^ y ↔ clog b x ≤ y :=
  (clog_le_iff_le_pow hb).symm

theorem pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} :
    b ^ y < x ↔ y < clog b x :=
  (lt_clog_iff_pow_lt hb).symm

end Nat
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

namespace Trace

variable {α : Type u} {step : α → Option α} {n m : ℕ} {a b c : α}

theorem iterate (h : Trace step n a b) :
    (fun s : Option α => s.bind step)^[n] (some a) = some b := by
  induction h with
  | refl => rfl
  | cons hs ht ih =>
      simpa only [Function.iterate_succ_apply, Option.bind_some, hs] using ih

theorem of_iterate
    (h : (fun s : Option α => s.bind step)^[n] (some a) = some b) :
    Trace step n a b := by
  induction n generalizing a with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at h
      subst b
      exact .refl a
  | succ n ih =>
      cases hs : step a with
      | none =>
          have hn :
              (fun s : Option α => s.bind step)^[n] none = none :=
            Function.iterate_fixed rfl n
          simp only [Function.iterate_succ_apply, Option.bind_some, hs, hn] at h
          cases h
      | some a' =>
          apply Trace.cons hs
          apply ih
          simpa only [Function.iterate_succ_apply, Option.bind_some, hs] using h

theorem trans (h₁ : Trace step n a b) (h₂ : Trace step m b c) :
    Trace step (n + m) a c := by
  apply of_iterate
  rw [Nat.add_comm, Function.iterate_add_apply, h₁.iterate, h₂.iterate]

end Trace

end SubexponentialSAT.Computation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Algorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable separated arithmetic kernels

The arithmetic expressions and their postfix compiler in this file are data.
The evaluator contains no choice, no decision of a semantic proposition, and no
enumeration of the Cartesian product of the two inner lists.  Its instruction
counts are proved by actual transition traces.  An arithmetic instruction is
not a primitive bit-machine instruction: refining the supplied coefficient
operations to the latter remains a separate obligation.
-/

namespace SubexponentialSAT.Algorithm

open scoped BigOperators

universe u

/-- Finite syntax for computations in the retained coefficient algebra. -/
inductive Expr (R : Type u) where
  | lit : R → Expr R
  | add : Expr R → Expr R → Expr R
  | mul : Expr R → Expr R → Expr R

namespace Expr

variable {R : Type u}

/-- Structural evaluation using the supplied, executable coefficient operations. -/
def eval [Add R] [Mul R] : Expr R → R
  | .lit x => x
  | .add e f => eval e + eval f
  | .mul e f => eval e * eval f

/-- Number of postfix instructions, including explicit coefficient loads. -/
def size : Expr R → ℕ
  | .lit _ => 1
  | .add e f => size e + size f + 1
  | .mul e f => size e + size f + 1

/-- A finite summation program. Its syntax contains each input exactly once. -/
def sum [Zero R] : List (Expr R) → Expr R
  | [] => .lit 0
  | e :: es => .add e (sum es)

/-- A finite group product; all factor computations remain explicit syntax. -/
def product [One R] : List (Expr R) → Expr R
  | [] => .lit 1
  | e :: es => .mul e (product es)

@[simp] theorem eval_sum [AddMonoid R] [Mul R] (es : List (Expr R)) :
    (sum es).eval = (es.map eval).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sum, eval, ih]

@[simp] theorem eval_product [Monoid R] [Add R] (es : List (Expr R)) :
    (product es).eval = (es.map eval).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [product, eval, ih]

/-- Change only coefficient representations, leaving the program unchanged. -/
def map {S : Type*} (f : R → S) : Expr R → Expr S
  | .lit r => .lit (f r)
  | .add e g => .add (e.map f) (g.map f)
  | .mul e g => .mul (e.map f) (g.map f)

@[simp] theorem size_map {S : Type*} (f : R → S) (e : Expr R) :
    (e.map f).size = e.size := by
  induction e with
  | lit => rfl
  | add e g he hg => simp [map, size, he, hg]
  | mul e g he hg => simp [map, size, he, hg]

end Expr

/-- The three actual instructions of the arithmetic kernel. -/
inductive Instr (R : Type u) where
  | push : R → Instr R
  | add : Instr R
  | mul : Instr R

namespace Expr

variable {R : Type u}

/-- Postfix compilation is structural and contains no interpreter oracle. -/
def compile : Expr R → List (Instr R)
  | .lit x => [.push x]
  | .add e f => compile e ++ compile f ++ [.add]
  | .mul e f => compile e ++ compile f ++ [.mul]

@[simp] theorem length_compile (e : Expr R) : e.compile.length = e.size := by
  induction e with
  | lit => rfl
  | add e f he hf => simp [compile, size, he, hf, Nat.add_assoc]
  | mul e f he hf => simp [compile, size, he, hf, Nat.add_assoc]

end Expr

/-! ## Constructive output-sensitive monomial enumeration -/

/-! ## Concrete dense coefficients and the arithmetic-machine backend -/

/-! ## Finite coefficient extraction after moment execution -/

/-- One weighted group evaluation. The group itself is executable syntax,
so its computation cost is included rather than assumed to be one operation. -/
structure WeightedTerm (R : Type u) where
  weight : R
  group : Expr R

namespace WeightedTerm

variable {R : Type u}

def expression (t : WeightedTerm R) : Expr R := .mul (.lit t.weight) t.group

@[simp] theorem expression_eval [Add R] [Mul R] (t : WeightedTerm R) :
    t.expression.eval = t.weight * t.group.eval := rfl

@[simp] theorem expression_size (t : WeightedTerm R) :
    t.expression.size = t.group.size + 2 := by
  simp [expression, Expr.size]; omega

end WeightedTerm

end SubexponentialSAT.Algorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Annihilation of the incidence-specific row paths

Section 5.3 is a finite linear-algebra statement once the row evaluations and
matrix support property are known.  This file proves that statement for actual
matrices and vectors, and specializes it to the universal type block.  It does
not assume the annihilation conclusion as a hypothesis.
-/

namespace SubexponentialSAT.Annihilation

open scoped BigOperators
open Matrix

variable {V K : Type*} [Fintype V] [DecidableEq V] [Ring K]

/-- Extend a row indexed by a subset by zero on its complement. -/
noncomputable def extendRow (J : Set V) (m : J → K) : V → K := by
  classical
  exact fun y => if hy : y ∈ J then m ⟨y, hy⟩ else 0

omit [Fintype V] [DecidableEq V] in
@[simp] theorem extendRow_mem (J : Set V) (m : J → K) (y : J) :
    extendRow J m y = m y := by
  classical
  simp [extendRow, y.property]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem extendRow_not_mem (J : Set V) (m : J → K)
    (y : V) (hy : y ∉ J) : extendRow J m y = 0 := by
  classical
  simp [extendRow, hy]

omit [DecidableEq V] in
/-- Zero extension preserves the sum pairing with a restricted vector. -/
theorem extendRow_dotProduct (J : Set V) [Fintype J] (m : J → K) (r : V → K) :
    extendRow J m ⬝ᵥ r = m ⬝ᵥ (fun y : J => r y) := by
  classical
  change (∑ y : V, extendRow J m y * r y) = ∑ y : J, m y * r y
  calc
    (∑ y : V, extendRow J m y * r y) =
        ∑ y ∈ J.toFinset, extendRow J m y * r y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      have hyJ : y ∉ J := by simpa using hy
      simp [extendRow, hyJ]
    _ = ∑ y : J, extendRow J m y * r y :=
      Finset.sum_subtype J.toFinset (fun _ => Set.mem_toFinset) _
    _ = ∑ y : J, m y * r y := by
      apply Finset.sum_congr rfl
      intro y _
      simp

omit [Fintype V] [DecidableEq V] in
/-- A row supported on `Y` stays supported on `Y` after zero extension. -/
theorem extendRow_eq_zero_outside (J : Set V) (Y : Finset V) (m : J → K)
    (hm : ∀ y : J, (y : V) ∉ Y → m y = 0)
    (y : V) (hy : y ∉ Y) : extendRow J m y = 0 := by
  classical
  by_cases hj : y ∈ J
  · simp [extendRow, hj, hm ⟨y, hj⟩ hy]
  · simp [extendRow, hj]

/-- If the selected coordinate is off the active side, all terms vanish.
Only correction values on the active side and inside `Y` need to be specified. -/
theorem annihilates_of_head_outside (S : Set V) (Y : Finset V)
    (u : V) (c r : V → K)
    (hu : u ∉ S)
    (hr : ∀ y, y ∉ S → r y = 0)
    (hc : ∀ y, y ∉ Y → c y = 0)
    (hcS : ∀ y, y ∈ S → y ∈ Y → c y = 0) :
    (Pi.single u 1 + c) ⬝ᵥ r = 0 := by
  rw [add_dotProduct, single_dotProduct, one_mul, hr u hu, zero_add]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hyS : y ∈ S
  · by_cases hyY : y ∈ Y
    · rw [hcS y hyS hyY, zero_mul]
    · rw [hc y hyY, zero_mul]
  · rw [hr y hyS, mul_zero]

/-- On the active side, the correction agrees with a negative matrix row.
The support hypothesis supplies all omitted correction coordinates. -/
theorem annihilates_of_head_inside (S J : Set V) (Y : Finset V)
    [Fintype J] (M : Matrix J J K) (u : J) (c r : V → K)
    (hr : ∀ y, y ∉ S → r y = 0)
    (hc : ∀ y, y ∉ Y → c y = 0)
    (hm : ∀ y : J, (y : V) ∉ Y → M u y = 0)
    (hcS : ∀ y, y ∈ S → y ∈ Y → c y = -extendRow J (M u) y)
    (hfix : M *ᵥ (fun y : J => r y) = fun y : J => r y) :
    (Pi.single (u : V) 1 + c) ⬝ᵥ r = 0 := by
  classical
  have hpair : c ⬝ᵥ r = (-extendRow J (M u)) ⬝ᵥ r := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases hyS : y ∈ S
    · by_cases hyY : y ∈ Y
      · rw [hcS y hyS hyY]
        rfl
      · simp only [hc y hyY, Pi.neg_apply,
          extendRow_eq_zero_outside J Y (M u) hm y hyY, neg_zero, zero_mul]
    · rw [hr y hyS]
      simp
  rw [add_dotProduct, single_dotProduct, one_mul, hpair, neg_dotProduct,
    extendRow_dotProduct]
  have huFix := congrFun hfix u
  change r u + -(M *ᵥ (fun y : J => r y)) u = 0
  rw [huFix, add_neg_cancel]

section ScalarExtension

variable {L J : Type*} [Ring L] [Fintype J]

/-- A fixed-vector equation survives a coefficient ring homomorphism. No
injectivity or extra equations on the original vector are needed. -/
theorem map_fixedVector (φ : K →+* L) (M : Matrix J J K) (r : J → K)
    (hfix : M *ᵥ r = r) : M.map φ *ᵥ (φ ∘ r) = φ ∘ r := by
  funext j
  calc
    (M.map φ *ᵥ (φ ∘ r)) j = φ ((M *ᵥ r) j) :=
      (φ.map_mulVec M r j).symm
    _ = φ (r j) := congrArg φ (congrFun hfix j)

end ScalarExtension

end SubexponentialSAT.Annihilation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A first-order finite program language. Unbounded data lives only in Boolean
stacks; every register is one bit and all control labels are fixed finite data. -/

namespace SubexponentialSAT.BitProgram

inductive Instr (r s l : ℕ) where
  | halt
  | goto (next : Fin l)
  | set (dst : Fin r) (value : Bool) (next : Fin l)
  | copy (dst src : Fin r) (next : Fin l)
  | bnot (dst src : Fin r) (next : Fin l)
  | band (dst left right : Fin r) (next : Fin l)
  | bor (dst left right : Fin r) (next : Fin l)
  | bxor (dst left right : Fin r) (next : Fin l)
  | branch (test : Fin r) (yes no : Fin l)
  | push (stack : Fin s) (src : Fin r) (next : Fin l)
  | peek (stack : Fin s) (value present : Fin r) (next : Fin l)
  | pop (stack : Fin s) (value present : Fin r) (next : Fin l)
  deriving DecidableEq, Fintype

structure Program (r s l : ℕ) where
  inputStack : Fin s
  outputStack : Fin s
  entry : Fin l
  code : Fin l → Instr r s l

structure Cfg (r s l : ℕ) where
  pc : Option (Fin l)
  regs : Fin r → Bool
  «stacks» : Fin s → List Bool

def readRegs {r : ℕ} (regs : Fin r → Bool) (value present : Fin r)
    (top : Option Bool) : Fin r → Bool :=
  Function.update (Function.update regs value (top.getD false)) present top.isSome

/-- One source instruction performs at most one stack operation. -/
def execInstr {r s l : ℕ} (instr : Instr r s l) (c : Cfg r s l) : Cfg r s l :=
  match instr with
  | .halt => { c with pc := none }
  | .goto next => { c with pc := some next }
  | .set dst value next =>
      { c with pc := some next, regs := Function.update c.regs dst value }
  | .copy dst src next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs src) }
  | .bnot dst src next =>
      { c with pc := some next, regs := Function.update c.regs dst (!(c.regs src)) }
  | .band dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a && c.regs b) }
  | .bor dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a || c.regs b) }
  | .bxor dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a ^^ c.regs b) }
  | .branch test yes no => { c with pc := some (if c.regs test then yes else no) }
  | .push stack src next =>
      { c with pc := some next, «stacks» := Function.update c.stacks stack (c.regs src :: c.stacks stack) }
  | .peek stack value present next =>
      { c with pc := some next, regs := readRegs c.regs value present (c.stacks stack).head? }
  | .pop stack value present next =>
      { pc := some next, regs := readRegs c.regs value present (c.stacks stack).head?, «stacks» := Function.update c.stacks stack (c.stacks stack).tail }

abbrev step {r s l : ℕ} (p : Program r s l) (c : Cfg r s l) : Option (Cfg r s l) :=
  c.pc.map fun label => execInstr (p.code label) c

abbrev initial {r s l : ℕ} (p : Program r s l) (input : List Bool) : Cfg r s l :=
  ⟨some p.entry, fun _ => false, fun stack => if stack = p.inputStack then input else []⟩

/-- A canonical output boundary, for the strong TM2 input/output convention. -/
abbrev terminal {r s l : ℕ} (p : Program r s l) (output : List Bool) : Cfg r s l :=
  ⟨none, fun _ => false, fun stack => if stack = p.outputStack then output else []⟩

abbrev Trace {r s l : ℕ} (p : Program r s l) := SubexponentialSAT.Computation.Trace (step p)

@[simp] theorem step_none {r s l : ℕ} (p : Program r s l) (c : Cfg r s l)
    (h : c.pc = none) : step p c = none := by simp [step, h]

@[simp] theorem readRegs_present {r : ℕ} (regs : Fin r → Bool)
    (value present : Fin r) (top : Option Bool) :
    readRegs regs value present top present = top.isSome := by
  simp [readRegs]

end SubexponentialSAT.BitProgram

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

open BitProgram

variable {r s l R S L : ℕ}

/-- Relocate all finite references, optionally replacing halt by a return jump. -/
def relocateInstr (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) :
    Instr r s l → Instr R S L
  | .halt => match returnPc with | none => .halt | some pc => .goto pc
  | .goto next => .goto (label next)
  | .set dst value next => .set (register dst) value (label next)
  | .copy dst src next => .copy (register dst) (register src) (label next)
  | .bnot dst src next => .bnot (register dst) (register src) (label next)
  | .band dst left right next =>
      .band (register dst) (register left) (register right) (label next)
  | .bor dst left right next =>
      .bor (register dst) (register left) (register right) (label next)
  | .bxor dst left right next =>
      .bxor (register dst) (register left) (register right) (label next)
  | .branch test yes no => .branch (register test) (label yes) (label no)
  | .push port src next => .push (stack port) (register src) (label next)
  | .peek port value present next =>
      .peek (stack port) (register value) (register present) (label next)
  | .pop port value present next =>
      .pop (stack port) (register value) (register present) (label next)

def relocatePc (label : Fin l → Fin L) (returnPc : Option (Fin L)) :
    Option (Fin l) → Option (Fin L)
  | none => returnPc
  | some pc => some (label pc)

/-- A mathematical embedding into the caller's frame.  The executable program
does not evaluate this function: it uses the finite relocated instruction table. -/
noncomputable def embedCfg (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (c : Cfg r s l) : Cfg R S L where
  pc := relocatePc label returnPc c.pc
  regs := Function.extend register c.regs frame.regs
  «stacks» := Function.extend stack c.stacks frame.stacks

@[simp] theorem embedCfg_register (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (hinj : Function.Injective register) (a : Fin r) :
    (embedCfg register stack label returnPc frame c).regs (register a) = c.regs a :=
  hinj.extend_apply _ _ _

@[simp] theorem embedCfg_stack (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (hinj : Function.Injective stack) (a : Fin s) :
    (embedCfg register stack label returnPc frame c).stacks (stack a) = c.stacks a :=
  hinj.extend_apply _ _ _

/-- Install a standalone program on a larger port set, keeping its labels. -/
abbrev liftProgram (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) : Program R S l where
  inputStack := stack p.inputStack
  outputStack := stack p.outputStack
  entry := p.entry
  code := fun pc => relocateInstr register stack id none (p.code pc)

/-! ## Concrete disjoint linking -/

/-- Install two finite tables in disjoint label ranges.  The first block's halts
jump to the second block's entry; the second block's halts stop the program.
Register and stack assignments can share ports between the two blocks. -/
abbrev linkInto {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    Program R S (l + m) where
  inputStack := stackP p.inputStack
  outputStack := stackQ q.outputStack
  entry := Fin.castAdd m p.entry
  code := Fin.addCases
    (fun pc => relocateInstr registerP stackP (Fin.castAdd m)
      (some (Fin.natAdd l q.entry)) (p.code pc))
    (fun pc => relocateInstr registerQ stackQ (Fin.natAdd l) none (q.code pc))

/-- Only change the finite program counter, keeping all data verbatim. -/
abbrev relabelCfg (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (c : Cfg r s l) : Cfg r s L where
  pc := relocatePc label returnPc c.pc
  regs := c.regs
  «stacks» := c.stacks

@[simp] theorem embedCfg_id (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (frame : Cfg r s L) (c : Cfg r s l) :
    embedCfg id id label returnPc frame c = relabelCfg label returnPc c := by
  simp [embedCfg, relabelCfg]

/-- Sequential composition when both blocks already use the same port set. -/
abbrev link {m : ℕ} (p : Program r s l) (q : Program r s m) : Program r s (l + m) :=
  linkInto p q id id id id

@[simp] theorem link_initial {m : ℕ} (p : Program r s l) (q : Program r s m)
    (input : List Bool) :
    relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) (initial p input) =
      initial (link p q) input := rfl

@[simp] theorem link_terminal {m : ℕ} (p : Program r s l) (q : Program r s m)
    (output : List Bool) :
    relabelCfg (Fin.natAdd l) none (terminal q output) =
      terminal (link p q) output := rfl

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

abbrev Stacks (S : Type u) := S → List Bool

/-- Specification of emptying one stack. -/
abbrev clearStacks {S : Type u} [DecidableEq S] (src : S) (stk : Stacks S) : Stacks S :=
  Function.update stk src []

/-- Specification of popping a source onto a destination. -/
abbrev transferStacks {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) : Stacks S :=
  Function.update (Function.update stk src []) dst
    ((stk src).reverse ++ stk dst)

/-- Specification of a preserving copy, with the copied word prefixed to `dst`. -/
abbrev copyStacks {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) : Stacks S :=
  Function.update stk dst (stk src ++ stk dst)

@[simp] theorem clearStacks_src {S : Type u} [DecidableEq S] (src : S) (stk : Stacks S) :
    clearStacks src stk src = [] := by simp [clearStacks]

@[simp] theorem transferStacks_src {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) (h : src ≠ dst) : transferStacks src dst stk src = [] := by
  simp [transferStacks, h]

@[simp] theorem transferStacks_dst {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) :
    transferStacks src dst stk dst = (stk src).reverse ++ stk dst := by
  simp [transferStacks]

@[simp] theorem copyStacks_dst {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) : copyStacks src dst stk dst = stk src ++ stk dst := by
  simp [copyStacks]

open BitProgram

/-- A complete four-label transfer program; label `3` is its halt. -/
abbrev transferProgram {r s : ℕ} (src dst : Fin s) (value present : Fin r) : Program r s 4 where
  inputStack := src
  outputStack := dst
  entry := 0
  code := ![.pop src value present 1, .branch present 2 3, .push dst value 0, .halt]

def copyResult {r s l : ℕ} (exit : Fin l) (src dst : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, copyStacks src dst stk⟩

/-- An eight-label program implementing preserving copy. Label `7` halts. -/
abbrev copyProgram {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r) : Program r s 8 where
  inputStack := src
  outputStack := dst
  entry := 0
  code := ![.pop src value present 1, .branch present 2 3, .push tmp value 0,
    .pop tmp value present 4, .branch present 5 7, .push src value 6, .push dst value 3, .halt]

end SubexponentialSAT.StackRoutines

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

namespace Add

abbrev Regs := Fin 8 → Bool

/-- A constant finite program: it never inspects the numeric value or length
of an operand. Registers 0..7 are carry,a,b,present-a,present-b,t,u,v. -/
def program : SubexponentialSAT.BitProgram.Program 8 3 13 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 1 3 1
    | 1 => .pop 1 2 4 2
    | 2 => .branch 3 4 3
    | 3 => .branch 4 4 10
    | 4 => .bxor 5 1 2 5
    | 5 => .band 6 1 2 6
    | 6 => .band 7 5 0 7
    | 7 => .bxor 1 5 0 8
    | 8 => .bxor 0 6 7 9
    | 9 => .push 2 1 0
    | 10 => .branch 0 11 12
    | 11 => .push 2 0 12
    | _ => .halt

/-- The complete adder followed by an actual stack-transfer loop.  Its output
has the same little-endian orientation as its inputs. -/
def littleEndianProgram : SubexponentialSAT.BitProgram.Program 8 3 17 :=
  SubexponentialSAT.ProgramLinking.link program
    (SubexponentialSAT.StackRoutines.transferProgram (2 : Fin 3) 0 (1 : Fin 8) 3)

end Add

namespace Mul

abbrev Regs := Fin 8 → Bool

end Mul

end SubexponentialSAT.BinaryPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StructuredProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Structured programs compiled to finite bit instruction tables

The syntax has no unbounded natural-number registers or semantic-function
instructions. All data operations are the concrete Boolean-register and stack
instructions of BitProgram. Loops inspect a Boolean register, and changing data
never changes the finite generated instruction table.
-/

namespace SubexponentialSAT.StructuredProgram

open SubexponentialSAT.BitProgram

/-- Data separate from the finite program counter. -/
structure State (r s : ℕ) where
  regs : Fin r → Bool
  «stacks» : Fin s → List Bool

namespace State

abbrev withPC {r s l : ℕ} (d : State r s) (pc : Option (Fin l)) : Cfg r s l :=
  ⟨pc, d.regs, d.stacks⟩

def ofCfg {r s l : ℕ} (c : Cfg r s l) : State r s := ⟨c.regs, c.stacks⟩

@[simp] theorem ofCfg_withPC {r s l : ℕ} (d : State r s) (pc : Option (Fin l)) :
    ofCfg (d.withPC pc) = d := rfl

end State

/-- Every atom is a single existing instruction with its continuation omitted. -/
inductive Atom (r s : ℕ) where
  | set (dst : Fin r) (value : Bool)
  | copy (dst src : Fin r)
  | bnot (dst src : Fin r)
  | band (dst left right : Fin r)
  | bor (dst left right : Fin r)
  | bxor (dst left right : Fin r)
  | push (stack : Fin s) (src : Fin r)
  | peek (stack : Fin s) (value present : Fin r)
  | pop (stack : Fin s) (value present : Fin r)
  deriving DecidableEq, Fintype

namespace Atom

def instr {r s l : ℕ} (a : Atom r s) (next : Fin l) : Instr r s l :=
  match a with
  | .set dst value => .set dst value next
  | .copy dst src => .copy dst src next
  | .bnot dst src => .bnot dst src next
  | .band dst left right => .band dst left right next
  | .bor dst left right => .bor dst left right next
  | .bxor dst left right => .bxor dst left right next
  | .push stack src => .push stack src next
  | .peek stack value present => .peek stack value present next
  | .pop stack value present => .pop stack value present next

end Atom

inductive Cmd (r s : ℕ) where
  | skip
  | atom (a : Atom r s)
  | seq (first second : Cmd r s)
  | ite (test : Fin r) (yes no : Cmd r s)
  | while (test : Fin r) (body : Cmd r s)

/-- One static site per atom or guard; sequencing introduces no instruction. -/
abbrev Site {r s : ℕ} : Cmd r s → Type
  | .skip => Empty
  | .atom _ => Unit
  | .seq first second => Site first ⊕ Site second
  | .ite _ yes no => Option (Site yes ⊕ Site no)
  | .while _ body => Option (Site body)

/-- Entry address when the command's continuation is a given address. -/
abbrev entry {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) : Fin l :=
  match c with
  | .skip => exit
  | .atom _ => embed ()
  | .seq first second =>
      entry first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
  | .ite _ _ _ => embed none
  | .while _ _ => embed none

/-- Actual instruction at each static site. While bodies return to their guard. -/
abbrev code {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) :
    Site c → Instr r s l :=
  match c with
  | .skip => fun q => nomatch q
  | .atom a => fun _ => a.instr exit
  | .seq first second => fun q => match q with
      | .inl x => code first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit) x
      | .inr x => code second (embed ∘ Sum.inr) exit x
  | .ite test yes no => fun q => match q with
      | none => .branch test (entry yes (fun x => embed (some (.inl x))) exit)
          (entry no (fun x => embed (some (.inr x))) exit)
      | some (.inl x) => code yes (fun x => embed (some (.inl x))) exit x
      | some (.inr x) => code no (fun x => embed (some (.inr x))) exit x
  | .while test body => fun q => match q with
      | none => .branch test (entry body (embed ∘ some) (embed none)) exit
      | some x => code body (embed ∘ some) (embed none) x

/-- Syntactic control size, independent of all runtime stack lengths. -/
abbrev size {r s : ℕ} : Cmd r s → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq first second => size first + size second
  | .ite _ yes no => size yes + size no + 1
  | .while _ body => size body + 1

/-- An explicit computable enumeration of control sites; no finite-choice
oracle is used to construct the generated instruction table. -/
abbrev siteEquiv {r s : ℕ} : (c : Cmd r s) → Site c ≃ Fin (size c)
  | .skip => finZeroEquiv.symm
  | .atom _ => finOneEquiv.symm
  | .seq first second =>
      ((siteEquiv first).sumCongr (siteEquiv second)).trans finSumFinEquiv
  | .ite _ yes no =>
      (((siteEquiv yes).sumCongr (siteEquiv no)).trans finSumFinEquiv).optionCongr.trans
        (finSuccEquiv _).symm
  | .while _ body => (siteEquiv body).optionCongr.trans (finSuccEquiv _).symm

/-- The extra address is the common final halt instruction. -/
abbrev labelEquiv {r s : ℕ} (c : Cmd r s) : Option (Site c) ≃ Fin (size c + 1) :=
  (siteEquiv c).optionCongr.trans (finSuccEquiv _).symm

abbrev siteAddress {r s : ℕ} (c : Cmd r s) (q : Site c) : Fin (size c + 1) :=
  labelEquiv c (some q)

abbrev exitAddress {r s : ℕ} (c : Cmd r s) : Fin (size c + 1) := labelEquiv c none

/-- A concrete, computably generated finite bit program. -/
def compiled {r s : ℕ} (c : Cmd r s) (inputStack outputStack : Fin s) :
    Program r s (size c + 1) where
  inputStack := inputStack
  outputStack := outputStack
  entry := entry c (siteAddress c) (exitAddress c)
  code label := match (labelEquiv c).symm label with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q

@[simp] theorem compiled_site {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) (q : Site c) :
    (compiled c inputStack outputStack).code (siteAddress c q) =
      code c (siteAddress c) (exitAddress c) q := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) (some q)) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem compiled_exit {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) :
    (compiled c inputStack outputStack).code (exitAddress c) = Instr.halt := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) none) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

end SubexponentialSAT.StructuredProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StructuredCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Structured invocation of existing finite bit programs

A call contains a fixed finite instruction table. Its execution premise is an
actual trace of that table, rather than a semantic or cost oracle. Compilation
relocates all its instructions and replaces each halt by a return jump. Thus
arbitrary cyclic subroutines can occur inside structured loops without manually
assigning global labels.
-/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

abbrev State := StructuredProgram.State

inductive Cmd (r s : ℕ) where
  | base (c : StructuredProgram.Cmd r s)
  | call {labels : ℕ} (program : Program r s labels)
  | seq (first second : Cmd r s)
  | ite (test : Fin r) (yes no : Cmd r s)
  | while (test : Fin r) (body : Cmd r s)

abbrev Site {r s : ℕ} : Cmd r s → Type
  | .base c => StructuredProgram.Site c
  | @Cmd.call _ _ labels _ => Fin labels
  | .seq first second => Site first ⊕ Site second
  | .ite _ yes no => Option (Site yes ⊕ Site no)
  | .while _ body => Option (Site body)

abbrev size {r s : ℕ} : Cmd r s → ℕ
  | .base c => StructuredProgram.size c
  | @Cmd.call _ _ labels _ => labels
  | .seq first second => size first + size second
  | .ite _ yes no => size yes + size no + 1
  | .while _ body => size body + 1

/-- Finite control enumeration is computed directly from the fixed syntax. -/
abbrev siteEquiv {r s : ℕ} : (c : Cmd r s) → Site c ≃ Fin (size c)
  | .base c => StructuredProgram.siteEquiv c
  | .call _ => Equiv.refl _
  | .seq first second =>
      ((siteEquiv first).sumCongr (siteEquiv second)).trans finSumFinEquiv
  | .ite _ yes no =>
      (((siteEquiv yes).sumCongr (siteEquiv no)).trans finSumFinEquiv).optionCongr.trans
        (finSuccEquiv _).symm
  | .while _ body => (siteEquiv body).optionCongr.trans (finSuccEquiv _).symm

abbrev entry {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) : Fin l :=
  match c with
  | .base c => StructuredProgram.entry c embed exit
  | .call p => embed p.entry
  | .seq first second =>
      entry first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
  | .ite _ _ _ => embed none
  | .while _ _ => embed none

/-- Calls use the proved concrete instruction relocation, including every
internal branch and each return instruction. -/
abbrev code {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) :
    Site c → Instr r s l :=
  match c with
  | .base c => StructuredProgram.code c embed exit
  | .call p => fun q => ProgramLinking.relocateInstr id id embed (some exit) (p.code q)
  | .seq first second => fun q => match q with
      | .inl x => code first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit) x
      | .inr x => code second (embed ∘ Sum.inr) exit x
  | .ite test yes no => fun q => match q with
      | none => .branch test (entry yes (fun x => embed (some (.inl x))) exit)
          (entry no (fun x => embed (some (.inr x))) exit)
      | some (.inl x) => code yes (fun x => embed (some (.inl x))) exit x
      | some (.inr x) => code no (fun x => embed (some (.inr x))) exit x
  | .while test body => fun q => match q with
      | none => .branch test (entry body (embed ∘ some) (embed none)) exit
      | some x => code body (embed ∘ some) (embed none) x

abbrev labelEquiv {r s : ℕ} (c : Cmd r s) : Option (Site c) ≃ Fin (size c + 1) :=
  (siteEquiv c).optionCongr.trans (finSuccEquiv _).symm

abbrev siteAddress {r s : ℕ} (c : Cmd r s) (q : Site c) : Fin (size c + 1) :=
  labelEquiv c (some q)

abbrev exitAddress {r s : ℕ} (c : Cmd r s) : Fin (size c + 1) := labelEquiv c none

/-- The full finite instruction table is computably generated from the fixed
syntax and finite subroutine tables. No runtime stack data is inspected. -/
def compiled {r s : ℕ} (c : Cmd r s) (inputStack outputStack : Fin s) :
    Program r s (size c + 1) where
  inputStack := inputStack
  outputStack := outputStack
  entry := entry c (siteAddress c) (exitAddress c)
  code label := match (labelEquiv c).symm label with
    | none => .halt
    | some q => code c (siteAddress c) (exitAddress c) q

@[simp] theorem compiled_site {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) (q : Site c) :
    (compiled c inputStack outputStack).code (siteAddress c q) =
      code c (siteAddress c) (exitAddress c) q := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) (some q)) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem compiled_exit {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) :
    (compiled c inputStack outputStack).code (exitAddress c) = Instr.halt := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) none) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ListRegisterProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unbounded Boolean-list registers implemented by finite programs

Logical words are Boolean stacks.  Three fixed scratch stacks suffice for
alias-safe word assignment, prefixing, and appending; all are restored empty.
The programs below contain only the existing finite Boolean/stack instructions.
Every stated cost is proved by an actual execution trace.
-/

namespace SubexponentialSAT.ListRegisterProgram

open BitProgram StackRoutines ProgramLinking

/-- A complete execution retaining an arbitrary surrounding data store. -/
abbrev Run {r s l : ℕ} (p : Program r s l) (n : ℕ)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (regs' : Fin r → Bool) (stk' : Stacks (Fin s)) : Prop :=
  Trace p n ⟨some p.entry, regs, stk⟩ ⟨none, regs', stk'⟩

end SubexponentialSAT.ListRegisterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Source-preserving arithmetic calls on fixed Boolean-stack ports

Operands are copied into distinct work ports before the actual finite adder or
multiplier runs. The source ports may coincide. The only final stack change is
the output word; every work port is restored to its incoming empty state.
-/

namespace SubexponentialSAT.ArithmeticCalls

open BitProgram StructuredCalls

structure Ports (S : ℕ) where
  left : Fin S
  right : Fin S
  out : Fin S
  work : Fin 5 ↪ Fin S
  out_ne_left : out ≠ left
  out_ne_right : out ≠ right
  work_ne_left : ∀ i, work i ≠ left
  work_ne_right : ∀ i, work i ≠ right
  work_ne_out : ∀ i, work i ≠ out

abbrev Data (S : ℕ) := StructuredProgram.State 8 S

def Valid {S : ℕ} (p : Ports S) (d : Data S) : Prop :=
  d.stacks p.out = [] ∧ ∀ i, d.stacks (p.work i) = []

@[simp] theorem left_ne_work {S : ℕ} (p : Ports S) (i : Fin 5) :
    p.left ≠ p.work i := (p.work_ne_left i).symm
@[simp] theorem right_ne_work {S : ℕ} (p : Ports S) (i : Fin 5) :
    p.right ≠ p.work i := (p.work_ne_right i).symm
@[simp] theorem out_ne_work {S : ℕ} (p : Ports S) (i : Fin 5) :
    p.out ≠ p.work i := (p.work_ne_out i).symm

abbrev copyAt {S : ℕ} (source target scratch : Fin S) : Cmd 8 S :=
  .call (StackRoutines.copyProgram source target scratch 0 1)

def afterCopy {S : ℕ} (source target : Fin S) (d : Data S) : Data S :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks target (d.stacks source)⟩

def addPorts {S : ℕ} (p : Ports S) : Fin 3 → Fin S :=
  ![p.out, p.work 1, p.work 2]

theorem addPorts_injective {S : ℕ} (p : Ports S) : Function.Injective (addPorts p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [addPorts, p.work.injective.eq_iff, p.work_ne_out]

abbrev addRaw {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram BinaryPrograms.Add.littleEndianProgram id (addPorts p))

abbrev addAt {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .seq (copyAt p.left p.out (p.work 3))
    (.seq (copyAt p.right (p.work 1) (p.work 3))
      (.seq (.base (.atom (.set 0 false))) (addRaw p)))

def addReady {S : ℕ} (p : Ports S) (d : Data S) : Data S :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks p.out (d.stacks p.left))
      (p.work 1) (d.stacks p.right)⟩

end SubexponentialSAT.ArithmeticCalls

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

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

abbrev Clause := List (List Bool)

namespace Filter

def guardStack : Fin 11 → Fin 14 := Fin.castAdd 3


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end


