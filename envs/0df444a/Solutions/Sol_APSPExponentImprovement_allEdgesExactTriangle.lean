-- Prove2me | solution 1 for APSPExponentImprovement.allEdgesExactTriangle
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T14:53:20.673524+00:00
-- url     : https://prove2.me/submissions/10ffc5d5-334f-4618-8443-7c2569ac0a64

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPExponentImprovement_AllEdgesExactTriangle
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_ZOrder
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_CountingSort
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_APSPSource_ThreeSumApsp_Util_PrimesInWindow
import Definitions.Def_TrulySubcubicAPSP_Problems
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Iterate
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Sec3_et17Sizes_spec
import Theorems.Thm_Light_Sec3_obeysBound17_hostTime
import Theorems.Thm_Light_Sec4_allInstances26_solves
import Theorems.Thm_Light_Sec4_allInstancesTime26_le
import Theorems.Thm_Light_Sec4_pre31_program31
import Theorems.Thm_Light_Sec4_queryAt_spec
import Theorems.Thm_Light_Sec4_specs40
import Theorems.Thm_Light_Wrap_realized
import Theorems.Thm_List_getD_filter_range_count
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_Spec_chunkTab_cover
import Theorems.Thm_ThreeSumApsp_Spec_chunkTab_pairwise
import Theorems.Thm_ThreeSumApsp_Spec_length_chunkTab_le
import Theorems.Thm_ThreeSumApsp_Spec_length_classIdx_eq_card
import Theorems.Thm_ThreeSumApsp_Spec_zRow_zCol_quadrant
import Theorems.Thm_ThreeSumApsp_Theorem19_Choice_ceil_le_sqrt
import Theorems.Thm_ThreeSumApsp_TriangleInstance_card_instanceIndices
import Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async true
namespace EndStatement
end EndStatement
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Transport from the original paper's word RAM and problem statements to the
mission's separately declared copies. No algorithm or running-time result is
assumed here: every theorem below preserves the source proof's exact step bound.
-/

namespace APSPProofBridge

/-- The instruction correspondence preserves each operand and branch target. -/
def instruction : EndStatement.Instr → TrulySubcubicAPSP.Instr
  | .one i => .one i
  | .add i j k => .add i j k
  | .sub i j k => .sub i j k
  | .mul i j k => .mul i j k
  | .load i j => .load i j
  | .store i j => .store i j
  | .bltz i l => .bltz i l
  | .accept => .accept
  | .reject => .reject

/-- Map every instruction, preserving program length and every program position. -/
def program (P : List EndStatement.Instr) : List TrulySubcubicAPSP.Instr :=
  P.map instruction

theorem loadWords (W : Nat) (ws : List Int) :
    TrulySubcubicAPSP.loadWords W ws = EndStatement.loadWords W ws := rfl

theorem instructionAt (P : List EndStatement.Instr) (pc : Nat) :
    (program P).getD pc .reject = instruction (P.getD pc .reject) := by
  induction P generalizing pc with
  | nil => simp [program, instruction]
  | cons i P ih =>
    cases pc with
    | zero => simp [program]
    | succ pc => simpa [program] using ih pc

/-- The copied machine executes the mapped program identically, at every word
width, time bound, program counter, and initial memory. -/
theorem exec {W : Nat} (P : List EndStatement.Instr) (t pc : Nat)
    (m : Int → BitVec W) :
    TrulySubcubicAPSP.exec (program P) t pc m = EndStatement.exec P t pc m := by
  induction t generalizing pc m with
  | zero => rfl
  | succ t ih =>
    simp only [TrulySubcubicAPSP.exec, EndStatement.exec, instructionAt]
    cases P.getD pc .reject <;> simp only [instruction] <;> try rfl
    all_goals apply ih

/-- Instance conversion together with matching input, verdict, and output
specifications suffices to transport an execution witness. -/
theorem solvedBy {Q : EndStatement.Problem} {R : TrulySubcubicAPSP.Problem}
    (f : ∀ {n : Nat}, R.Instance n → Q.Instance n)
    (input_eq : ∀ {n : Nat} (x : R.Instance n), Q.input (f x) = R.input x)
    (yes_iff : ∀ {n : Nat} (x : R.Instance n), Q.yes (f x) ↔ R.yes x)
    (output_iff : ∀ {n : Nat} (x : R.Instance n) (out : Nat → Int),
      Q.output (f x) out ↔ R.output x out)
    {n : Nat} (x : R.Instance n) (P : List EndStatement.Instr) (W t : Nat)
    (h : Q.SolvedBy (f x) P W t) : R.SolvedBy x (program P) W t := by
  obtain ⟨verdict, m, run, correct, output⟩ := h
  refine ⟨verdict, m, ?_, correct.trans (yes_iff x), ?_⟩
  · rw [exec, loadWords, ← input_eq x]
    exact run
  · apply (output_iff x _).mp
    simpa only [input_eq x] using output

/-- Transport preserves the program's step bound, width bound, exponent, and all
quantifiers over input magnitudes, sizes, instances, and word widths. -/
theorem solvedInTime {Q : EndStatement.Problem} {R : TrulySubcubicAPSP.Problem}
    (f : ∀ {n : Nat}, R.Instance n → Q.Instance n)
    (input_eq : ∀ {n : Nat} (x : R.Instance n), Q.input (f x) = R.input x)
    (yes_iff : ∀ {n : Nat} (x : R.Instance n), Q.yes (f x) ↔ R.yes x)
    (output_iff : ∀ {n : Nat} (x : R.Instance n) (out : Nat → Int),
      Q.output (f x) out ↔ R.output x out)
    {r : Rat} (h : Q.SolvedInTime r) : R.SolvedInTime r := by
  intro κ
  obtain ⟨P, b, T, bound, correct⟩ := h κ
  refine ⟨program P, b, T, bound, ?_⟩
  intro n x magnitude W width
  apply solvedBy f input_eq yes_iff output_iff
  apply correct n (f x) _ W width
  simpa only [input_eq x] using magnitude





















































end APSPProofBridge

end

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

/-- Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i,
whatever is appended after the list. -/
theorem getElem?_append_append {P₀ B : Program} (R : Program) {i : ℕ} {body : Stmt}
    (h : B[i]? = some body) : (P₀ ++ (B ++ R))[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R







/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩













/-- Loops.  I i is the invariant before round number i (counted from 0) of n rounds, and b i bounds
the cost of that round. -/
theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h
































/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/







/-- The sum of two expressions. -/
infixl:65 " +' " => Expr.op Op.add
/-- The difference of two expressions. -/
infixl:65 " -' " => Expr.op Op.sub
/-- The product of two expressions. -/
infixl:70 " *' " => Expr.op Op.mul
 infix:50 " <' " => Cond.lt
 infix:50 " =' " => Cond.eq
 infixr:30 " ;; " => Stmt.seq



@[inherit_doc] infix:50 " ≤' " => Cond.le








/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame












/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/
























end Light

end
end

section


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

/-- The case of a single cell. -/
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl

theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl

theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)

/-- Fewer cells are kept. -/
theorem SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)

/-- Two steps that keep different cells. -/
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)

/-- Writing a cell that need not be kept. -/
theorem SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := fun c hc => by
  rw [Function.update_of_ne (by rintro rfl; exact hb hc)]; exact h c hc

/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- Nothing has been written yet. -/
theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

/-- One more cell is written. -/
theorem wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]










/-- Writing `j ≤ n` cells from `dst` changes no cell outside the `n` cells from `dst`. -/
theorem sameOutside_wrote {n : ℕ} (h : j ≤ n) : SameOutside μ (wrote μ dst f j) dst n :=
  fun _ hb => wrote_rest (by omega)

/-! ## The tactics -/









































end Light

end
end

section


/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/





/-- Row `a < m` ends within the matrix: `a * n + b ≤ m * n` for `b ≤ n`, so also for `b = n`. -/
theorem mul_add_le_mul {a b m n : ℕ} (ha : a < m) (hb : b ≤ n) : a * n + b ≤ m * n :=
  calc a * n + b ≤ a * n + n := Nat.add_le_add_left hb _
    _ = (a + 1) * n := (Nat.succ_mul a n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n ha

/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/












/-- The row of an index below `m * n` is below `m`. -/
theorem div_lt_of_lt_mul' {t m n : ℕ} (h : t < m * n) : t / n < m :=
  Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ h)

/-- The column of an index below `m * n` is below `n`. -/
theorem mod_lt_of_lt_mul {t m n : ℕ} (h : t < m * n) : t % n < n :=
  Nat.mod_lt t (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt h))














/-! ## The next index -/

/-- The next index, if it is in the same row. -/
theorem succ_div_mod_of_lt {n i : ℕ} (h : i % n + 1 < n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by
  have hsucc : i + 1 = i / n * n + (i % n + 1) := by rw [← Nat.add_assoc, Nat.div_add_mod']
  exact ⟨by rw [hsucc, mul_add_div_of_lt h], by rw [hsucc, Nat.mul_add_mod_of_lt h]⟩

/-- The next index, if the test "is this the end of the row?" fails. -/
theorem succ_div_mod_of_ne {n i : ℕ} (hn : 0 < n) (h : i % n + 1 ≠ n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 :=
  succ_div_mod_of_lt (lt_of_le_of_ne (Nat.mod_lt i hn) h)

/-- After the last index of a row comes the first index of the next row. -/
theorem succ_div_mod_of_eq {n i : ℕ} (h : i % n + 1 = n) :
    (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0 := by
  have hn : 0 < n := h ▸ Nat.succ_pos _
  have hsucc : i + 1 = (i / n + 1) * n + 0 := by
    have hdivmod := Nat.div_add_mod' i n
    rw [Nat.succ_mul]
    -- `i = i / n * n + i % n` and `i % n + 1 = n`
    omega
  exact ⟨by rw [hsucc, mul_add_div_of_lt hn], by rw [hsucc, Nat.mul_add_mod_of_lt hn]⟩

end Nat

namespace Int

/-! ## Residues as natural numbers -/






/-- The residue of an integer modulo `M ≥ 1` is a natural number. -/
theorem natCast_toNat_emod {M : ℕ} (hM : 0 < M) (x : ℤ) : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (Int.natCast_ne_zero_iff_pos.2 hM))

end Int

end
end

section


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]

/-- Entry `j` of the second of two lists put together. -/
theorem getD_append_add (l l' : List α) (j : ℕ) (d : α) :
    (l ++ l').getD (l.length + j) d = l'.getD j d := by
  rw [List.getD_append_right l l' d _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Entry `j` of a list without its first `a` entries. -/
theorem getD_drop (l : List α) (a j : ℕ) (d : α) : (l.drop a).getD j d = l.getD (a + j) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Entry `j < n` of the first `n` entries. -/
theorem getD_take_of_lt (l : List α) {n j : ℕ} (hj : j < n) (d : α) :
    (l.take n).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]









































/-! ## Blocks one after the other -/

/-- Blocks of any lengths: entry `o` of block `r` stands after the blocks `0, …, r - 1`. -/
theorem getD_flatMap_range_sum (f : ℕ → List α) {n r o : ℕ} (hr : r < n) (ho : o < (f r).length)
    (d : α) :
    ((List.range n).flatMap f).getD (((List.range r).map fun s => (f s).length).sum + o) d =
      (f r).getD o d := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hr
  rw [Nat.add_assoc, List.range_add, List.flatMap_append, ← List.length_flatMap, getD_append_add,
    Nat.add_comm c 1, List.range_add, List.map_append, List.flatMap_append,
    List.getD_append _ _ _ _ (by simpa using ho)]
  simp

/-- The length of `n` blocks of length `k`. -/
theorem length_flatMap_range {k : ℕ} (n : ℕ) (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) :
    ((List.range n).flatMap f).length = n * k := by
  rw [List.length_flatMap,
    List.map_congr_left (g := fun _ => k) fun z hz => hf z (List.mem_range.1 hz)]
  simp

/-- Blocks of length `k`: entry `r` of block `z` has the index `z * k + r`. -/
theorem getD_flatMap_range {k n : ℕ} (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) {z r : ℕ}
    (hz : z < n) (hr : r < k) (d : α) :
    ((List.range n).flatMap f).getD (z * k + r) d = (f z).getD r d := by
  rw [← length_flatMap_range z f fun s hs => hf s (hs.trans hz), List.length_flatMap]
  exact getD_flatMap_range_sum f hz (hf z hz ▸ hr) d

















/-- A run of `n` blocks, cut out of a list of blocks of length `k`. -/
theorem take_drop_flatMap_range {k : ℕ} (m n c : ℕ) (f : ℕ → List α)
    (hf : ∀ z < m + n + c, (f z).length = k) :
    (((List.range (m + n + c)).flatMap f).drop (m * k)).take (n * k) =
      (List.range n).flatMap fun z => f (m + z) := by
  have hm : ((List.range m).flatMap f).length = m * k :=
    length_flatMap_range m f fun z hz => hf z (by omega)
  have hn : ((List.range n).flatMap fun z => f (m + z)).length = n * k :=
    length_flatMap_range n _ fun z hz => hf _ (by omega)
  rw [List.range_add, List.range_add, List.flatMap_append, List.flatMap_append, List.append_assoc,
    List.flatMap_map, ← hm, List.drop_left, ← hn, List.take_left]

/-- An entrywise operation on two lists of blocks of one length works block by block. -/
theorem zipWith_flatMap_range {γ : Type*} {k : ℕ} (g : α → β → γ) (n : ℕ) (f : ℕ → List α)
    (f' : ℕ → List β) (hf : ∀ z, (f z).length = k) (hf' : ∀ z, (f' z).length = k) :
    List.zipWith g ((List.range n).flatMap f) ((List.range n).flatMap f') =
      (List.range n).flatMap fun z => List.zipWith g (f z) (f' z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlen : ((List.range n).flatMap f).length = ((List.range n).flatMap f').length := by
      rw [length_flatMap_range n f fun z _ => hf z, length_flatMap_range n f' fun z _ => hf' z]
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_append,
      List.zipWith_append hlen, ih]
    simp








/-! ## Sums -/

/-- The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
`Fin n` go on with `Finset.sum_range`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  rfl

/-- Partial sums of natural numbers grow. -/
theorem sum_map_range_mono (g : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    ((List.range a).map g).sum ≤ ((List.range b).map g).sum := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _




























section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/






















/-- The members with `t a < z + 1` are those with `t a < z` and those with `t a = z`. -/
theorem length_filter_lt_succ (t : α → ℕ) (z : ℕ) (l : List α) :
    (l.filter fun a => decide (t a < z + 1)).length =
      (l.filter fun a => decide (t a < z)).length +
        (l.filter fun a => decide (t a = z)).length := by
  simp only [← List.countP_eq_length_filter]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, ih, decide_eq_true_eq]
    split_ifs <;> omega

/-- The list of the `j < n` with `q j` has `Nat.count q n` members. -/
theorem length_filter_range (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    ((List.range n).filter fun j => decide (q j)).length = Nat.count q n := by
  rw [Nat.count, List.countP_eq_length_filter]






































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/




/-- A bound on the absolute values of all members bounds every entry. -/
theorem AbsLe.getElem {l : List ℤ} {U : ℤ} (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U :=
  h _ (List.getElem_mem hi)






/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}












@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)

/-- Reading a cell of a segment. -/
theorem Seg.get (h : Seg μ a l) {i : ℕ} (hi : i < l.length) : μ (a + i) = l[i] := h i hi









theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at h0,
      fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · have := h (l₁.length + i) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < l₁.length
    · rw [List.getElem_append_left hi₁, h₁ i hi₁]
    · have hi₂ : i - l₁.length < l₂.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega), ← h₂ _ hi₂]
      congr 1
      omega

theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']

theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]

/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_44043_0 apspMacro_44043_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_44043_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_44043_2 apspMacro_44043_0 (by omega)));
                                                                                                  (revert apspMacro_44043_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_44043_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_44043_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_44043_3 apspMacro_44043_0 (by omega)));
                                                                                                  (revert apspMacro_44043_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_44043_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_44043_4 apspMacro_44043_0 (by omega)));
                                                                                                  (revert apspMacro_44043_4)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (fail
                                                                                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩










/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩

/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)

theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc









/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)




/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]






/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l : List ℕ} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h (x : ℤ)







/-- A piece of a segment of natural numbers: w cells from the place lo on. -/
theorem SegN.drop_take {l : List ℕ} (h : SegN μ a l) (lo w : ℕ) :
    SegN μ (a + lo) ((l.drop lo).take w) := by
  simpa only [SegN, List.map_take, List.map_drop] using (Seg.drop h lo).take w

/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_46570_0 apspMacro_46570_1);
                                                    (first
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_46570_2));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_46570_2 apspMacro_46570_0 (by omega)));
                                                                    (revert apspMacro_46570_2)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((simp [] at apspMacro_46570_1);
                                                          (((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_46570_3));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_46570_3 apspMacro_46570_0 (by omega)));
                                                                    (revert apspMacro_46570_3)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_46570_4));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_46570_4 apspMacro_46570_0 (by omega)));
                                                                    (revert apspMacro_46570_4)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (fail
                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                        its condition K x does not follow from the hypotheses."))))) : SegN μ' a l :=
  Seg.keep h (by simpa using hs)

/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : SegN μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : SegN μ' b l :=
  Seg.of_sameOutside h hs (by simpa using hd)





/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.congr {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (he : ∀ b, a ≤ b → b < a + n * k → μ' b = μ b) : MatAt μ' a A := fun i j => by
  have := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [he _ (by omega) (by omega)]
  exact h i j






/-- A matrix that lies below e is still there in a memory that agrees below e. -/
theorem MatAt.congr_below {n k e : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hlow : ∀ x < e, μ' x = μ x) (hle : a + n * k ≤ e) : MatAt μ' a A :=
  h.congr fun b _ hb => hlow b (by omega)
















end Light

end
end

section


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/

/-- A weaker conclusion. -/
theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R)
    (hR : ∀ σ', R σ' → R' σ') : s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩


















theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by first
                                  |
                                    ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                      (first
                                        | omega
                                        | ((ring_nf); (omega))))
                                  | omega
                                  |
                                    (simp [] <;>
                                        first
                                        | omega
                                        | ((ring_nf); (omega)))) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ (Light.Stmt.seq s₂ s₃))) σ T Q) : Ends lim P d ((Light.Stmt.seq (Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d ((Light.Stmt.seq .skip s)) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.next T₁ (h.mono le_rfl rest) hT

/-- A piece of the program about which `h` is known, at the end of the program. -/
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by first
                                                                                            |
                                                                                              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                (first
                                                                                                  | omega
                                                                                                  | ((ring_nf); (omega))))
                                                                                            | omega
                                                                                            |
                                                                                              (simp [] <;>
                                                                                                  first
                                                                                                  | omega
                                                                                                  | ((ring_nf); (omega)))) :
    Ends lim P d s σ T Q :=
  h.mono hT rest































/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
                                                                                                                        |
                                                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                                            (first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega))))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
                                                                                                                        |
                                                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                                            (first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega))))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩










/-! ## Loops whose body is a block -/

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

/-! ## Counting loops -/





/-- **Counting loops.**  I j is the invariant before round j.  The bound hi has the value n
throughout, n fits in a word, and the body keeps the counter and takes at most b steps.  The rule
supplies σ.loc i = j; I 0 is asked of σ with 0 in the counter, and I (j + 1) of the state after the
increment. -/
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

/-- **Counting loops whose body changes no local variable.**  Before round j the local variables are
the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
throughout, n fits in a word, and the body takes at most b steps. -/
theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

end Light

end
end

section


/-!
# Arrays in the memory

A routine assumes the same facts about each of its arrays: which list it holds, how long the list
is, and that it lies below some address `top`, from which on the routine writes: the free pointer,
the place of the result, the scratch space.  `ListAt μ a l N top` is the record of these three
facts, and `ArrayAt μ a l N U top` adds a bound `U` on the entries.  `IndexAt μ a l N p top` is the
record for a list of natural numbers below `p`.  What a routine assumes is then a record with one
field for each array.

* `ListAt.keep`, `ArrayAt.keep`: an array stays in place when its cells do not change.
* `ListAt.mono`, `ArrayAt.mono`: `top` and `U` may grow.
* `ListAt.read`, `ArrayAt.read`, `ArrayAt.abs_read_le`: what a cell holds, and how large it is.
* `ListAt.drop_take`, `ArrayAt.drop_take`: a piece of an array is an array.
* `IndexAt.keep`, `IndexAt.read`, `IndexAt.getD_lt`: the same for natural numbers.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}















namespace ListAt

/-- A list stays in place when its cells do not change.  That they lie below `top` is said again in
the description of the cells: so the promise `Kept μ μ' top` of a callee is enough as it stands. -/
theorem keep (h : ListAt μ a l N top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_61105_0 apspMacro_61105_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_61105_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_61105_2 apspMacro_61105_0 (by omega)));
                                                                                    (revert apspMacro_61105_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_61105_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_61105_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_61105_3 apspMacro_61105_0 (by omega)));
                                                                                    (revert apspMacro_61105_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_61105_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_61105_4 apspMacro_61105_0 (by omega)));
                                                                                    (revert apspMacro_61105_4)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (fail
                                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                        its condition K x does not follow from the hypotheses."))))) : ListAt μ' a l N top :=
  { h with seg := h.seg.congr fun i hi => hs _ (by have := h.len; have := h.below; omega) }





/-- Reading a cell. -/
theorem read (h : ListAt μ a l N top) (hi : i < N) : μ (a + i) = l.getD i 0 :=
  h.seg.getD (h.len ▸ hi) 0








end ListAt

namespace ArrayAt

/-- An array without the bound on its entries. -/
theorem listAt (h : ArrayAt μ a l N U top) : ListAt μ a l N top := { h with }

/-- An array stays in place when its cells do not change. -/
theorem keep (h : ArrayAt μ a l N U top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_61713_0 apspMacro_61713_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_61713_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_61713_2 apspMacro_61713_0 (by omega)));
                                                                                    (revert apspMacro_61713_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_61713_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_61713_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_61713_3 apspMacro_61713_0 (by omega)));
                                                                                    (revert apspMacro_61713_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_61713_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_61713_4 apspMacro_61713_0 (by omega)));
                                                                                    (revert apspMacro_61713_4)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (fail
                                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                        its condition K x does not follow from the hypotheses."))))) :
    ArrayAt μ' a l N U top :=
  { h with seg := (h.listAt.keep hs).seg }






/-- Reading a cell. -/
theorem read (h : ArrayAt μ a l N U top) (hi : i < N) : μ (a + i) = l.getD i 0 := h.listAt.read hi












end ArrayAt









namespace IndexAt

variable {l : List ℕ} {p : ℕ}

/-- A list of natural numbers stays in place when its cells do not change. -/
theorem keep (h : IndexAt μ a l N p top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_62204_0 apspMacro_62204_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_62204_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_62204_2 apspMacro_62204_0 (by omega)));
                                                                                    (revert apspMacro_62204_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_62204_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_62204_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_62204_3 apspMacro_62204_0 (by omega)));
                                                                                    (revert apspMacro_62204_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_62204_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_62204_4 apspMacro_62204_0 (by omega)));
                                                                                    (revert apspMacro_62204_4)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (fail
                                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                        its condition K x does not follow from the hypotheses."))))) :
    IndexAt μ' a l N p top :=
  { h with
    seg := Seg.congr h.seg fun i hi => hs _ (by
      have := h.len
      have := h.below
      rw [List.length_map] at hi
      omega) }

/-- Reading a cell. -/
theorem read (h : IndexAt μ a l N p top) (hi : i < N) : μ (a + i) = (l.getD i 0 : ℕ) :=
  h.seg.read (h.len ▸ hi)

/-- An entry is below `p`. -/
theorem getD_lt (h : IndexAt μ a l N p top) (hi : i < N) : l.getD i 0 < p := by
  have hl : i < l.length := h.len ▸ hi
  rw [List.getD_eq_getElem _ 0 hl]
  exact h.lt _ (List.getElem_mem hl)

end IndexAt

end Light

end
end

section


/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/









/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]

/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}














/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
                                          |
                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                              (first
                                                | omega
                                                | ((ring_nf); (omega))))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | ((ring_nf); (omega)))) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
                                          |
                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                              (first
                                                | omega
                                                | ((ring_nf); (omega))))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.store a e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT

/-- **Counting loops whose body is a block that changes no local variable**, with the locals as a
list.  Before round j the locals are the given ones with j in the counter, and I j holds of the
memory.  The bound hi gives n, and n fits in a word.  The round is a goal about the body, for the
rules of this file, and its time is body.blockCost, so that no number is typed.  A loop or a call
counts 0 steps in blockCost; for a body that contains one use Ends.forShape. -/
theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; (((try have := Light.Std.space_le (by assumption)));
                                                                       ((try have := Light.Std.const_le (by assumption)));
                                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI


































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

















/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩

end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT











/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam


































/-- The bound is positive. -/
theorem one_le_polyBound (s k : ℕ) (params : List ℕ) : 1 ≤ polyBound s k params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_pos (by positivity) (by positivity)



































/-- A power of two times the bound is a bound of the same form. -/
theorem polyBound_mul (s s' k : ℕ) (params : List ℕ) :
    2 ^ s' * polyBound s k params = polyBound (s' + s) k params := by
  simp only [polyBound, pow_add, mul_assoc]









end Light

end
end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/
















/-- A smaller need is allowed for if a larger one is, also with a larger free pointer and at a
larger depth if the sums are not larger. -/
theorem Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩








/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/



























/-- A solver stays a solver when procedures are appended to its program. -/
theorem Solves.append {task : Task} {P : Program} {p : ℕ} {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : Solves task P p T need) (R : Program) : Solves task (P ++ R) p T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, getElem?_append_of_eq_some hp R, fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact hb (R ++ R') lim d x μ fr hpre hok

/-- **A solver meets the specification that its task prescribes**, in every program that begins with
its program. -/
theorem Solves.meets {task : Task} {P₀ : Program} {p : ℕ} {T₀ : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : _root_.Light.Solves task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ} (x : task.Inst) {μ : ℕ → ℤ}
    (fr : ℕ) (hpre : task.Pre x μ fr) (hok : (need (task.size x) (task.bound x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.size x) (task.bound x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩









/-- A larger bound on the running time is still a bound on the running time. -/
theorem SolvedIn.mono {task : Task} {T T' : ℕ → ℝ → ℝ} (h : SolvedIn task T)
    (hT : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ u → T n u ≤ T' n u) : SolvedIn task T' := by
  obtain ⟨P, p, Tn, need, h1, h2, h3⟩ := h
  refine ⟨P, p, Tn, need, h1, h2, fun n U u hn hU hu => (h3 n U u hn hU hu).trans (hT n u hn ?_)⟩
  exact le_trans (by exact_mod_cast hU) hu






theorem le_timeUpTo (Tn : ℕ → ℕ → ℕ) (n : ℕ) {U : ℕ} {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (Tn n U : ℝ) ≤ timeUpTo Tn n u :=
  Nat.cast_le.2 (Finset.le_sup (f := Tn n)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hu))))

/-- What bounds the time for every natural number `U ≤ u` bounds `timeUpTo`.  For a negative `u`
there is still `U = 0`. -/
theorem timeUpTo_le {Tn : ℕ → ℕ → ℕ} {n : ℕ} {u B : ℝ}
    (h : ∀ U : ℕ, (U : ℝ) ≤ max u 0 → (Tn n U : ℝ) ≤ B) : timeUpTo Tn n u ≤ B := by
  obtain ⟨U, hU, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊u⌋₊ + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (Tn n)
  rw [timeUpTo, hsup]
  refine h U ((Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hU))).trans ?_)
  rcases le_total 0 u with hu | hu
  · exact (Nat.floor_le hu).trans (le_max_left u 0)
  · rw [Nat.floor_of_nonpos hu, Nat.cast_zero]
    exact le_max_right u 0

/-- A solver with a polynomially bounded need solves its task in its own time. -/
theorem Solves.solvedIn {task : Task} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hs : Solves task P p Tn need) (hp : PolyNeed need) : SolvedIn task (timeUpTo Tn) :=
  ⟨P, p, Tn, need, hp, hs, fun n _ _ _ _ hu => le_timeUpTo Tn n hu⟩

/-! ## Hosts -/










/-- From a host to a transfer of running times.  What remains is arithmetic: a bound for the host's
time function, given a bound for the solver's. -/
theorem IsHost.solvedIn {lower upper : Task} {time : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ}
    {need : (ℕ → ℕ → Need) → ℕ → ℕ → Need} (h : IsHost lower upper time need) {T T' : ℕ → ℝ → ℝ}
    (hs : SolvedIn lower T)
    (hb : ∀ Tn : ℕ → ℕ → ℕ, (∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤
    T n u) → ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (time Tn n U : ℝ) ≤ T' n u) :
    SolvedIn upper T' := by
  obtain ⟨P, p, Tn, r, hr, hsol, hT⟩ := hs
  obtain ⟨R, p', hsol'⟩ := h.1 P p Tn r hsol
  exact ⟨P ++ R, p', time Tn, need r, h.2 r hr, hsol', hb Tn hT⟩

/-! ## Tasks with a list of parameters -/























/-- A solver stays a solver when procedures are appended to its program. -/
theorem SolvesN.append {task : TaskN} {P : Program} {p : ℕ} {T : List ℕ → ℕ} {need : List ℕ → Need}
    (h : SolvesN task P p T need) (R : Program) : SolvesN task (P ++ R) p T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, getElem?_append_of_eq_some hp R, fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact hb (R ++ R') lim d x μ fr hpre hok

/-- A solver meets the specification of its task, at the depth d at which it runs. -/
theorem SolvesN.meets {task : TaskN} {P₀ : Program} {p : ℕ} {T₀ : List ℕ → ℕ}
    {need : List ℕ → Need} (h : SolvesN task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ}
    (x : task.Inst) {μ : ℕ → ℤ} {fr : ℕ} (hpre : task.Pre x μ fr)
    (hok : (need (task.pars x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.pars x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩






end Light

end
end

section


/-!
# The answer of a decision problem as a number

A routine for a decision problem returns 1 for yes and 0 for no: `flag p` is this number for the
proposition `p`.
-/

@[expose] public section

namespace ThreeSumApsp

















/-- Equivalent questions have the same answer. -/
theorem flag_congr {p q : Prop} (h : p ↔ q) : flag p = flag q := by
  rw [propext h]







end ThreeSumApsp

end
end

section


/-!
# The problems of the paper as tasks

* The problems for Section 3.4 have a size and a bound (`Task`).
* The problems of Theorem 5 and of Section 3.1 have the parameters `N`, `D`, `w` and `U` (`TaskN`).
  The calling convention is the same: sizes, the bound, the addresses of the arrays, the address of
  the output, and the free pointer last.  The three tasks: the wanted entries of a thin matrix
  product (`thinTask`; Theorem 5 and Corollary 26), #Lop-AE-SparseTri (`lopCountTask`;
  Definition 14) and Lop-AE-SparseTri (`lopDetectTask`; Definition 13).  All three have the same
  instances (`ThinInst`).
* What "solved in time `T`" means for them: `ThinSolvedIn`, `LopSolvedIn`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

open ThreeSumApsp.Spec

/-! ## The problems for Section 3.4 -/



































/-- The free pointer may grow. -/
theorem TriInst.Pre.mono {x : TriInst} {μ : ℕ → ℤ} {fr fr' : ℕ} (h : x.Pre μ fr) (hfr : fr ≤ fr') :
    x.Pre μ fr' :=
  { h with
    belowAB := h.belowAB.trans hfr
    belowBC := h.belowBC.trans hfr
    belowAC := h.belowAC.trans hfr }























































































































































/-! ## The thin matrix product and the lopsided triangle problems -/




























































/-! The ten arguments of a procedure for one of these tasks, as local variables. -/

namespace ThinArg






















end ThinArg

























































end Light

end
end

section


@[expose] public section

namespace APSPImprovement

open Light ThreeSumApsp ThreeSumApsp.Spec

/-- The input matrices of Exact Triangle together with a separate output region. -/
structure AllEdgesInst extends TriInst where
  out : ℕ

structure AllEdgesInst.Pre (x : AllEdgesInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop
    extends TriInst.Pre x.toTriInst μ fr where
  belowOut : x.out + x.n * x.n ≤ fr
  apartAB : Apart x.ab (x.n * x.n) x.out (x.n * x.n)
  apartBC : Apart x.bc (x.n * x.n) x.out (x.n * x.n)
  apartAC : Apart x.ac (x.n * x.n) x.out (x.n * x.n)

theorem AllEdgesInst.Pre.keep {x : AllEdgesInst} {μ μ' : ℕ → ℤ} {fr : ℕ}
    (h : x.Pre μ fr) (hs : KeptBut μ μ' fr x.out (x.n * x.n) := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_85803_0 apspMacro_85803_1);
                                                                        (first
                                                                          |
                                                                            ((((repeat
                                                                                      (((with_reducible
                                                                                              rename Light.SameOn _ _ _ => apspMacro_85803_2));
                                                                                        ((try
                                                                                              have :=
                                                                                                apspMacro_85803_2 apspMacro_85803_0 (by omega)));
                                                                                        (revert apspMacro_85803_2)));
                                                                                  (intros);
                                                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                              (omega))
                                                                          |
                                                                            ((simp [] at apspMacro_85803_1);
                                                                              (((repeat
                                                                                      (((with_reducible
                                                                                              rename Light.SameOn _ _ _ => apspMacro_85803_3));
                                                                                        ((try
                                                                                              have :=
                                                                                                apspMacro_85803_3 apspMacro_85803_0 (by omega)));
                                                                                        (revert apspMacro_85803_3)));
                                                                                  (intros);
                                                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                              (omega))
                                                                          |
                                                                            ((((repeat
                                                                                      (((with_reducible
                                                                                              rename Light.SameOn _ _ _ => apspMacro_85803_4));
                                                                                        ((try
                                                                                              have :=
                                                                                                apspMacro_85803_4 apspMacro_85803_0 (by omega)));
                                                                                        (revert apspMacro_85803_4)));
                                                                                  (intros);
                                                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                              (fail
                                                                                  "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                            its condition K x does not follow from the hypotheses."))))) :
    x.Pre μ' fr := by
  (obtain ⟨⟩ := id h.toPre)
  (obtain ⟨⟩ := id h)
  exact { h with segAB := h.segAB.keep, segBC := h.segBC.keep, segAC := h.segAC.keep }

/-- Flags for the AB edge family, indexed by `(a,b)` in row-major order. -/
noncomputable def abZeroFlags (n : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    flag (∃ c < n, AB.getD q 0 + BC.getD ((q % n) * n + c) 0 +
      AC.getD ((q / n) * n + c) 0 = 0)

/-- Flags for the AC edge family, indexed by `(a,c)` in row-major order. -/
noncomputable def acZeroFlags (n : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    flag (∃ b < n, AB.getD ((q / n) * n + b) 0 + BC.getD (b * n + q % n) 0 +
      AC.getD q 0 = 0)

noncomputable def allEdgesTask : Task where
  Inst := AllEdgesInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.out]
  Pre := AllEdgesInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (abZeroFlags x.n x.AB x.BC x.AC) ∧
    KeptBut μ μ' fr x.out (x.n * x.n)










@[simp] theorem abZeroFlags_length (n : ℕ) (AB BC AC : List ℤ) :
    (abZeroFlags n AB BC AC).length = n * n := by simp [abZeroFlags]

@[simp] theorem acZeroFlags_length (n : ℕ) (AB BC AC : List ℤ) :
    (acZeroFlags n AB BC AC).length = n * n := by simp [acZeroFlags]

end APSPImprovement

end
end

section


@[expose] public section

namespace APSPImprovement

open Light ThreeSumApsp ThreeSumApsp.Spec

/-- The public all-edges layout requires three disjoint flag blocks. -/
structure AllEdgesInst.FullPre (x : AllEdgesInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop
    extends TriInst.Pre x.toTriInst μ fr where
  belowOut : x.out + 3 * (x.n * x.n) ≤ fr
  apartAB : Apart x.ab (x.n * x.n) x.out (3 * (x.n * x.n))
  apartBC : Apart x.bc (x.n * x.n) x.out (3 * (x.n * x.n))
  apartAC : Apart x.ac (x.n * x.n) x.out (3 * (x.n * x.n))

theorem AllEdgesInst.FullPre.keep {x : AllEdgesInst} {μ μ' : ℕ → ℤ} {fr : ℕ}
    (h : x.FullPre μ fr) (hs : KeptBut μ μ' fr x.out (3 * (x.n * x.n)) := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_87859_0 apspMacro_87859_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_87859_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_87859_2 apspMacro_87859_0 (by omega)));
                                                                                                  (revert apspMacro_87859_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_87859_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_87859_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_87859_3 apspMacro_87859_0 (by omega)));
                                                                                                  (revert apspMacro_87859_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_87859_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_87859_4 apspMacro_87859_0 (by omega)));
                                                                                                  (revert apspMacro_87859_4)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (fail
                                                                                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))) :
    x.FullPre μ' fr := by
  (obtain ⟨⟩ := id h.toPre)
  (obtain ⟨⟩ := id h)
  exact { h with segAB := h.segAB.keep, segBC := h.segBC.keep, segAC := h.segAC.keep }

/-- The first output block is a legal one-orientation task output. -/
theorem AllEdgesInst.FullPre.abPre {x : AllEdgesInst} {μ : ℕ → ℤ} {fr : ℕ}
    (h : x.FullPre μ fr) : x.Pre μ fr := by
  refine { h.toPre with belowOut := ?_, apartAB := ?_, apartBC := ?_, apartAC := ?_ }
  · have := h.belowOut
    omega
  · rcases h.apartAB with hl | hr
    · exact Or.inl hl
    · exact Or.inr (by omega)
  · rcases h.apartBC with hl | hr
    · exact Or.inl hl
    · exact Or.inr (by omega)
  · rcases h.apartAC with hl | hr
    · exact Or.inl hl
    · exact Or.inr (by omega)

/-- Flags for the BC edge family, in `(b,c)` row-major order. -/
noncomputable def bcZeroFlags (n : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    flag (∃ a < n, AB.getD (a * n + q / n) 0 + BC.getD q 0 +
      AC.getD (a * n + q % n) 0 = 0)

/-- Exactly the public ordering: first AB, then BC, then AC. -/
noncomputable def fullZeroFlags (n : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  abZeroFlags n AB BC AC ++ bcZeroFlags n AB BC AC ++ acZeroFlags n AB BC AC

@[simp] theorem bcZeroFlags_length (n : ℕ) (AB BC AC : List ℤ) :
    (bcZeroFlags n AB BC AC).length = n * n := by simp [bcZeroFlags]







/-- A composable Light task computing all three public output blocks. -/
noncomputable def fullAllEdgesTask : Task where
  Inst := AllEdgesInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.out]
  Pre := AllEdgesInst.FullPre
  Post x μ fr _ μ' := Seg μ' x.out (fullZeroFlags x.n x.AB x.BC x.AC) ∧
    KeptBut μ μ' fr x.out (3 * (x.n * x.n))

end APSPImprovement

end
end

section


/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/








































/-! ## Configurations and single steps -/






















/-! ## Runs -/




























/-- Within no steps there is no verdict. -/
theorem exec_zero (c : Cfg W) : exec P 0 c.pc c.mem = none := by rw [exec]

private theorem exec_succ (t : ℕ) (c : Cfg W) : exec P (t + 1) c.pc c.mem =
    match step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => exec P t next.pc next.mem := by
  rw [exec, step]
  cases P.getD c.pc .reject <;> rfl

/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {c : Cfg W} {v : Bool} (h : step P c = .inr v) (t : ℕ) :
    exec P (t + 1) c.pc c.mem = some (v, c.mem) := by rw [exec_succ, h]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step {c c' : Cfg W} (h : step P c = .inl c') (t : ℕ) :
    exec P (t + 1) c.pc c.mem = exec P t c'.pc c'.mem := by rw [exec_succ, h]













/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {c : Cfg W} {r : Bool × (ℤ → BitVec W)}
    (h : exec P t c.pc c.mem = some r) (ht : t ≤ t') : exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => simp [exec_zero] at h
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : step P c with
    | inr v => rwa [exec_succ_of_verdict hs] at h ⊢
    | inl n =>
      rw [exec_succ_of_step hs] at h ⊢
      exact ih h (by omega)

/-! ## Pieces of code -/





































/-! ## Straight-line code -/





















































/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

















































end known

/-! ## Branches and verdicts -/























/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}






















































end framing

end ThreeSumApsp.WordRam

end
end

section


/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp






namespace Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/

/-- A bound with an explicit nonnegative constant. -/
theorem of_le_const_mul {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩

/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩

/-- Every function is bounded by itself. -/
protected theorem refl (dom : α → Prop) (f : α → ℝ) : Dominated dom f f :=
  of_le fun _ _ => le_rfl

/-- A bound with a constant of unknown sign, when `g` is nonnegative on the domain. -/
theorem of_exists_const (hfg : ∃ C : ℝ, ∀ x, dom x → f x ≤ C * g x) (hg : ∀ x, dom x → 0 ≤ g x) :
    Dominated dom f g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨|C|, abs_nonneg C, fun x hx =>
    (hC x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hg x hx))⟩











/-- A constant is `O(g)` when `g ≥ 1` on the domain. -/
protected theorem const (c : ℝ) (hg : ∀ x, dom x → 1 ≤ g x) : Dominated dom (fun _ => c) g :=
  ⟨|c|, abs_nonneg c, fun x hx =>
    (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) (hg x hx))⟩

/-! ### Leaving the calculus -/

/-- Two bounds, by nonnegative functions, hold with one constant. -/
theorem exists_const_and (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hg₁ : ∀ x, dom x → 0 ≤ g₁ x) (hg₂ : ∀ x, dom x → 0 ≤ g₂ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, dom x → f₁ x ≤ C * g₁ x ∧ f₂ x ≤ C * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  exact ⟨C + D, add_nonneg hC hD, fun x hx =>
    ⟨(h₁ x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (hg₁ x hx)),
      (h₂ x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (hg₂ x hx))⟩⟩

/-! ### Chaining, restricting, substituting -/

/-- `f = O(g)` and `g = O(h)` give `f = O(h)`. -/
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC

/-- A bound holds on every smaller domain. -/
theorem mono_dom (hfg : Dominated dom f g) (hdom : ∀ x, dom' x → dom x) : Dominated dom' f g := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun x hx => hf x (hdom x hx)⟩

/-- The left side may be replaced by a smaller function. -/
theorem mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g :=
  (of_le hle).trans hfg

/-- The right side may be replaced by a larger function. -/
theorem mono_right (hfg : Dominated dom f g) (hle : ∀ x, dom x → g x ≤ g' x) : Dominated dom f g' :=
  hfg.trans (of_le hle)

/-- Both sides may be replaced by functions that agree with them on the domain. -/
protected theorem congr (hfg : Dominated dom f g) (hf : ∀ x, dom x → f x = f' x)
    (hg : ∀ x, dom x → g x = g' x) : Dominated dom f' g' :=
  (hfg.mono_left fun x hx => (hf x hx).ge).mono_right fun x hx => (hg x hx).le

/-- Substituting the parameters: a bound in `x` gives a bound in `y` at `x = φ y`, on every domain
that `φ` maps into `dom`. -/
protected theorem comp (hfg : Dominated dom f g) (φ : β → α) {dom' : β → Prop}
    (hφ : ∀ y, dom' y → dom (φ y)) : Dominated dom' (fun y => f (φ y)) fun y => g (φ y) := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun y hy => hf (φ y) (hφ y hy)⟩

/-! ### Sums and case distinctions -/

/-- `O(h) + O(h) = O(h)`. -/
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)







/-- A case distinction: a bound on `f₁` where `p` holds and a bound on `f₂` where it does not, both
by the same nonnegative `g`. -/
protected theorem ite {p : α → Prop} [DecidablePred p]
    (h₁ : Dominated (fun x => dom x ∧ p x) f₁ g) (h₂ : Dominated (fun x => dom x ∧ ¬p x) f₂ g)
    (hg : ∀ x, dom x → 0 ≤ g x) : Dominated dom (fun x => if p x then f₁ x else f₂ x) g := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  change (if p x then f₁ x else f₂ x) ≤ (C + D) * g x
  split_ifs with hp
  · exact (h₁ x ⟨hx, hp⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (hg x hx))
  · exact (h₂ x ⟨hx, hp⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (hg x hx))

/-! ### Products and quotients -/

/-- A nonnegative constant factor on the left side is absorbed. -/
theorem const_mul (hfg : Dominated dom f g) {c : ℝ} (hc : 0 ≤ c) :
    Dominated dom (fun x => c * f x) g := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨c * C, mul_nonneg hc hC, fun x hx => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx) hc






/-- A constant factor of any sign in front of a function that is nonnegative on the domain is
absorbed. -/
theorem const_mul_of_nonneg (hfg : Dominated dom f g) (c : ℝ) (hf : ∀ x, dom x → 0 ≤ f x) :
    Dominated dom (fun x => c * f x) g :=
  (of_exists_const ⟨c, fun _ _ => le_rfl⟩ hf).trans hfg



















/-- `O(g₁) · O(g₂) = O(g₁ g₂)` for nonnegative `f₁`, `f₂`. -/
protected theorem mul (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hf₁ : ∀ x, dom x → 0 ≤ f₁ x) (hf₂ : ∀ x, dom x → 0 ≤ f₂ x) :
    Dominated dom (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => ?_⟩
  rw [mul_mul_mul_comm]
  exact mul_le_mul (h₁ x hx) (h₂ x hx) (hf₂ x hx) ((hf₁ x hx).trans (h₁ x hx))

/-- `O(g) ^ e = O(g ^ e)` for nonnegative `f`. -/
protected theorem pow (hfg : Dominated dom f g) (hf : ∀ x, dom x → 0 ≤ f x) (e : ℕ) :
    Dominated dom (fun x => f x ^ e) fun x => g x ^ e := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine ⟨C ^ e, pow_nonneg hC e, fun x hx => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hf x hx) (hle x hx) e

/-! ### Functions of one natural number -/






















/-- A bound by a nonnegative `g` that holds from some unknown point on gives a bound by `g + 1`
everywhere. -/
theorem of_eventually_add_one {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n)
    (hg : ∀ n, 0 ≤ g n) : Dominated (fun _ => True) f fun n => g n + 1 := by
  have hpos : ∀ n, 0 ≤ n → 0 < g n + 1 := fun n _ => add_pos_of_nonneg_of_pos (hg n) zero_lt_one
  refine (of_eventually (C := |C|) (hfg.mono fun n hn => hn.trans ?_) hpos).mono_dom
    fun n _ => n.zero_le
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (hg n)).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg C))









end Dominated












end ThreeSumApsp

end
end

section


/-!
# Powers of `n` and of `log n` for large `n`

The facts behind the paper's `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`, for functions of a natural number
`n` and in the language of Mathlib's `f =O[atTop] g`. Powers of `n` are monotone in the exponent
(`isBigO_rpow_rpow_of_le`, `isBigO_rpow_mul_log_pow_of_le`) and multiply by adding exponents
(`rpow_mul_rpow_eventuallyEq`). A constant or a power of `log n` is below every positive power of
`n` (`eventually_le_rpow`, `isLittleO_log_pow_rpow`). Hence `n ^ a * (log n) ^ e` is `o(n ^ b)` and
`O(n ^ b)` for `a < b` (`isLittleO_rpow_mul_log_pow_rpow`, `isBigO_rpow_mul_log_pow_rpow`), which is
where logarithms are absorbed for large `n`; with the constant absorbed too, this is
`eventually_mul_rpow_mul_log_pow_le`. The rounded power `⌈n ^ μ⌉` tends to infinity for `μ > 0`
(`tendsto_ceil_rpow_atTop`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

/-- A bound `|f n| ≤ C * g n` from some `n₀` on gives `f = O(g)`. -/
theorem isBigO_of_abs_le {f g : ℕ → ℝ} (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * g n) :
    f =O[atTop] g := by
  refine IsBigO.of_bound |C| (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
  exact (h n hn).trans (le_abs_self _)










/-- `n ^ a = O(n ^ b)` for `a ≤ b`. -/
theorem isBigO_rpow_rpow_of_le {a b : ℝ} (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  refine isBigO_of_abs_le 1 1 fun n hn => ?_
  rw [one_mul, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)]
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hab

/-- `n ^ a * n ^ b = n ^ (a + b)` for all large `n`. -/
theorem rpow_mul_rpow_eventuallyEq (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (a + b) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_add (Nat.cast_pos.2 hn)]

/-- `(log n) ^ e = o(n ^ η)` for `η > 0`. -/
theorem isLittleO_log_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    (fun n : ℕ => Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ η := by
  have h := (isLittleO_log_rpow_rpow_atTop (e : ℝ) hη).comp_tendsto tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast] using h

/-- `(log n) ^ e = O((log n) ^ e')` for `e ≤ e'`. -/
theorem isBigO_log_pow_log_pow_of_le {e e' : ℕ} (he : e ≤ e') :
    (fun n : ℕ => Real.log n ^ e) =O[atTop] fun n : ℕ => Real.log n ^ e' := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hlog
  refine isBigO_of_abs_le 1 n₀ fun n hn => ?_
  rw [one_mul, abs_of_nonneg (pow_nonneg (zero_le_one.trans (hn₀ n hn)) e)]
  exact pow_le_pow_right₀ (hn₀ n hn) he

/-- `n ^ a * (log n) ^ e = O(n ^ b * (log n) ^ e')` for `a ≤ b` and `e ≤ e'`. -/
theorem isBigO_rpow_mul_log_pow_of_le {a b : ℝ} {e e' : ℕ} (hab : a ≤ b) (he : e ≤ e') :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ b * Real.log n ^ e' :=
  (isBigO_rpow_rpow_of_le hab).mul (isBigO_log_pow_log_pow_of_le he)

/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = o(n ^ b)` for `a < b`. -/
theorem isLittleO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a) atTop).mul_isLittleO
    (isLittleO_log_pow_rpow (sub_pos.2 hab) e)
  refine h.congr' EventuallyEq.rfl ?_
  simpa only [add_sub_cancel] using rpow_mul_rpow_eventuallyEq a (b - a)






/-- Constants are absorbed as well: `C * (n ^ a * (log n) ^ e) ≤ n ^ b` for all large `n`, if
`a < b`. -/
theorem eventually_mul_rpow_mul_log_pow_le (C : ℝ) {a b : ℝ} (hab : a < b) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) ^ a * Real.log n ^ e) ≤ (n : ℝ) ^ b := by
  have h := ((isLittleO_rpow_mul_log_pow_rpow hab e).const_mul_left C).def zero_lt_one
  filter_upwards [h] with n hn
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg b)] at hn
  exact (le_abs_self _).trans hn






end ThreeSumApsp

end
end

section


/-!
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)
open Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/




























/-- `EndStatement.Problem.SolvedBy` counts the output cells as `1 + len + i`, and `output` counts
them as `(len + 1) + i`. -/
theorem output_cons {W : ℕ} (c : ℤ → BitVec W) (n : ℤ) (l : List ℤ) :
    (fun i : ℕ => (c ((1 + l.length + i : ℕ) : ℤ)).toInt) = output c (n :: l).length := by
  funext i
  simp only [output, List.length_cons, Nat.add_comm 1]
  rfl

/-- `SolvesWithin` is `Solves` for the problem `ofEnd Q`, on the instances with `U = n^κ`. -/
theorem solvesWithin_iff {Q : EndStatement.Problem} {κ : ℕ} {P : List Instr} {b : ℕ} {T : ℕ → ℝ} :
    SolvesWithin Q κ P b T ↔ Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ) fun x => T x.n := by
  constructor
  · intro h x hx bits hbits
    obtain ⟨t, ht, verdict, m, hexec, hyes, hout⟩ :=
      h x.n x.x (hx ▸ x.bounded) bits (by simpa [Admissible] using hbits)
    exact ⟨t, verdict, m, ht, hexec, hyes, output_cons m x.n (Q.input x.x) ▸ hout⟩
  · intro h n x hx W hW
    obtain ⟨t, verdict, c, ht, hrun, hyes, hout⟩ :=
      h ⟨n, n ^ κ, x, hx⟩ rfl W (by simpa [Admissible] using hW)
    exact ⟨t, ht, verdict, c, hrun, hyes, (output_cons c n (Q.input x)).symm ▸ hout⟩

/-- `SolvedInTimeAt` in terms of `Solves`. -/
theorem solvedInTimeAt_iff {Q : EndStatement.Problem} {κ : ℕ} {a : ℝ} {e : ℕ} :
    SolvedInTimeAt Q κ a e ↔ ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ)
        fun x => C * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1) := by
  simp only [SolvedInTimeAt, solvesWithin_iff]

/-! ## Monotonicity -/

/-- `Solves` stays true for a larger slope, a smaller set of instances and a larger time bound. -/
theorem Solves.mono {prob : Problem} {P : List Instr} {b b' : ℕ} {dom dom' : prob.Inst → Prop}
    {T T' : prob.Inst → ℝ} (h : _root_.ThreeSumApsp.WordRam.Solves prob P b dom T) (hb : b ≤ b') (hdom : ∀ x, dom' x → dom x)
    (hT : ∀ x, dom' x → T x ≤ T' x) : _root_.ThreeSumApsp.WordRam.Solves prob P b' dom' T' := by
  intro x hx bits hadm
  obtain ⟨t, verdict, c, ht, he, ha⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  exact ⟨t, verdict, c, ht.trans (hT x hx), he, ha⟩



















/-! ## Bounds up to a constant -/

/-- A program that solves a problem in time `O(f)` solves it in time `O(f')` if `f = O(f')`. -/
theorem exists_solves_of_dominated {prob : Problem} {dom dom' : prob.Inst → Prop}
    {f f' : prob.Inst → ℝ}
    (h : ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom fun x => C * f x)
    (hdom : ∀ x, dom' x → dom x) (hf : Dominated dom' f f')
    (hf0 : ∀ x, dom' x → 0 ≤ f x := by intro _ _; positivity) :
    ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom' fun x => C * f' x := by
  obtain ⟨P, b, C, h⟩ := h
  obtain ⟨K, -, hf⟩ := hf.const_mul_of_nonneg C hf0
  exact ⟨P, b, K, h.mono le_rfl hdom hf⟩






















/-! ## Bounds in one size -/

/-- The bound `O(n^a (log n)^e)` may be replaced by a bound `O(n^a' (log n)^e')` that is at least as
large, up to a constant, for all large `n`. -/
theorem SolvedInTimeAt.of_eventually_le {Q : EndStatement.Problem} {κ : ℕ} {a a' C : ℝ} {e e' : ℕ}
    (h : SolvedInTimeAt Q κ a e)
    (hle : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ a * Real.log n ^ e ≤ C * ((n : ℝ) ^ a' * Real.log n ^ e')) :
    SolvedInTimeAt Q κ a' e' := by
  have hall : Dominated (fun _ : ℕ => True) (fun n => (n : ℝ) ^ a * Real.log n ^ e + 1)
      fun n => (n : ℝ) ^ a' * Real.log n ^ e' + 1 :=
    (Dominated.of_eventually_add_one hle fun n => by positivity).add
      (.of_le fun n _ => le_add_of_nonneg_left (by positivity))
  exact solvedInTimeAt_iff.2 (exists_solves_of_dominated (solvedInTimeAt_iff.1 h) (fun _ hx => hx)
    (hall.comp (fun x : Bounded Q => x.n) fun _ _ => trivial))













/-- A bound `O(n^a (log n)^{O(1)})` is a bound `O(n^a')` for `a < a'`. -/
theorem SolvedInPolylogTime.solvedInTime {Q : EndStatement.Problem} {a a' : ℝ}
    (h : SolvedInPolylogTime Q a) (ha : a < a') : SolvedInTime Q a' 0 := fun κ =>
  let ⟨e, he⟩ := h κ
  he.of_eventually_le (C := 1) <| by
    simpa only [one_mul, pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le 1 ha e

end ThreeSumApsp.WordRam

end
end

section


/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/

/-- `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
`b * k` on the right. -/
theorem ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]

/-- `i < a ⌈/⌉ b` says that `i` pieces of size `b` do not cover `a`. -/
theorem lt_ceilDiv_iff {a b i : ℕ} (hb : 0 < b) : i < a ⌈/⌉ b ↔ i * b < a := by
  rw [← Nat.not_le, ceilDiv_le_iff hb, Nat.not_le]





/-- `a ⌈/⌉ b` pieces of size `b` overshoot `a` by less than one piece. -/
theorem ceilDiv_mul_lt {a b : ℕ} (hb : 0 < b) : a ⌈/⌉ b * b < a + b := by
  have := Nat.div_mul_le_self (a + b - 1) b
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega





/-- The ceiling of the real quotient of two natural numbers, in natural numbers. -/
theorem ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff hb]
  exact_mod_cast Iff.rfl

/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/

/-- Rounding `n ≥ 1` up to a power of `b` costs at most a factor `b`. -/
theorem pow_clog_le_mul {b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n) : b ^ Nat.clog b n ≤ b * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp [Nat.clog_one_right, hb.le]
  · have hpos : 0 < Nat.clog b n := Nat.clog_pos hb hn
    have hlt := Nat.pow_pred_clog_lt_self hb hn
    calc b ^ Nat.clog b n = b * b ^ (Nat.clog b n).pred := by
          rw [← Nat.pow_succ', Nat.succ_pred_eq_of_pos hpos]
      _ ≤ b * n := Nat.mul_le_mul_left b hlt.le

end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/

/-- `x` is at most the `e`-th root of `t` exactly if `x ^ e ≤ t`. -/
theorem natCast_le_rpow_inv_iff {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (x : ℝ) ≤ (t : ℝ) ^ ((e : ℝ)⁻¹) ↔ x ^ e ≤ t := by
  rw [Real.le_rpow_inv_iff_of_pos x.cast_nonneg t.cast_nonneg
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- The `e`-th root of `t` is at most `x` exactly if `t ≤ x ^ e`. -/
theorem rpow_inv_le_natCast_iff {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (t : ℝ) ^ ((e : ℝ)⁻¹) ≤ (x : ℝ) ↔ t ≤ x ^ e := by
  rw [Real.rpow_inv_le_iff_of_pos t.cast_nonneg x.cast_nonneg
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

end Real

namespace ThreeSumApsp




end ThreeSumApsp

end
end

section


/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/

































/-- The exponent of Strassen's algorithm: `log₂ 7 < 59 / 21 < 2.81`, because `7 ^ 21 < 2 ^ 59`. -/
theorem logb_two_seven_lt : logb 2 7 < 2.81 := by
  have hpow : ((2 : ℝ) ^ (59 / 21 : ℝ)) ^ 21 = 2 ^ 59 := by
    rw [← rpow_natCast, ← rpow_mul two_pos.le, ← rpow_natCast]
    norm_num
  have hlt : (7 : ℝ) < 2 ^ (59 / 21 : ℝ) :=
    lt_of_pow_lt_pow_left₀ 21 (rpow_nonneg two_pos.le _) (by rw [hpow]; norm_num)
  exact ((logb_lt_iff_lt_rpow one_lt_two (by norm_num)).2 hlt).trans (by norm_num)





/-! ### The rounded logarithm `Nat.clog` -/




















end Real

namespace ThreeSumApsp






end ThreeSumApsp

end
end

section


/-!
# Calculating with `O(n^a)` and `Õ(n^a)`

Closure properties of the two classes `IsBigOPow f a`, that is `f(n) = O(n^a)`, and
`IsPowPolylog f a`, that is `f(n) = O(n^a (log n)^{O(1)})`, which the paper writes `Õ(n^a)`.

A bound enters by `of_abs_le`, by `of_isBigO`, or from the model functions (`isBigOPow_rpow`,
`isBigOPow_natCast_pow`, `isBigOPow_const`, `isPowPolylog_rpow_mul_log_pow`, `isPowPolylog_log_pow`,
and for rounded powers `isBigOPow_ceil_rpow`, `isBigOPow_floor_rpow` and their inverses;
`IsBigOPow.natCeil` for rounding in general). Both classes are closed under sums, constant factors
and passing to a smaller function (`mono_left`). A product has the exponent `a + b` and a power the
exponent `a * k` (`pow`, `rpow`), to be brought to the wanted form by `mono`, which asks only for an
inequality between exponents. Substituting `n ↦ size n` multiplies nonnegative exponents
(`IsBigOPow.comp`, `IsPowPolylog.comp`), for `size n = O(n^μ)`, and then `log (size n) = Õ(1)`
(`IsBigOPow.isPowPolylog_log_natCast`). The classes are related by `IsBigOPow.isPowPolylog` and,
with a loss in the exponent, `IsPowPolylog.isBigOPow`; `eventually_abs_le` absorbs the constant as
well.
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` -/

/-- `n ^ a = O(n^a)`. -/
theorem isBigOPow_rpow (a : ℝ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ a) a :=
  isBigO_refl _ _

/-- `n ^ k = O(n^k)` for a natural number `k`. -/
theorem isBigOPow_natCast_pow (k : ℕ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ k) k := by
  simpa only [Real.rpow_natCast] using isBigOPow_rpow (k : ℝ)





/-- A constant is `O(n^0)`. -/
theorem isBigOPow_const (c : ℝ) : IsBigOPow (fun _ => c) 0 :=
  isBigO_of_abs_le |c| 0 fun n _ => by rw [Real.rpow_zero, mul_one]

namespace IsBigOPow



























































/-- `O(n^a) ⊆ Õ(n^a)`. -/
theorem isPowPolylog (hf : IsBigOPow f a) : IsPowPolylog f a :=
  ⟨0, by simpa only [pow_zero, mul_one, IsBigOPow] using hf⟩

end IsBigOPow








































/-! ### `Õ(n^a)` -/

/-- `n ^ a * (log n) ^ e = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) a :=
  ⟨e, isBigO_refl _ _⟩






/-- `n ^ a = Õ(n^a)`. -/
theorem isPowPolylog_rpow (a : ℝ) : IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a) a :=
  (isBigOPow_rpow a).isPowPolylog

/-- `(log n) ^ e = Õ(1)`. -/
theorem isPowPolylog_log_pow (e : ℕ) : IsPowPolylog (fun n : ℕ => Real.log n ^ e) 0 :=
  ⟨e, by simpa only [Real.rpow_zero, one_mul] using isBigO_refl (fun n : ℕ => Real.log n ^ e) atTop⟩

/-- `log n = Õ(1)`. -/
theorem isPowPolylog_log : IsPowPolylog (fun n : ℕ => Real.log n) 0 := by
  simpa only [pow_one] using isPowPolylog_log_pow 1

/-- A constant is `Õ(1)`. -/
theorem isPowPolylog_const (c : ℝ) : IsPowPolylog (fun _ => c) 0 :=
  (isBigOPow_const c).isPowPolylog

namespace IsPowPolylog






/-- If `g = Õ(n^a)` and `f = O(g)`, then `f = Õ(n^a)`. -/
theorem of_isBigO (hg : IsPowPolylog g a) (hfg : f =O[atTop] g) : IsPowPolylog f a := by
  obtain ⟨e, hg⟩ := hg
  exact ⟨e, hfg.trans hg⟩

/-- If `|f n| ≤ |g n|` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left (hg : IsPowPolylog g a) (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsPowPolylog f a :=
  hg.of_isBigO (IsBigO.of_bound' h)

/-- If `0 ≤ f n ≤ g n` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left_of_nonneg (hg : IsPowPolylog g a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsPowPolylog f a :=
  hg.mono_left ((h0.and h).mono fun _ hn => abs_le_abs_of_nonneg hn.1 hn.2)

/-- The exponent may be raised. -/
protected theorem mono (hf : IsPowPolylog f a) (hab : a ≤ b) : IsPowPolylog f b := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.trans (isBigO_rpow_mul_log_pow_of_le hab le_rfl)⟩

/-- `Õ(n^a) + Õ(n^a) = Õ(n^a)`. -/
protected theorem add (hf : IsPowPolylog f a) (hg : IsPowPolylog g a) :
    IsPowPolylog (fun n => f n + g n) a := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  exact ⟨max e₁ e₂, (hf.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_left _ _))).add
    (hg.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_right _ _)))⟩

/-- Constant factors are absorbed. -/
theorem const_mul (hf : IsPowPolylog f a) (c : ℝ) : IsPowPolylog (fun n => c * f n) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.const_mul_left c⟩





/-- `Õ(n^a) · Õ(n^b) = Õ(n^(a+b))`. -/
protected theorem mul (hf : IsPowPolylog f a) (hg : IsPowPolylog g b) :
    IsPowPolylog (fun n => f n * g n) (a + b) := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  refine ⟨e₁ + e₂, (hf.mul hg).congr' EventuallyEq.rfl ?_⟩
  filter_upwards [rpow_mul_rpow_eventuallyEq a b] with n hn
  rw [← hn, pow_add, mul_mul_mul_comm]

/-- `Õ(n^a) ^ k = Õ(n^(a k))` for a natural number `k`. -/
protected theorem pow (hf : IsPowPolylog f a) (k : ℕ) :
    IsPowPolylog (fun n => f n ^ k) (a * k) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e * k, (hf.pow k).congr_right fun n => ?_⟩
  rw [mul_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul n.cast_nonneg]



















/-- If `f = Õ(n^a)` then `|f| = Õ(n^a)`. -/
protected theorem abs (hf : IsPowPolylog f a) : IsPowPolylog (fun n => |f n|) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.norm_left⟩

/-- If `f = Õ(n^a)` and `g n = f n` for all large `n`, then `g = Õ(n^a)`. -/
protected theorem congr (hf : IsPowPolylog f a) (h : f =ᶠ[atTop] g) : IsPowPolylog g a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.congr' h EventuallyEq.rfl⟩












end IsPowPolylog






































/-- `n ^ a * (log n + 1) ^ e = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log_add_one_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * (Real.log n + 1) ^ e) a := by
  have h := (isPowPolylog_rpow a).mul ((isPowPolylog_log.add (isPowPolylog_const 1)).pow e)
  rwa [zero_mul, add_zero] at h

/-- `log (c * n ^ κ) = Õ(1)`. -/
theorem isPowPolylog_log_mul_rpow (c κ : ℝ) :
    IsPowPolylog (fun n : ℕ => Real.log (c * (n : ℝ) ^ κ)) 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa only [zero_mul, Real.log_zero] using isPowPolylog_const 0
  · refine ((isPowPolylog_const (Real.log c)).add (isPowPolylog_log.const_mul κ)).congr ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [Real.log_mul hc (Real.rpow_pos_of_pos hpos κ).ne', Real.log_rpow hpos]

end ThreeSumApsp

end
end

section


/-!
# One-sided bounds `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`

A running time is bounded from above only. `UpperBigOPow f a`, `UpperPowPolylog f a` and
`UpperPowLittleO f a` say that `f(n)` is eventually at most `C n^a`, at most `C n^a (log n)^e`, and
at most `n^{a+ε(n)}` with `ε(n) → 0`, where `IsBigOPow`, `IsPowPolylog` and `IsPowLittleO` say this
of `|f(n)|`.

A bound on `|f|` is a bound on `f` (`IsBigOPow.upperBigOPow`), and the function may be replaced by a
smaller one (`mono_left`); these two lemmas have the same names for the three classes. For `Õ(n^a)`
and `n^{a+o(1)}` a bound on `f` is a bound by a nonnegative function of the class that bounds `|f|`
(`UpperPowPolylog.exists_isPowPolylog`). For `Õ(n^a)` the closure properties follow: a bound on `f`
is a bound on `|f|` if `f` is eventually nonnegative (`UpperPowPolylog.isPowPolylog`), sums,
nonnegative constant factors, products with a nonnegative factor, a larger exponent (`mono`).
Logarithms and the `o(1)` are absorbed by a strictly larger exponent
(`UpperPowPolylog.upperBigOPow`, `UpperPowLittleO.upperBigOPow`).
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp















variable {f f' g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` from above -/








namespace UpperBigOPow






end UpperBigOPow

/-! ### `Õ(n^a)` from above -/

/-- `f = Õ(n^a)` is in particular an upper bound on `f`. -/
theorem IsPowPolylog.upperPowPolylog (hf : IsPowPolylog f a) : UpperPowPolylog f a := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨C, hC⟩ := hf.bound
  refine ⟨C, e, hC.mono fun n hn => ?_⟩
  have hnonneg : 0 ≤ (n : ℝ) ^ a * Real.log n ^ e :=
    mul_nonneg (Real.rpow_nonneg n.cast_nonneg a) (pow_nonneg (Real.log_natCast_nonneg n) e)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  exact (le_abs_self _).trans hn

namespace UpperPowPolylog

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperPowPolylog f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowPolylog f' a := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨C, e, (hle.and hC).mono fun n hn => hn.1.trans hn.2⟩

/-- An upper bound `Õ(n^a)` is a bound by a nonnegative function of the class `Õ(n^a)`. -/
theorem exists_isPowPolylog (h : UpperPowPolylog f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowPolylog g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨fun n => |C * ((n : ℝ) ^ a * Real.log n ^ e)|, fun n => abs_nonneg _,
    ((isPowPolylog_rpow_mul_log_pow a e).const_mul C).abs,
    hC.mono fun n hn => hn.trans (le_abs_self _)⟩












/-- `Õ(n^a) + Õ(n^a) = Õ(n^a)`, from above. -/
protected theorem add (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g a) :
    UpperPowPolylog (fun n => f n + g n) a := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  obtain ⟨G, -, hG, hgG⟩ := hg.exists_isPowPolylog
  exact (hF.add hG).upperPowPolylog.mono_left
    ((hfF.and hgG).mono fun n hn => add_le_add hn.1 hn.2)

/-- Nonnegative constant factors are absorbed. -/
theorem const_mul (hf : UpperPowPolylog f a) {c : ℝ} (hc : 0 ≤ c) :
    UpperPowPolylog (fun n => c * f n) a := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  exact (hF.const_mul c).upperPowPolylog.mono_left
    (hfF.mono fun n hn => mul_le_mul_of_nonneg_left hn hc)














end UpperPowPolylog

/-! ### `n^{a+o(1)}` from above -/






namespace UpperPowLittleO




















end UpperPowLittleO

end ThreeSumApsp

end
end

section


/-!
# From a realized running time to a program with the paper's bound

A claim gives a running time `T` with `T ≤ C X`, where `X` is the bound that the paper prints, and
`RealizedWithin` gives a program that takes `c T + c` steps.  This file puts the two together.

* Bounds in several parameters, valid on a domain on which `X ≥ 1`: `exists_solves`, and
  `exists_solves_nonneg` with `exists_solves_pair` for two programs with one slope and one constant.
* Bounds `O(n^a (log n)^e)` in one size, valid for all large `n`: `solvedAt_of_realized`, and for
  every exponent `κ` of the magnitude `solvedInTime_of_claim` and `solvedInPolylogTime_of_claim`.
* An instance with numbers bounded by `n^κ` is also one with numbers bounded by `n^κ'`, `κ ≤ κ'`
  (`solvedInTimeAt_mono`), so that a bound for all `κ ≥ 1` is a bound for all `κ`
  (`solvedInTime_of_one_le`).
-/

public section

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam
open EndStatement (Instr)

/-! ## Bounds on a domain -/




















































/-! ## Bounds in one size, for all large sizes -/


































/-- A claim "solved in `O(n^a (log n)^{O(1)})` time on numbers of absolute value at most `n^κ`, for
every `κ`", in a reading `S` of "is solved in time T" that is realized, gives programs. -/
theorem solvedInPolylogTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperPowPolylog a) :
    SolvedInPolylogTime Q a := by
  intro κ
  obtain ⟨T, hT, C, e, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact ⟨e, solvedAt_of_realized T κ (hR T hT) hb⟩






















end ThreeSumApsp.FromClaims

end
end

section


/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam






























/-- The rounded bound is `O(n^r)` in the sense of the end statement. -/
theorem bigO_stepBound (C : ℝ) {r : ℚ} (hr0 : 0 ≤ r) : EndStatement.BigO (stepBound C r) r := by
  refine bigO_of_le_rpow (C := 2 * |C| + 1) hr0 fun n hn => ?_
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by exact_mod_cast hr0)
  have habs : C * ((n : ℝ) ^ (r : ℝ) + 1) ≤ |C| * ((n : ℝ) ^ (r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hceil : (stepBound C r n : ℝ) < |C| * ((n : ℝ) ^ (r : ℝ) + 1) + 1 :=
    (Nat.cast_le.2 (Nat.ceil_le_ceil habs)).trans_lt (Nat.ceil_lt_add_one (by positivity))
  -- `|C| (X + 1) + 1 ≤ (2 |C| + 1) X` for `X ≥ 1`
  nlinarith [mul_nonneg (abs_nonneg C) (sub_nonneg.2 hone)]

/-- **A bound `O(n^a)` of an item statement, with `a` the rational `r`, is the bound `O(n^r)` of the
end statement**, with the same program and the same slope. -/
theorem SolvedInTime.endStatement {Q : EndStatement.Problem} {a : ℝ} (h : SolvedInTime Q a 0)
    {r : ℚ} (hr : (r : ℝ) = a) (hr0 : 0 ≤ r) : Q.SolvedInTime r := by
  subst hr
  intro κ
  obtain ⟨P, b, C, hsolves⟩ := h κ
  refine ⟨P, b, stepBound C r, bigO_stepBound C hr0, fun n x hx W hW => ?_⟩
  obtain ⟨t, ht, verdict, c, hrun, hanswer⟩ := hsolves n x hx W hW
  have ht' : t ≤ stepBound C r n := by
    simp only [pow_zero, mul_one] at ht
    exact_mod_cast ht.trans (Nat.le_ceil _)
  exact ⟨verdict, c, WordRam.exec_mono (c := ⟨0, _⟩) hrun ht', hanswer⟩

end ThreeSumApsp.WordRam

end
end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace APSPImprovement

open Light ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec

/-- The source machine uses exactly the new mission's instances and output
predicate. Only the problem record's machine type differs. -/
def AllEdgesSource : EndStatement.Problem where
  Instance := EndStatement.ExactTriangle.Instance
  input := EndStatement.ExactTriangle.input
  output := APSPExponentImprovement.AllEdgesExactTriangle.output

def decisionBounded (x : Bounded AllEdgesSource) : Bounded EndStatement.ExactTriangle :=
  ⟨x.n, x.U, x.x, x.bounded⟩

def fullAllEdgesInst (x : Bounded AllEdgesSource) : AllEdgesInst where
  toTriInst := Light.Sec3.triangleInst (decisionBounded x)
  out := 1 + 3 * (x.n * x.n)

theorem input_allEdges (x : Bounded AllEdgesSource) :
    (ofEnd AllEdgesSource).input x =
      (x.n : ℤ) :: (rowMajor x.x.1 ++ rowMajor x.x.2.1 ++ rowMajor x.x.2.2) :=
  Light.Sec3.input_exactTriangle (decisionBounded x)

theorem input_allEdges_length (x : Bounded AllEdgesSource) :
    ((ofEnd AllEdgesSource).input x).length = 1 + 3 * (x.n * x.n) := by
  rw [input_allEdges]
  simp only [List.length_cons, List.length_append, length_rowMajor]
  omega

theorem pre_allEdges (x : Bounded AllEdgesSource) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    fullAllEdgesTask.Pre (fullAllEdgesInst x) (memOf ((ofEnd AllEdgesSource).input x))
      (1 + 6 * (x.n * x.n)) := by
  have ht := (Light.Sec3.pre_exactTriangle (decisionBounded x) hn hU).mono
    (show 1 + 3 * (x.n * x.n) ≤ 1 + 6 * (x.n * x.n) by omega)
  refine { ht with belowOut := ?_, apartAB := ?_, apartBC := ?_, apartAC := ?_ }
  · simp only [fullAllEdgesInst, Light.Sec3.triangleInst, decisionBounded]
    omega
  all_goals exact Or.inl (by
    simp only [fullAllEdgesInst, Light.Sec3.triangleInst, decisionBounded]
    omega)

theorem entry_abZeroFlags {n : ℕ} (AB BC AC : Fin n → Fin n → ℤ) (a b : Fin n) :
    (abZeroFlags n (rowMajor AB) (rowMajor BC) (rowMajor AC)).getD (a.val * n + b.val) 0 =
      flag (∃ c : Fin n, AB a b + BC b c + AC a c = 0) := by
  rw [abZeroFlags, List.getD_map_range _ (Nat.mul_add_lt_mul a.isLt b.isLt),
    Nat.mul_add_div_of_lt b.isLt, Nat.mul_add_mod_of_lt b.isLt]
  apply flag_congr
  constructor
  · rintro ⟨c, hc, h⟩
    rw [getD_rowMajor BC b ⟨c, hc⟩, getD_rowMajor AC a ⟨c, hc⟩] at h
    exact ⟨⟨c, hc⟩, by simpa only [getD_rowMajor] using h⟩
  · rintro ⟨c, h⟩
    exact ⟨c.val, c.isLt, by simpa only [getD_rowMajor] using h⟩

theorem entry_bcZeroFlags {n : ℕ} (AB BC AC : Fin n → Fin n → ℤ) (b c : Fin n) :
    (bcZeroFlags n (rowMajor AB) (rowMajor BC) (rowMajor AC)).getD (b.val * n + c.val) 0 =
      flag (∃ a : Fin n, AB a b + BC b c + AC a c = 0) := by
  rw [bcZeroFlags, List.getD_map_range _ (Nat.mul_add_lt_mul b.isLt c.isLt),
    Nat.mul_add_div_of_lt c.isLt, Nat.mul_add_mod_of_lt c.isLt]
  apply flag_congr
  constructor
  · rintro ⟨a, ha, h⟩
    rw [getD_rowMajor AB ⟨a, ha⟩ b, getD_rowMajor AC ⟨a, ha⟩ c] at h
    exact ⟨⟨a, ha⟩, by simpa only [getD_rowMajor] using h⟩
  · rintro ⟨a, h⟩
    exact ⟨a.val, a.isLt, by simpa only [getD_rowMajor] using h⟩

theorem entry_acZeroFlags {n : ℕ} (AB BC AC : Fin n → Fin n → ℤ) (a c : Fin n) :
    (acZeroFlags n (rowMajor AB) (rowMajor BC) (rowMajor AC)).getD (a.val * n + c.val) 0 =
      flag (∃ b : Fin n, AB a b + BC b c + AC a c = 0) := by
  rw [acZeroFlags, List.getD_map_range _ (Nat.mul_add_lt_mul a.isLt c.isLt),
    Nat.mul_add_div_of_lt c.isLt, Nat.mul_add_mod_of_lt c.isLt]
  apply flag_congr
  constructor
  · rintro ⟨b, hb, h⟩
    rw [getD_rowMajor AB a ⟨b, hb⟩, getD_rowMajor BC ⟨b, hb⟩ c] at h
    exact ⟨⟨b, hb⟩, by simpa only [getD_rowMajor] using h⟩
  · rintro ⟨b, h⟩
    exact ⟨b.val, b.isLt, by simpa only [getD_rowMajor] using h⟩

theorem isFlag_flag (p : Prop) : APSPExponentImprovement.IsFlag (flag p) p := by
  by_cases h : p
  · exact Or.inl ⟨flag_of h, h⟩
  · exact Or.inr ⟨flag_of_not h, h⟩

theorem post_allEdges (x : Bounded AllEdgesSource) (r : ℤ) (μ' : ℕ → ℤ)
    (h : fullAllEdgesTask.Post (fullAllEdgesInst x)
      (memOf ((ofEnd AllEdgesSource).input x)) (1 + 6 * (x.n * x.n)) r μ') :
    (ofEnd AllEdgesSource).IsAnswer x (verdictOf false 1) fun i =>
      μ' (((ofEnd AllEdgesSource).input x).length + i) := by
  have hs := h.1
  change Seg μ' (1 + 3 * (x.n * x.n))
    (fullZeroFlags x.n (rowMajor x.x.1) (rowMajor x.x.2.1) (rowMajor x.x.2.2)) at hs
  rw [fullZeroFlags, seg_append, seg_append] at hs
  obtain ⟨⟨hAB, hBC⟩, hAC⟩ := hs
  simp only [abZeroFlags_length] at hBC
  simp only [List.length_append, abZeroFlags_length, bcZeroFlags_length] at hAC
  refine ⟨by simp [verdictOf, AllEdgesSource], ?_, ?_, ?_⟩
  · intro a b
    have he := hAB.getD (by simpa using Nat.mul_add_lt_mul a.isLt b.isLt) 0
    rw [entry_abZeroFlags] at he
    change APSPExponentImprovement.IsFlag (μ' (_ + (a.val * x.n + b.val))) _
    rw [input_allEdges_length, he]
    exact isFlag_flag _
  · intro b c
    have he := hBC.getD (by simpa using Nat.mul_add_lt_mul b.isLt c.isLt) 0
    rw [entry_bcZeroFlags] at he
    change APSPExponentImprovement.IsFlag (μ' (_ + (x.n * x.n + b.val * x.n + c.val))) _
    rw [input_allEdges_length]
    have addr : 1 + 3 * (x.n * x.n) + (x.n * x.n + b.val * x.n + c.val) =
        (1 + 3 * (x.n * x.n) + x.n * x.n) + (b.val * x.n + c.val) := by omega
    rw [addr, he]
    exact isFlag_flag _
  · intro a c
    have he := hAC.getD (by simpa using Nat.mul_add_lt_mul a.isLt c.isLt) 0
    rw [entry_acZeroFlags] at he
    change APSPExponentImprovement.IsFlag (μ' (_ + (2 * x.n * x.n + a.val * x.n + c.val))) _
    rw [input_allEdges_length]
    have addr : 1 + 3 * (x.n * x.n) + (2 * x.n * x.n + a.val * x.n + c.val) =
        (1 + 3 * (x.n * x.n) + (x.n * x.n + x.n * x.n)) +
          (a.val * x.n + c.val) := by ring
    rw [addr, he]
    exact isFlag_flag _

/-- The fixed public memory layout, including the free pointer after all
three output blocks, is implemented by the proved source top-level wrapper. -/
def wrapAllEdges : Wrap AllEdgesSource fullAllEdgesTask false where
  args := [v 1, v 2, k 1, ((Light.Expr.op Light.Op.add) (k 1) (v 3)), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 2) (v 3))),
    ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 3) (v 3))), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 6) (v 3)))]
  inst := fullAllEdgesInst
  fr x := 1 + 6 * (x.n * x.n)
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by omega
  vals x σ hn hU hnn := by
    simp [fullAllEdgesTask, fullAllEdgesInst, Light.Sec3.triangleInst, decisionBounded,
      hn, hU, hnn]
  safe x lim σ _ _ hnn hw := by
    have hn0 : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
    push_cast at hw hnn
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    simp only [Expr.Safe, Expr.val, Op.eval, hnn, true_and, Nat.cast_ofNat,
      Nat.cast_one, abs_le]
    omega
  zero x hn _ := by
    refine ⟨by simp [AllEdgesSource], ?_, ?_, ?_⟩
    all_goals intro i; exact False.elim (by have := i.isLt; omega)
  pre := pre_allEdges
  post x r μ' _ h := post_allEdges x r μ' h

/-- The full Light task has a compiled deterministic word-RAM realization,
with constant-factor time overhead and the exact public input/output layout. -/
theorem realized_allEdges (T : ℕ → ℝ → ℝ) (h : SolvedIn fullAllEdgesTask T) :
    Realized AllEdgesSource T := wrapAllEdges.realized h

/-- Changing from the source machine datatype to the mission's separately
declared machine preserves the exact bound and all three flag families. -/
theorem allEdges_sourceToMission {r : ℚ} (h : AllEdgesSource.SolvedInTime r) :
    APSPExponentImprovement.AllEdgesExactTriangle.SolvedInTime r :=
  APSPProofBridge.solvedInTime (fun x => x) (fun _ => rfl)
    (fun _ => Iff.rfl) (fun _ _ => Iff.rfl) h

/-- The final all-edges mission statement follows once the three-orientation
task has a composable source claim at the unrounded exponent. -/
theorem mission_allEdges_of_sourceClaim
    (h : Claim.SolvedAlongPow (SolvedIn fullAllEdgesTask) UpperPowPolylog 2.99825) :
    ∀ r : ℚ, 2.99825 < r →
      APSPExponentImprovement.AllEdgesExactTriangle.SolvedInTime r := by
  intro r hr
  have hr' : (2.99825 : ℝ) < (r : ℝ) := by
    have hc : ((2.99825 : ℚ) : ℝ) < (r : ℝ) := Rat.cast_lt.2 hr
    norm_num at hc ⊢
    exact hc
  have hr0 : 0 ≤ r := by linarith
  have ht := FromClaims.solvedInPolylogTime_of_claim realized_allEdges h
  exact allEdges_sourceToMission ((ht.solvedInTime hr').endStatement rfl hr0)

end APSPImprovement





end

section


/-!
# Orders of growth of counts

The time and the need of a program are natural numbers, given by explicit expressions in the
parameters of the input.  Only their order of growth is needed.  This file has one calculus
that reads the order of growth off such an expression, so that no constant is ever written out.

A *scale* (`Scale α ι`) fixes the parameters `x : α` for which bounds are claimed (`dom`) and some
quantities that are at least 1 there: the *bases* `base i`, whose powers are counted, and one more,
`hidden`, whose powers are not.  `s.SoftO t e` says that the count `t` is at most a constant times a
power of `hidden` times the monomial `∏ i, base i ^ e i`.  Three examples:

* bases `n`, `√D`, `κ log n` and `hidden = 1`: `s.SoftO t ![2, 1, 1]` is `t = O(n² √D κ log n)`;
* one base `√n` and `hidden = log n`: `s.SoftO t ![3]` is `t = Õ(n^{3/2})`;
* no base and `hidden = n U`: `s.SoftO t ![]` says that `t` is polynomially bounded.

So `SoftO` is `O` up to powers of `hidden`: it is `O` itself if `hidden = 1`, and `Õ` if `hidden` is
a logarithm.  The bounds hold on the whole domain and not only from some point on.

The exponents follow the expression.  A constant has the exponents 0 (`SoftO.const`), a sum the
larger ones (`SoftO.add`), a product their sum (`SoftO.mul`), a power their multiple (`SoftO.pow`).
Exponents may be raised (`SoftO.mono`), and the count may be replaced by a smaller one
(`SoftO.of_le`, `SoftO.of_forall_le`).  If every base is at most `2 ^ hidden`, the binary logarithm
of a bounded count has the exponents 0 (`SoftO.log2`).

The tactic `growth [h₁, h₂, …]` applies these rules from the outside to the inside of the
expression.  The facts `hᵢ` bound the quantities at which the rules stop: parameters, and functions
whose bound is a lemma of its own.  A function that is to be followed into its definition is
unfolded first.

A bound leaves the calculus by `SoftO.exists_le`, or as a `Dominated` statement by
`SoftO.dominated`.
-/

@[expose] public section

namespace ThreeSumApsp














namespace Scale










variable {α ι : Type*} [Fintype ι] (s : Scale α ι)









theorem mon_zero (x : α) : s.mon 0 x = 1 := by simp [mon]

theorem mon_add (e e' : ι → ℕ) (x : α) : s.mon (e + e') x = s.mon e x * s.mon e' x := by
  simp only [mon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem mon_smul (k : ℕ) (e : ι → ℕ) (x : α) : s.mon (k • e) x = s.mon e x ^ k := by
  simp only [mon, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm k]

theorem mon_single [DecidableEq ι] (i : ι) (x : α) : s.mon (Pi.single i 1) x = s.base i x := by
  simp [mon, Pi.single_apply, pow_ite]

variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}

/-- All bases are at least 1, so a monomial grows with its exponents. -/
theorem mon_le_mon (he : ∀ i, e i ≤ e' i) (hx : s.dom x) : s.mon e x ≤ s.mon e' x :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (s.one_le_base i x hx)) _)
    fun i _ => pow_le_pow_right₀ (s.one_le_base i x hx) (he i)

/-- A monomial is at least 1. -/
theorem one_le_mon (e : ι → ℕ) (hx : s.dom x) : 1 ≤ s.mon e x :=
  (s.mon_zero x).ge.trans (mon_le_mon (fun _ => Nat.zero_le _) hx)

/-- The bound grows with all exponents. -/
theorem pow_mul_mon_le (hc : c ≤ c') (he : ∀ i, e i ≤ e' i) (hx : s.dom x) :
    s.hidden x ^ c * s.mon e x ≤ s.hidden x ^ c' * s.mon e' x :=
  mul_le_mul (pow_le_pow_right₀ (s.one_le_hidden x hx) hc) (mon_le_mon he hx)
    (zero_le_one.trans (one_le_mon e hx)) (pow_nonneg (zero_le_one.trans (s.one_le_hidden x hx)) _)

namespace SoftO

variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}

/-! ### Entering and leaving -/

/-- A count that is at most `hidden`. -/
theorem of_le_hidden (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.hidden x) : s.SoftO t 0 :=
  ⟨1, .of_le fun x hx => by simpa only [pow_one, mon_zero, mul_one] using h x hx⟩

/-- A count that is at most a constant times a base. -/
theorem of_dominated_base [DecidableEq ι] (i : ι)
    (h : Dominated s.dom (fun x => (t x : ℝ)) (s.base i)) : s.SoftO t (Pi.single i 1) :=
  ⟨0, h.congr (fun _ _ => rfl) fun x _ => by rw [pow_zero, mon_single, one_mul]⟩

/-- A count that is at most a base. -/
theorem of_le_base [DecidableEq ι] (i : ι) (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.base i x) :
    s.SoftO t (Pi.single i 1) :=
  of_dominated_base i (.of_le h)

/-- A count that is at most a constant times a monomial. -/
theorem of_dominated (h : Dominated s.dom (fun x => (t x : ℝ)) (s.mon e)) : s.SoftO t e :=
  ⟨0, by simpa only [pow_zero, one_mul] using h⟩

/-- The bound, written out. -/
theorem exists_le (h : s.SoftO t e) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ x, s.dom x → (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) :=
  let ⟨c, C, hC, hle⟩ := h
  ⟨C, c, hC, hle⟩

/-- If `hidden = 1`, the bound is the monomial. -/
theorem dominated (h : s.SoftO t e) (hhidden : ∀ x, s.dom x → s.hidden x = 1) :
    Dominated s.dom (fun x => (t x : ℝ)) (s.mon e) :=
  let ⟨_, h⟩ := h
  h.congr (fun _ _ => rfl) fun x hx => by rw [hhidden x hx, one_pow, one_mul]

/-! ### The rules -/

/-- The exponents may be raised. -/
theorem mono (h : s.SoftO t e) (he : ∀ i, e i ≤ e' i) : s.SoftO t e' :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_right fun _ hx => pow_mul_mon_le le_rfl he hx⟩

/-- A smaller count has the same bound. -/
theorem of_le (h : s.SoftO t₂ e) (hle : ∀ x, s.dom x → t₁ x ≤ t₂ x) : s.SoftO t₁ e :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_left fun x hx => Nat.cast_le.2 (hle x hx)⟩

/-- A quantity `f` that is at most `g` everywhere has the bound of `g`, at any argument. -/
theorem of_forall_le {β : Type*} {f g : β → ℕ} (hle : ∀ y, f y ≤ g y) {u : α → β}
    (h : s.SoftO (fun x => g (u x)) e) : s.SoftO (fun x => f (u x)) e :=
  h.of_le fun _ _ => hle _

/-- A quantity `f` with two arguments that is at most `g` everywhere has the bound of `g`. -/
theorem of_forall_le₂ {β γ : Type*} {f g : β → γ → ℕ} (hle : ∀ y z, f y z ≤ g y z) {u : α → β}
    {v : α → γ} (h : s.SoftO (fun x => g (u x) (v x)) e) : s.SoftO (fun x => f (u x) (v x)) e :=
  h.of_le fun _ _ => hle _ _

/-- A constant has the exponents 0. -/
protected theorem const (k : ℕ) : s.SoftO (fun _ => k) 0 :=
  ⟨0, .const _ fun x _ => by rw [pow_zero, mon_zero, mul_one]⟩

/-- A sum has the larger exponents. -/
protected theorem add (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x + t₂ x) (e₁ ⊔ e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨max c₁ c₂, ?_⟩
  simpa only [Nat.cast_add] using
    (h₁.mono_right fun _ hx =>
      pow_mul_mon_le (e' := e₁ ⊔ e₂) (le_max_left _ _) (fun _ => le_sup_left) hx).add
      (h₂.mono_right fun _ hx => pow_mul_mon_le (le_max_right _ _) (fun _ => le_sup_right) hx)

/-- A sum of two counts with the same bound. -/
theorem add_le (h₁ : s.SoftO t₁ e) (h₂ : s.SoftO t₂ e) : s.SoftO (fun x => t₁ x + t₂ x) e :=
  (h₁.add h₂).mono fun _ => (sup_idem _).le

/-- In a product the exponents add up. -/
protected theorem mul (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x * t₂ x) (e₁ + e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, ?_⟩
  simpa only [Nat.cast_mul] using
    (h₁.mul h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_add, pow_add, mul_mul_mul_comm]

/-- The `k`-th power multiplies the exponents by `k`. -/
protected theorem pow (h : s.SoftO t e) (k : ℕ) : s.SoftO (fun x => t x ^ k) (k • e) := by
  obtain ⟨c, h⟩ := h
  refine ⟨c * k, ?_⟩
  simpa only [Nat.cast_pow] using
    (h.pow (fun _ _ => Nat.cast_nonneg _) k).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_smul, mul_pow, pow_mul]

/-- A maximum has the larger exponents. -/
protected theorem max (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => max (t₁ x) (t₂ x)) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- A difference has the exponents of its first term. -/
protected theorem sub (h : s.SoftO t₁ e) (t₂ : α → ℕ) : s.SoftO (fun x => t₁ x - t₂ x) e :=
  h.of_le fun _ _ => Nat.sub_le _ _

/-- A quotient has the exponents of its numerator. -/
protected theorem div (h : s.SoftO t₁ e) (t₂ : α → ℕ) : s.SoftO (fun x => t₁ x / t₂ x) e :=
  h.of_le fun _ _ => Nat.div_le_self _ _

/-- A quotient that is rounded up has the larger exponents of numerator and denominator. -/
protected theorem ceilDiv (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x ⌈/⌉ t₂ x) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ =>
    (Nat.ceilDiv_eq_add_pred_div _ _).trans_le ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))

/-- A logarithm is at most the number. -/
protected theorem log (h : s.SoftO t e) (b : ℕ) : s.SoftO (fun x => Nat.log b (t x)) e :=
  h.of_le fun _ _ => Nat.log_le_self _ _

/-- A square root is at most the number. -/
protected theorem sqrt (h : s.SoftO t e) : s.SoftO (fun x => Nat.sqrt (t x)) e :=
  h.of_le fun _ _ => Nat.sqrt_le_self _




































end SoftO

end Scale








































end ThreeSumApsp

end
end

section


/-!
# Polynomially bounded needs

The need of a program is given by explicit expressions in the size n of the input and the bound U on
its numbers.  `PolyBounded F` says that F(n, U) is at most a polynomial in (n + 1)(U + 1).  It is
the calculus `ThreeSumApsp.Scale.SoftO` on the scale `polyScale`, and the tactic `growth_poly`
proves it by following the expression.

Three such functions make a polynomially bounded need (`PolyBounded.polyNeed`), and the need of a
solver that a host calls has three such parts (`PolyNeed.word`, `PolyNeed.cells`, `PolyNeed.depth`).
So the need of a host is polynomially bounded if the need of its solver is; the tactic `poly_need`
proves this from the definition of the need of the host.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Upper bounds that are polynomial in (n + 1)(U + 1) -/













namespace PolyBounded

variable {F : ℕ → ℕ → ℕ}

/-- The size `n` is polynomially bounded. -/
theorem fst : PolyBounded (fun n _ => n) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ p.2.succ_pos)).mono (by decide)

/-- The bound `U` is polynomially bounded. -/
theorem snd : PolyBounded (fun _ U => U) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ p.1.succ_pos)).mono (by decide)

/-- A smaller function has the same bound. -/
theorem of_le {G : ℕ → ℕ → ℕ} (h : PolyBounded G) (hle : ∀ n U, F n U ≤ G n U) : PolyBounded F :=
  Scale.SoftO.of_le h fun _ _ => hle _ _

/-- The bound with natural numbers. -/
theorem exists_nat_le (h : PolyBounded F) :
    ∃ K e : ℕ, ∀ n U, F n U ≤ K * ((n + 1) * (U + 1)) ^ e := by
  obtain ⟨C, e, hC, hle⟩ := h.exists_le
  refine ⟨⌈C⌉₊, e, fun n U => ?_⟩
  have hceil : (F n U : ℝ) ≤ ⌈C⌉₊ * (((n + 1) * (U + 1) : ℕ) : ℝ) ^ e := by
    simpa [polyScale, Scale.mon] using (hle (n, U) trivial).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by simp [polyScale, Scale.mon]; positivity))
  exact_mod_cast hceil

end PolyBounded






namespace PolyBounded

/-- A polynomial bound at polynomially bounded parameters. -/
theorem polyBound {A B : ℕ → ℕ → ℕ} (hA : PolyBounded A) (hB : PolyBounded B) (s k : ℕ) :
    PolyBounded (fun n U => polyBound s k [A n U, B n U]) :=
  of_le (G := fun n U => 2 ^ s * ((A n U + 1) * (B n U + 1)) ^ k) (by first
                                                                      |
                                                                        ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                          (·
                                                                              repeat'
                                                                                with_reducible
                                                                                  first
                                                                                  | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                  | apply Light.PolyBounded.fst
                                                                                  | apply Light.PolyBounded.snd
                                                                                  | apply ThreeSumApsp.Scale.SoftO.log
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                  | apply hA
                                                                                  | apply hB
                                                                                  | apply ThreeSumApsp.Scale.SoftO.add
                                                                                  | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                  | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                  | apply ThreeSumApsp.Scale.SoftO.max
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                  | apply ThreeSumApsp.Scale.SoftO.div);
                                                                          (·
                                                                              first
                                                                              | decide
                                                                              | exact isEmptyElim))
                                                                      |
                                                                        ((fail_if_success
                                                                              (fail_if_success
                                                                                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                                    (on_goal 1 =>
                                                                                        ((repeat'
                                                                                              with_reducible
                                                                                                first
                                                                                                | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                                | apply Light.PolyBounded.fst
                                                                                                | apply Light.PolyBounded.snd
                                                                                                | apply ThreeSumApsp.Scale.SoftO.log
                                                                                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                                | apply hA
                                                                                                | apply hB
                                                                                                | apply ThreeSumApsp.Scale.SoftO.add
                                                                                                | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                                | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                                | apply ThreeSumApsp.Scale.SoftO.max
                                                                                                | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                                | apply ThreeSumApsp.Scale.SoftO.div);
                                                                                          (done))))));
                                                                          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                                                                          (all_goals
                                                                              try
                                                                                ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                                  (·
                                                                                      repeat'
                                                                                        with_reducible
                                                                                          first
                                                                                          | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                          | apply Light.PolyBounded.fst
                                                                                          | apply Light.PolyBounded.snd
                                                                                          | apply ThreeSumApsp.Scale.SoftO.log
                                                                                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                          | apply hA
                                                                                          | apply hB
                                                                                          | apply ThreeSumApsp.Scale.SoftO.add
                                                                                          | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                          | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                          | apply ThreeSumApsp.Scale.SoftO.max
                                                                                          | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                          | apply ThreeSumApsp.Scale.SoftO.div);
                                                                                  (· decide))))
                                                                      |
                                                                        ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                          (·
                                                                              repeat'
                                                                                with_reducible
                                                                                  first
                                                                                  | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                  | apply Light.PolyBounded.fst
                                                                                  | apply Light.PolyBounded.snd
                                                                                  | apply ThreeSumApsp.Scale.SoftO.log
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                  | apply hA
                                                                                  | apply hB
                                                                                  | apply ThreeSumApsp.Scale.SoftO.add
                                                                                  | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                  | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                  | apply ThreeSumApsp.Scale.SoftO.max
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                  | apply ThreeSumApsp.Scale.SoftO.div)))
    fun n U => by simp [Light.polyBound]

/-- Three polynomially bounded functions make a polynomially bounded need. -/
theorem polyNeed {need : ℕ → ℕ → Need} (hw : PolyBounded fun n U => (need n U).word)
    (hc : PolyBounded fun n U => (need n U).cells) (hd : PolyBounded fun n U => (need n U).depth) :
    PolyNeed need := by
  obtain ⟨K, e, hK⟩ := exists_nat_le (F := fun n U => (need n U).word + (need n U).cells +
    (need n U).depth) (by first
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div);
                              (·
                                  first
                                  | decide
                                  | exact isEmptyElim))
                          |
                            ((fail_if_success
                                  (fail_if_success
                                      ((apply ThreeSumApsp.Scale.SoftO.mono);
                                        (on_goal 1 =>
                                            ((repeat'
                                                  with_reducible
                                                    first
                                                    | exact ThreeSumApsp.Scale.SoftO.const _
                                                    | apply Light.PolyBounded.fst
                                                    | apply Light.PolyBounded.snd
                                                    | apply ThreeSumApsp.Scale.SoftO.log
                                                    | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                    | apply hw
                                                    | apply hc
                                                    | apply hd
                                                    | apply ThreeSumApsp.Scale.SoftO.add
                                                    | apply ThreeSumApsp.Scale.SoftO.mul
                                                    | apply ThreeSumApsp.Scale.SoftO.pow
                                                    | apply ThreeSumApsp.Scale.SoftO.max
                                                    | apply ThreeSumApsp.Scale.SoftO.sub
                                                    | apply ThreeSumApsp.Scale.SoftO.div);
                                              (done))))));
                              (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                              (all_goals
                                  try
                                    ((apply ThreeSumApsp.Scale.SoftO.mono);
                                      (·
                                          repeat'
                                            with_reducible
                                              first
                                              | exact ThreeSumApsp.Scale.SoftO.const _
                                              | apply Light.PolyBounded.fst
                                              | apply Light.PolyBounded.snd
                                              | apply ThreeSumApsp.Scale.SoftO.log
                                              | apply ThreeSumApsp.Scale.SoftO.sqrt
                                              | apply hw
                                              | apply hc
                                              | apply hd
                                              | apply ThreeSumApsp.Scale.SoftO.add
                                              | apply ThreeSumApsp.Scale.SoftO.mul
                                              | apply ThreeSumApsp.Scale.SoftO.pow
                                              | apply ThreeSumApsp.Scale.SoftO.max
                                              | apply ThreeSumApsp.Scale.SoftO.sub
                                              | apply ThreeSumApsp.Scale.SoftO.div);
                                      (· decide))))
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div)))
  refine ⟨Nat.size K, e, fun n U => ?_⟩
  have hsum := hK n U
  have hpoly : K * ((n + 1) * (U + 1)) ^ e ≤ Light.polyBound (Nat.size K) e [n, U] := by
    simp only [Light.polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.lt_size_self K).le
  exact ⟨by omega, by omega, by omega⟩

end PolyBounded

/-! ## The need of a solver that a host calls

A polynomially bounded need, at a size `A(n, U)` and a bound `B(n, U)` that are polynomially
bounded, has polynomially bounded parts. -/

namespace PolyNeed

variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}

private theorem part (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    ∃ R : ℕ → ℕ → ℕ, PolyBounded R ∧ ∀ n U, (need (A (n, U)) (B (n, U))).word ≤ R n U ∧
      (need (A (n, U)) (B (n, U))).cells ≤ R n U ∧ (need (A (n, U)) (B (n, U))).depth ≤ R n U :=
  let ⟨s, k, hle⟩ := h
  ⟨_, PolyBounded.polyBound (A := fun n U => A (n, U)) (B := fun n U => B (n, U))
    (hA.mono isEmptyElim) (hB.mono isEmptyElim) s k, fun _ _ => hle _ _⟩

/-- The numbers of the solver. -/
theorem word (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).word) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).1

/-- The cells of the solver. -/
theorem cells (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).cells) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.1

/-- The depth of the calls of the solver. -/
theorem depth (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).depth) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.2

end PolyNeed








end Light

end
end

section


/-!
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

/-- After the pass the n cells hold the list of the values f 0, …, f (n - 1). -/
theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : Seg (wrote μ dst f n) dst l := fun i hi => by
  rw [wrote_done (hl ▸ hi), h i hi]







/-- **The rule for a pass.**  The locals x and y hold the length n and the address dst.  In round j
the locals are the given ones with j in the counter, and the memory is `wrote μ dst f j`; there the
expression e has to be safe and have the value f j. -/
theorem Ends.pass {c x y n T : ℕ} {e : Expr} {loc : ℕ → ℤ} {Q : State → Prop} (f : ℕ → ℤ)
    (round : ∀ j < n, e.Safe lim ⟨Function.update loc c j, wrote μ dst f j⟩ ∧
      e.val ⟨Function.update loc c j, wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, wrote μ dst f n⟩)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) (hlen : loc x = n)
    (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by first
                                            |
                                              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                (first
                                                  | omega
                                                  | ((ring_nf); (omega))))
                                            | omega
                                            |
                                              (simp [] <;>
                                                  first
                                                  | omega
                                                  | ((ring_nf); (omega)))) :
    Ends lim P d (pass c (v x) (v y) e) ⟨loc, μ⟩ T Q := by
  refine Ends.forMem (fun j μ' => μ' = wrote μ dst f j) n _ wrote_zero.symm
    (fun j μ' hj hμ' => Ends.block ?round le_rfl)
    (fun μ' h => by rw [h]; exact done)
    (fun j μ' _ _ => ⟨trivial, (Function.update_of_ne hx _ _).trans hlen⟩) (by omega)
    (le_trans (le_of_eq (by simp only [Stmt.blockCost, Expr.cost]; ring)) hT)
  -- Round j: dst[j] := e.
  subst hμ'
  obtain ⟨hs, hv⟩ := round j hj
  have qc : Function.update loc c (j : ℤ) c = j := Function.update_self ..
  have qy : Function.update loc c (j : ℤ) y = dst := by rw [Function.update_of_ne hy, haddr]
  refine ⟨⟨?_, hs, ?_⟩, rfl, ?_⟩
  · simp only [Expr.Safe, Expr.val, Op.eval, qc, qy, true_and, abs_le]
    omega
  · simp only [Expr.val, Op.eval, qc, qy, Limits.Addr]
    omega
  · simp only [Stmt.after, Expr.val, Op.eval, qc, qy, hv, toNat_natCast_add_natCast, wrote_succ]

end Light

end
end

section


/-!
# `logU`, the paper's `log U`

`logU u` is `log u`, read as `log 2` for `u < 2`.

* It is positive and nondecreasing, and `log (cu) ≤ log c + log u` for `c ≥ 1`.
* `log (cU) = O(log U)` (`dominated_logU_mul`) and `log (c n^κ) = O(log n)`
  (`dominated_logU_mul_rpow`).
* Along bounds `u(n) ≤ c n^κ` it is `Õ(1)` (`isPowPolylog_logU_of_le`).
-/

public section

namespace ThreeSumApsp

/-- `logU u ≥ log 2`. -/
theorem log_two_le_logU (u : ℝ) : Real.log 2 ≤ logU u :=
  Real.log_le_log two_pos (le_max_right _ _)

/-- `logU u > 0`. -/
theorem logU_pos (u : ℝ) : 0 < logU u :=
  (Real.log_pos one_lt_two).trans_le (log_two_le_logU u)

/-- `1 + logU u ≥ 1`. -/
theorem one_le_one_add_logU (u : ℝ) : 1 ≤ 1 + logU u :=
  le_add_of_nonneg_right (logU_pos u).le

/-- `log u ≤ logU u` for `u > 0`. -/
theorem log_le_logU {u : ℝ} (hu : 0 < u) : Real.log u ≤ logU u :=
  Real.log_le_log hu (le_max_left _ _)




























/-! ## `logU` of a multiple -/
























/-! ## `logU` along bounds that are polynomial in `n` -/

/-- `log u(n) = Õ(1)` for bounds `1 ≤ u(n) ≤ c n^κ` on the numbers. -/
theorem isPowPolylog_logU_of_le {mag : ℕ → ℝ} {c κ : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → 1 ≤ mag n ∧ mag n ≤ c * (n : ℝ) ^ κ) :
    IsPowPolylog (fun n => logU (mag n)) 0 := by
  refine (isPowPolylog_log_mul_rpow (2 * c) κ).mono_left_of_nonneg
    (.of_forall fun n => (logU_pos _).le) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨hone, hle⟩ := h n hn
  refine Real.log_le_log (lt_max_of_lt_right two_pos) (max_le ?_ ?_) <;> rw [mul_assoc] <;> linarith

/-- `log (c n^κ) = Õ(1)`. -/
theorem isPowPolylog_logU_mul_rpow {c κ : ℝ} (hc : 1 ≤ c) (hκ : 0 ≤ κ) :
    IsPowPolylog (fun n : ℕ => logU (c * (n : ℝ) ^ κ)) 0 :=
  isPowPolylog_logU_of_le fun _ hn =>
    ⟨one_le_mul_of_one_le_of_one_le hc (Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ), le_rfl⟩

end ThreeSumApsp

end
end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Improvement.APSP

open ThreeSumApsp

/-- A Light solver can be bounded using any larger magnitude argument. This
changes its time bound, not its program or its resource requirements. -/
theorem solvedIn_raiseMagnitude {task : Light.Task} {T : ℕ → ℝ → ℝ}
    (h : Light.SolvedIn task T) (v : ℕ → ℝ) :
    Light.SolvedIn task (fun n u => T n (max u (v n))) := by
  obtain ⟨P, p, Tn, need, hn, hs, ht⟩ := h
  exact ⟨P, p, Tn, need, hn, hs, fun n U u hn hU hu =>
    ht n U _ hn hU (hu.trans (le_max_left _ _))⟩














































































end Improvement.APSP






end

section


@[expose] public section

namespace APSPImprovement.AllEdges

open Light ThreeSumApsp

/-- Reuse the source's algorithm-independent exponent analysis for the all-edges task.
Only the exact-triangle field changes; the sparse solver and all machine semantics
remain those of the original proved light-language model. -/
noncomputable def allEdgesModel : DetTimeModel :=
  { lightModel with exactTriangle := SolvedIn allEdgesTask }

theorem mono_allEdges : Closure.MonoExactTriangle allEdgesModel :=
  fun _ _ hle hT => SolvedIn.mono hT hle

end APSPImprovement.AllEdges

end
end

section


/-!
# Scanning a piece (the proof of Theorem 17)

"For every query pair that the oracle accepts, scan the piece C_k of its instance for a c with
S(a,b,c) = 0".  The procedure scan (`scanBody`) goes through an interval of vertices `c` for a fixed
pair `(a, b)` (`scan_spec`, `scan_meets`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}




theorem flag_eq_bit (b : Bool) : flag (b = true) = bit b := by
  cases b
  · simp [bit, flag_of_not]
  · simp [bit, flag_of]

/-! ## The three arrays of weights -/










/-! ## Scanning an interval of vertices -/

namespace Scan


















end Scan





















/-- One more vertex in a scan. -/
theorem scanHit_succ (n : ℕ) (AB BC AC : List ℤ) (a b c0 c : ℕ) :
    scanHit n AB BC AC a b c0 (c + 1) = (scanHit n AB BC AC a b c0 c || decide
      (AB.getD (a * n + b) 0 + BC.getD (b * n + c0 + c) 0 + AC.getD (a * n + c0 + c) 0 = 0)) := by
  simp [scanHit, List.range_succ, List.any_append]

/-- One round of `scan`, for the weights `wbc` and `wac` that it reads. -/
theorem scanRound_runs {μ : ℕ → ℤ} {ab bc ac n a b c0 len c rowB rowA U : ℕ} {wab wbc wac : ℤ}
    {hit : Bool} (hw : (lim.space : ℤ) ≤ lim.word) (hU : 3 * (U : ℤ) + 1 ≤ lim.word)
    (hreadB : μ (rowB + c) = wbc) (hreadA : μ (rowA + c) = wac) (hB : rowB + c < lim.space)
    (hA : rowA + c < lim.space) (leAB : |wab| ≤ U) (leBC : |wbc| ≤ U) (leAC : |wac| ≤ U) :
    scanRound.Runs lim ⟨frame [ab, bc, ac, n, a, b, c0, len, c, bit hit, wab, rowB, rowA], μ⟩
      (· = ⟨frame [ab, bc, ac, n, a, b, c0, len, (c + 1 : ℕ),
        bit (hit || decide (wab + wbc + wac = 0)), wab, rowB, rowA], μ⟩) := by
  rw [abs_le] at leAB leBC leAC
  by_cases hz : wab + wbc + wac = 0 <;>
    exact ⟨by
      simp [scanRound, Limits.Addr, abs_le, update_frame_setLocal, hreadB, hreadA, hz]; omega,
      by simp [scanRound, update_frame_setLocal, hreadB, hreadA, hz, bit]⟩

/-- **scan** returns 1 if some `c` in the interval has `S(a,b,c) = 0`, and 0 if not; it changes no
cell. -/
theorem scan_spec {μ : ℕ → ℤ} {ab bc ac n a b c0 len U : ℕ} {AB BC AC : List ℤ}
    (C : Weights lim μ ab bc ac n U AB BC AC) (ha : a < n) (hb : b < n) (hc : c0 + len ≤ n) :
    Ends lim P d scanBody ⟨frame [ab, bc, ac, n, a, b, c0, len], μ⟩ (tScan len) fun σ' =>
      σ'.loc 0 = flag (scanHit n AB BC AC a b c0 len = true) ∧ σ'.mem = μ := by
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.arrAB); (obtain ⟨⟩ := id C.arrBC);
    (obtain ⟨⟩ := id C.arrAC))
  have iab : a * n + b < n * n := Nat.mul_add_lt_mul ha hb
  have ibc : b * n + (c0 + len) ≤ n * n := Nat.mul_add_le_mul hb hc
  have iac : a * n + (c0 + len) ≤ n * n := Nat.mul_add_le_mul ha hc
  -- The weight `w(a,b)` and the addresses of `w(b,c0)` and `w(a,c0)`.
  obtain ⟨wab, hwab⟩ : ∃ z, z = AB.getD (a * n + b) 0 := ⟨_, rfl⟩
  obtain ⟨rowB, hrowB⟩ : ∃ r, r = bc + b * n + c0 := ⟨_, rfl⟩
  obtain ⟨rowA, hrowA⟩ : ∃ r, r = ac + a * n + c0 := ⟨_, rfl⟩
  have hreadAB : μ (ab + (a * n + b)) = wab := (C.arrAB.read iab).trans hwab.symm
  have haddrAB : ((ab : ℤ) + (a : ℤ) * (n : ℤ) + (b : ℤ)).toNat = ab + (a * n + b) := by
    rw [show (ab : ℤ) + (a : ℤ) * (n : ℤ) + (b : ℤ) = ((ab + (a * n + b) : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
  have leAB : |wab| ≤ U := hwab ▸ AbsLe.abs_getD_le (Int.natCast_nonneg U) C.arrAB.bound _
  unfold scanBody tScan
  -- hit := 0; wab := ab[a n + b]; rowB := bc + b n + c0; rowA := ac + a n + c0; c := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen wab ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddrAB,
                hreadAB]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddrAB, hreadAB] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddrAB, hreadAB] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen rowB ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen rowA ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (0 : ℕ)
            -- while c < len
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while c < len
  refine Ends.next _ (Ends.whileBlock (fun c σ => σ = ⟨frame [ab, bc, ac, n, a, b, c0, len, c,
    bit (scanHit n AB BC AC a b c0 c), wab, rowB, rowA], μ⟩) len ?start ?round ?done le_rfl)
    (by simp [scanRound]; omega)
  case start => simp [scanHit, bit]
  case round =>
    rintro c _ hcl rfl
    have hreadBC : μ (rowB + c) = BC.getD (b * n + c0 + c) 0 := by
      rw [← C.arrBC.read (by omega), hrowB, Nat.add_assoc bc, Nat.add_assoc bc]
    have hreadAC : μ (rowA + c) = AC.getD (a * n + c0 + c) 0 := by
      rw [← C.arrAC.read (by omega), hrowA, Nat.add_assoc ac, Nat.add_assoc ac]
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    rw [scanHit_succ, ← hwab]
    exact scanRound_runs C.hw C.hU hreadBC hreadAC (by omega) (by omega) leAB
      (AbsLe.abs_getD_le (Int.natCast_nonneg U) C.arrBC.bound _)
      (AbsLe.abs_getD_le (Int.natCast_nonneg U) C.arrAC.bound _)
  case done =>
    rintro _ rfl
    -- return hit
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), Ends.setTo (bit (scanHit n AB BC AC a b c0 len))
      ⟨(flag_eq_bit _).symm, rfl⟩ (hT := by simp [scanRound]; omega)⟩

/-- The specification of `scan`, for its callers. -/
theorem scan_meets {p : ℕ} {μ : ℕ → ℤ} {ab bc ac n a b c0 len U : ℕ} {AB BC AC : List ℤ}
    (hP : P[p]? = some scanBody) (C : Weights lim μ ab bc ac n U AB BC AC) (ha : a < n) (hb : b < n)
    (hc : c0 + len ≤ n) :
    Meets lim P p d [ab, bc, ac, n, a, b, c0, len] μ (tScan len) fun r μ' =>
      r = flag (scanHit n AB BC AC a b c0 len = true) ∧ μ' = μ :=
  Meets.of_body hP (scan_spec C ha hb hc)

end Light.Sec3

end
end

section


/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}




























namespace Brute














end Brute






















/-- An instance of Exact Triangle gives `scan` what it assumes. -/
theorem _root_.Light.TriInst.Pre.weights {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Weights lim μ x.ab x.bc x.ac x.n x.U x.AB x.BC x.AC where
  hw := hok.space
  hU := by exact_mod_cast hok.word
  arrAB := ⟨hpre.lenAB, hpre.segAB, hpre.leAB, hpre.belowAB.trans hok.cells⟩
  arrBC := ⟨hpre.lenBC, hpre.segBC, hpre.leBC, hpre.belowBC.trans hok.cells⟩
  arrAC := ⟨hpre.lenAC, hpre.segAC, hpre.leAC, hpre.belowAC.trans hok.cells⟩

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}











































end





























































end Light.Sec3

end
end

section


/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}














/-- Procedure p of P is procedure `p + Q.length` of P placed behind Q, with its calls
shifted. -/
theorem Program.getElem?_behind_right (Q : Program) {p : ℕ} {body : Stmt} (h : P[p]? = some body) :
    (Program.behind Q P)[p + Q.length]? = some (body.shift Q.length) := by
  rw [Program.behind, List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
    List.getElem?_map, h]
  rfl

/-- **Relocation.**  A run in P is a run, with the same states and the same number of steps, of
the shifted statement in P placed behind Q. -/
theorem Exec.shift {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (Q : Program) :
    Exec lim (Program.behind Q P) d (s.shift Q.length) σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (Program.getElem?_behind_right Q h₂) h₃ ih

/-- What is proved about a statement in P holds for the shifted statement in P placed behind
Q. -/
theorem Ends.shift {s σ T post} (h : Ends lim P d s σ T post) (Q : Program) :
    Ends lim (Program.behind Q P) d (s.shift Q.length) σ T post := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.shift Q, hc, hq⟩

/-- The same with more procedures appended behind. -/
theorem Ends.shift_append {s σ T post} (h : Ends lim P d s σ T post) (Q R : Program) :
    Ends lim (Program.behind Q P ++ R) d (s.shift Q.length) σ T post :=
  (h.shift Q).append R

end Light

end
end

section


/-!
# Two algorithms for Exact Triangle and a threshold on the number of vertices

For every threshold n₀ there is a constant C₀ such that, if Exact Triangle is solved in time T₁ and
in time T₂, then it is solved in time T₁ + C₀ for n < n₀ and T₂ + C₀ for n ≥ n₀.  This is
`Closure.ChooseBySize`, with "Exact Triangle is solved in time T" read as `SolvedIn etTask T`
(`closure_chooseBySize`).  It is used in the proof of Theorem 19, where the bounds hold
for large n only.

Two solvers are put into one program, the second behind the first (`solves_behind`), and one more
procedure looks at the number of vertices and calls the first solver below a fixed threshold n₀ and
the second one from the threshold on (`bySize_spec`).  The need stays polynomial
(`polyNeed_bySize`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}


















namespace ChooseHost

/-- A solver stays a solver, with its number shifted, when its program is placed behind another
program. -/
theorem solves_behind {task : Task} {P : Program} {p : ℕ} {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : Solves task P p T need)
    (Q : Program) : Solves task (Program.behind Q P) (p + Q.length) T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body.shift Q.length, Program.getElem?_behind_right Q hp, fun R lim d x μ fr hpre hok =>
    ?_⟩
  have := hb [] lim d x μ fr hpre hok
  rw [List.append_nil] at this
  exact this.shift_append Q R


























/-- The need of choose is polynomially bounded if the needs of the two solvers are. -/
theorem polyNeed_bySize (n₀ : ℕ) {r₁ r₂ : ℕ → ℕ → Need} (h₁ : PolyNeed r₁) (h₂ : PolyNeed r₂) :
    PolyNeed (bySizeNeed n₀ r₁ r₂) := by
  unfold bySizeNeed
  (refine Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
      first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply h₁.word
                  | apply h₁.cells
                  | apply h₁.depth
                  | apply h₂.word
                  | apply h₂.cells
                  | apply h₂.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply h₁.word
                                | apply h₁.cells
                                | apply h₁.depth
                                | apply h₂.word
                                | apply h₂.cells
                                | apply h₂.depth
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply h₁.word
                          | apply h₁.cells
                          | apply h₁.depth
                          | apply h₂.word
                          | apply h₂.cells
                          | apply h₂.depth
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply h₁.word
                  | apply h₁.cells
                  | apply h₁.depth
                  | apply h₂.word
                  | apply h₂.cells
                  | apply h₂.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)))

end ChooseHost

open ChooseHost




















end Light.Sec3

end
end

section


@[expose] public section

namespace APSPImprovement

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

theorem scan_flag_eq {n a b : ℕ} (AB BC AC : List ℤ) (ha : a < n) (hb : b < n) :
    flag (scanHit n AB BC AC a b 0 n = true) =
      (abZeroFlags n AB BC AC).getD (a * n + b) 0 := by
  rw [abZeroFlags, List.getD_map_range _ (Nat.mul_add_lt_mul ha hb),
    Nat.mul_add_div_of_lt hb, Nat.mul_add_mod_of_lt hb]
  apply flag_congr
  simp [scanHit]

namespace AllEdgesBrute

abbrev Verts : ℕ := 0

abbrev MatAB : ℕ := 2
abbrev MatBC : ℕ := 3
abbrev MatAC : ℕ := 4
abbrev Out : ℕ := 5

abbrev Row : ℕ := 7
abbrev Col : ℕ := 8
abbrev Res : ℕ := 9

def inner (pScan : ℕ) : Stmt :=
  .for Col (v Verts) (
    (Light.Stmt.seq
      (.call pScan [v MatAB, v MatBC, v MatAC, v Verts, v Row, v Col, k 0, v Verts]
        Res)
      (.store
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) (v Out)
            ((Light.Expr.op Light.Op.mul) (v Row) (v Verts)))
          (v Col))
        (v Res))))

def body (pScan : ℕ) : Stmt := .for Row (v Verts) (inner pScan)

def time (n : ℕ) : ℕ := 100 * n ^ 3 + 100

abbrev locals (x : AllEdgesInst) (fr : ℕ) (a b r : ℤ) : List ℤ :=
  [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr, a, b, r]

def Mem (x : AllEdgesInst) (μ : ℕ → ℤ) (a b : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ q < a * x.n + b, μ' (x.out + q) = (abZeroFlags x.n x.AB x.BC x.AC).getD q 0) ∧
    SameOutside μ μ' x.out (x.n * x.n)

theorem inner_spec {lim : Limits} {P : Program} {d pScan : ℕ}
    (hP : P[pScan]? = some scanBody) {x : AllEdgesInst} {μ μ' : ℕ → ℤ}
    {fr a : ℕ} {b₀ r₀ : ℤ} (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) (ha : a < x.n)
    (hm : Mem x μ a 0 μ') :
    Ends lim P d (inner pScan) ⟨frame (locals x fr a b₀ r₀), μ'⟩
      (x.n * (24 * x.n + 70) + 6) fun σ' =>
      ∃ r μ'', σ' = ⟨frame (locals x fr a x.n r), μ''⟩ ∧ Mem x μ (a + 1) 0 μ'' := by
  (obtain ⟨⟩ := id hpre.toPre)
  (obtain ⟨⟩ := id hpre)
  have hw := hok.space
  have hs := hok.cells
  have hd : d < lim.depth := hok.depth
  have hn2 : x.n ≤ x.n * x.n := Nat.le_mul_self _
  refine Ends.for (fun b σ => ∃ r μ'', σ = ⟨frame (locals x fr a b r), μ''⟩ ∧
    Mem x μ a b μ'') x.n (tScan x.n + 27) ?start ?round ?done ?bound
    (hT := by simp [tScan]; ring_nf; omega)
  case start => exact ⟨r₀, μ', by rw [update_frame_setLocal]; rfl, hm⟩
  case bound => rintro b _ - - ⟨r, μ'', rfl, -⟩; simp
  case done =>
    rintro _ - ⟨r, μ'', rfl, hm'⟩
    exact ⟨r, μ'', rfl, by simpa [Mem, Nat.add_mul] using hm'⟩
  case round =>
    rintro b _ hb - ⟨r, μ'', rfl, hdone, hrest⟩
    have hp' : x.Pre μ'' fr := hpre.keep
    have C := hp'.toPre.weights hok
    have hab : a * x.n + b < x.n * x.n := Nat.mul_add_lt_mul ha hb
    have habZ : 0 ≤ (a : ℤ) * x.n ∧ (a : ℤ) * x.n + b < x.n * x.n := by
      exact_mod_cast And.intro (Nat.zero_le _) hab
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (first
        |
          refine
            Light.Ends.callToThen
              ((scan_meets hP C ha hb (c0 := 0) (len := x.n) (by omega)) _
                (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            Light.Ends.callToThen
              (scan_meets hP C ha hb (c0 := 0) (len := x.n) (by omega)) ?_ ?_ ?_
              ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (on_goal -1 =>
          ((rintro _ _ ⟨rfl, rfl⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine
          Light.Ends.storeToThen (x.out + (a * x.n + b))
            (flag (scanHit x.n x.AB x.BC x.AC a b 0 x.n = true)) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp, flag (scanHit x.n x.AB x.BC x.AC a b 0 x.n = true),
      Function.update _ (x.out + (a * x.n + b)) (flag (scanHit x.n x.AB x.BC x.AC a b 0 x.n = true)),
      by simp [update_frame_setLocal],
      fun q hq => ?_, hrest.update ⟨by omega, by omega⟩ _⟩
    by_cases he : q = a * x.n + b
    · subst q
      rw [Function.update_self, scan_flag_eq x.AB x.BC x.AC ha hb]
    · rw [Function.update_of_ne (by omega)]
      exact hdone q (by omega)

theorem spec {lim : Limits} {P : Program} {d pScan : ℕ}
    (hP : P[pScan]? = some scanBody) (x : AllEdgesInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Ends lim P d (body pScan) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩ (time x.n)
      fun σ' => Seg σ'.mem x.out (abZeroFlags x.n x.AB x.BC x.AC) ∧
        KeptBut μ σ'.mem fr x.out (x.n * x.n) := by
  (obtain ⟨⟩ := id hpre.toPre)
  (obtain ⟨⟩ := id hpre)
  have hw := hok.space
  have hs := hok.cells
  have hn2 : x.n ≤ x.n * x.n := Nat.le_mul_self _
  refine Ends.for (fun a σ => ∃ b r μ', σ = ⟨frame (locals x fr a b r), μ'⟩ ∧
    Mem x μ a 0 μ') x.n (x.n * (24 * x.n + 70) + 6) ?start ?round ?done ?bound
    (hT := ?time)
  case start =>
    refine ⟨0, 0, μ, ?_, fun q hq => absurd hq (by omega), .refl⟩
    rw [update_frame_setLocal, ← frame_append_zeros _ 2]
    rfl
  case bound => rintro a _ - - ⟨b, r, μ', rfl, -⟩; simp
  case round =>
    rintro a _ ha - ⟨b, r, μ', rfl, hm⟩
    refine (inner_spec hP hpre hok ha hm).mono le_rfl ?_
    rintro _ ⟨r', μ'', rfl, hm'⟩
    exact ⟨by simp, x.n, r', μ'', by rw [update_frame_setLocal]; rfl, hm'⟩
  case done =>
    rintro _ - ⟨b, r, μ', rfl, hdone, hrest⟩
    exact ⟨fun q hq => (hdone q (by simpa using hq)).trans (List.getD_eq_getElem _ _ hq),
      fun c hc => hrest c hc.2⟩
  case time =>
    by_cases hn1 : x.n = 1
    · simp [time, hn1]
    have hn2 : 2 ≤ x.n := by omega
    have hsq2 : 2 * x.n ^ 2 ≤ x.n ^ 3 := by
      calc
        2 * x.n ^ 2 ≤ x.n * x.n ^ 2 := Nat.mul_le_mul_right (x.n ^ 2) hn2
        _ = x.n ^ 3 := by ring
    have hsq : x.n ^ 2 ≤ x.n ^ 3 := Nat.pow_le_pow_right hpre.n_pos (by omega)
    have hlin : x.n ≤ x.n ^ 3 := Nat.le_self_pow (by omega) x.n
    simp [time]
    ring_nf
    omega

theorem solves : Solves allEdgesTask [body 1, scanBody] 0 (fun n _ => time n) bruteNeed :=
  ⟨body 1, rfl, fun _ _ _ x μ fr hpre hok => spec rfl x μ fr hpre hok⟩

end AllEdgesBrute

theorem AllEdges.claim_bruteForce : Claim.BruteForce AllEdges.allEdgesModel := by
  refine ⟨300, [AllEdgesBrute.body 1, scanBody], 0,
    fun n _ => AllEdgesBrute.time n, bruteNeed, ?_, AllEdgesBrute.solves,
    fun n U u hn _ _ => ?_⟩
  · unfold bruteNeed
    (refine Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
        first
        |
          ((apply ThreeSumApsp.Scale.SoftO.mono);
            (·
                repeat'
                  with_reducible
                    first
                    | exact ThreeSumApsp.Scale.SoftO.const _
                    | apply Light.PolyBounded.fst
                    | apply Light.PolyBounded.snd
                    | apply ThreeSumApsp.Scale.SoftO.log
                    | apply ThreeSumApsp.Scale.SoftO.sqrt
                    | apply ThreeSumApsp.Scale.SoftO.add
                    | apply ThreeSumApsp.Scale.SoftO.mul
                    | apply ThreeSumApsp.Scale.SoftO.pow
                    | apply ThreeSumApsp.Scale.SoftO.max
                    | apply ThreeSumApsp.Scale.SoftO.sub
                    | apply ThreeSumApsp.Scale.SoftO.div);
            (·
                first
                | decide
                | exact isEmptyElim))
        |
          ((fail_if_success
                (fail_if_success
                    ((apply ThreeSumApsp.Scale.SoftO.mono);
                      (on_goal 1 =>
                          ((repeat'
                                with_reducible
                                  first
                                  | exact ThreeSumApsp.Scale.SoftO.const _
                                  | apply Light.PolyBounded.fst
                                  | apply Light.PolyBounded.snd
                                  | apply ThreeSumApsp.Scale.SoftO.log
                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                  | apply ThreeSumApsp.Scale.SoftO.add
                                  | apply ThreeSumApsp.Scale.SoftO.mul
                                  | apply ThreeSumApsp.Scale.SoftO.pow
                                  | apply ThreeSumApsp.Scale.SoftO.max
                                  | apply ThreeSumApsp.Scale.SoftO.sub
                                  | apply ThreeSumApsp.Scale.SoftO.div);
                            (done))))));
            (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
            (all_goals
                try
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (·
                        repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                    (· decide))))
        |
          ((apply ThreeSumApsp.Scale.SoftO.mono);
            (·
                repeat'
                  with_reducible
                    first
                    | exact ThreeSumApsp.Scale.SoftO.const _
                    | apply Light.PolyBounded.fst
                    | apply Light.PolyBounded.snd
                    | apply ThreeSumApsp.Scale.SoftO.log
                    | apply ThreeSumApsp.Scale.SoftO.sqrt
                    | apply ThreeSumApsp.Scale.SoftO.add
                    | apply ThreeSumApsp.Scale.SoftO.mul
                    | apply ThreeSumApsp.Scale.SoftO.pow
                    | apply ThreeSumApsp.Scale.SoftO.max
                    | apply ThreeSumApsp.Scale.SoftO.sub
                    | apply ThreeSumApsp.Scale.SoftO.div)))
  · have hlog : 0 ≤ logU u := Real.log_nonneg (le_trans (by norm_num) (le_max_right u 2))
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
    calc ((AllEdgesBrute.time n : ℕ) : ℝ) = 100 * (n : ℝ) ^ 3 + 100 := by
          rw [AllEdgesBrute.time]; push_cast; rfl
      _ ≤ 300 * ((n : ℝ) ^ 3 * 1) := by linarith
      _ ≤ 300 * ((n : ℝ) ^ 3 * (1 + logU u)) := by gcongr; linarith

end APSPImprovement




end
end

section


@[expose] public section

namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

def bySizeBody (n₀ p₁ p₂ : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (v 0) (k n₀))) (.call p₁ [v 0, v 1, v 2, v 3, v 4, v 5, v 6] 0)
    (.call p₂ [v 0, v 1, v 2, v 3, v 4, v 5, v 6] 0)

def bySizeTime (n₀ : ℕ) (T₁ T₂ : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  (if n < n₀ then T₁ n U else T₂ n U) + 13

theorem bySize_spec {lim : Limits} {d : ℕ} {P₀ R : Program} {n₀ p₁ p₂ : ℕ}
    {T₁ T₂ : ℕ → ℕ → ℕ} {r₁ r₂ : ℕ → ℕ → Need}
    (h₁ : Solves allEdgesTask P₀ p₁ T₁ r₁) (h₂ : Solves allEdgesTask P₀ p₂ T₂ r₂)
    {x : AllEdgesInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (Light.Sec3.bySizeNeed n₀ r₁ r₂ x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (bySizeBody n₀ p₁ p₂) ⟨frame (allEdgesTask.args x ++ [(fr : ℤ)]), μ⟩
      (bySizeTime n₀ T₁ T₂ x.n x.U) fun σ' => allEdgesTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hword : ((n₀ + (r₁ x.n x.U).word + (r₂ x.n x.U).word : ℕ) : ℤ) ≤ lim.word := hok.word
  have hdep : d + (1 + (r₁ x.n x.U).depth + (r₂ x.n x.U).depth) ≤ lim.depth := hok.depth
  have hok₁ : (r₁ x.n x.U).Ok lim fr (d + 1) := hok.mono
    (by simp only [Light.Sec3.bySizeNeed]; omega)
    (by simp only [Light.Sec3.bySizeNeed]; omega)
    (by simp only [Light.Sec3.bySizeNeed]; omega)
  have hok₂ : (r₂ x.n x.U).Ok lim fr (d + 1) := hok.mono
    (by simp only [Light.Sec3.bySizeNeed]; omega)
    (by simp only [Light.Sec3.bySizeNeed]; omega)
    (by simp only [Light.Sec3.bySizeNeed]; omega)
  have hm₁ : Meets lim (P₀ ++ R) p₁ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr]
      μ (T₁ x.n x.U) (allEdgesTask.Post x μ fr) := h₁.meets R x fr hpre hok₁
  have hm₂ : Meets lim (P₀ ++ R) p₂ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr]
      μ (T₂ x.n x.U) (allEdgesTask.Post x μ fr) := h₂.meets R x fr hpre hok₂
  change Ends lim (P₀ ++ R) d (bySizeBody n₀ p₁ p₂)
    ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩ _ _
  unfold bySizeTime
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · rw [if_pos (show x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₁ fun _ _ h => h
  · rw [if_neg (show ¬ x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₂ fun _ _ h => h

theorem closure_chooseBySize : Closure.ChooseBySize allEdgesModel := by
  refine fun n₀ => ⟨13, fun T₁ T₂ hT₁ hT₂ => ?_⟩
  obtain ⟨Q₁, p₁, Tn₁, r₁, hr₁, hs₁, ht₁⟩ := hT₁
  obtain ⟨Q₂, p₂, Tn₂, r₂, hr₂, hs₂, ht₂⟩ := hT₂
  have g₁ : Solves allEdgesTask (Program.behind Q₁ Q₂) p₁ Tn₁ r₁ := hs₁.append _
  have g₂ : Solves allEdgesTask (Program.behind Q₁ Q₂) (p₂ + Q₁.length) Tn₂ r₂ :=
    ChooseHost.solves_behind hs₂ Q₁
  refine ⟨Program.behind Q₁ Q₂ ++ [bySizeBody n₀ p₁ (p₂ + Q₁.length)],
    (Program.behind Q₁ Q₂).length, bySizeTime n₀ Tn₁ Tn₂,
    Light.Sec3.bySizeNeed n₀ r₁ r₂, ChooseHost.polyNeed_bySize n₀ hr₁ hr₂, ?_,
    fun n U u hn hU hu => ?_⟩
  · refine ⟨bySizeBody n₀ p₁ (p₂ + Q₁.length), by simp,
      fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact bySize_spec g₁ g₂ hpre hok
  · simp only [bySizeTime]
    push_cast
    split_ifs
    · linarith [ht₁ n U u hn hU hu]
    · linarith [ht₂ n U u hn hU hu]

end APSPImprovement.AllEdges



end
end

section


/-!
# Corollary 15: counting triangles with the thin matrix product, and detecting with counting

Two steps of the proof of Corollary 15, with "the problem is solved in time T" read as
`ThinSolvedIn` and `LopSolvedIn`.

* `Claim.LopCountFromThinProduct`: "Apply Theorem 5 with N = n to the two biadjacency matrices".  An
  instance of #Lop-AE-SparseTri is given by its two biadjacency matrices, so a solver of the thin
  matrix product is a solver of #Lop-AE-SparseTri as it stands, called with U = 1, where U, the
  fourth argument and parameter, is the bound on the entries of the matrices
  (`solvesN_count_of_thin`, `claim_lopCountFromThinProduct`).
* `Claim.LopDetectFromCount`: the counts "are nonzero exactly for the query pairs that lie in a
  triangle".  One more procedure calls the counting solver and replaces every nonzero count by 1
  (`detect_spec`, `claim_lopDetectFromCount`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

namespace LopHosts

/-! ## Bounds -/

/-- One more parameter with the value 1 costs a factor `2^e`. -/
theorem polyBound_snoc_one (s e : ℕ) (ps : List ℕ) :
    polyBound s e (ps ++ [1]) = polyBound (s + e) e ps := by
  simp only [polyBound, List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one,
    mul_pow, pow_add]
  norm_num
  ring

/-- Twice the bound leaves room for one more. -/
theorem polyBound_le_succ (s e : ℕ) (ps : List ℕ) :
    polyBound s e ps + 1 ≤ polyBound (1 + s) e ps := by
  have h1 := one_le_polyBound s e ps
  rw [← polyBound_mul]
  omega

/-! ## Counting with the thin matrix product -/

/-- A solver of the thin matrix product solves #Lop-AE-SparseTri. -/
theorem solvesN_count_of_thin {P : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (h : SolvesN thinTask P p Tn need) :
    SolvesN lopCountTask P p (fun ps => Tn (ps ++ [1])) fun ps => need (ps ++ [1]) := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, hp, fun R lim d x μ fr hpre hok => ?_⟩
  obtain ⟨h1, -, h3⟩ := hpre
  have hpars : thinTask.pars x = lopCountTask.pars x ++ [1] := by
    simp only [thinTask, lopCountTask, List.cons_append, List.nil_append]
    rw [h3]
  have hrun := hb R lim d x μ fr h1 (hpars ▸ hok)
  rwa [hpars] at hrun

/-- A polynomially bounded need stays so when a parameter is fixed to 1. -/
theorem polyNeedN_snoc_one {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN fun ps => need (ps ++ [1]) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨s + e, e, fun ps => ?_⟩
  rw [← polyBound_snoc_one]
  exact h _

end LopHosts

open LopHosts

/-- **Counting common neighbours is a thin matrix product** (Section 3.1). -/
theorem claim_lopCountFromThinProduct : Claim.LopCountFromThinProduct lightModel := by
  refine ⟨0, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P, p, _, _, polyNeedN_snoc_one hneed, solvesN_count_of_thin hsol,
    fun n D w w' hn hD hw => ?_⟩
  have := htime n D w w' 1 1 hn hD le_rfl hw (by norm_num)
  simpa using this

/-! ## Detecting with counting -/

namespace LopArgs














end LopArgs
















namespace LopHosts

/-- There is one answer for each wanted position. -/
theorem length_thinOut (N D : ℕ) (X Y : List ℤ) {WI WJ : List ℕ} {w : ℕ} (h1 : WI.length = w)
    (h2 : WJ.length = w) : (thinOut N D X Y WI WJ).length = w := by
  simp [thinOut, h1, h2]

/-- **detect** solves Lop-AE-SparseTri. -/
theorem detect_spec {P₀ R : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (hsol : SolvesN lopCountTask P₀ p Tn need) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : lopDetectTask.Pre x μ fr)
    (hok : (lopDetectNeed need (lopDetectTask.pars x)).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (lopDetectBody p) ⟨frame (lopDetectTask.args x ++ [(fr : ℤ)]), μ⟩
      (lopDetectTime Tn (lopDetectTask.pars x))
      fun σ' => lopDetectTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hw := hok.space
  have hcells := hok.cells
  have hdep : d + ((need [x.N, x.D, x.w]).depth + 1) ≤ lim.depth := hok.depth
  have bO := hpre.1.belowOut
  have hlen := length_thinOut x.N x.D x.X x.Y hpre.1.lenWI hpre.1.lenWJ
  have hm : Meets lim (P₀ ++ R) p (d + 1)
      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (Tn [x.N, x.D, x.w]) fun _ μ₁ =>
        Seg μ₁ x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ₁ fr x.out x.w :=
    hsol.meets R x hpre (hok.mono le_rfl le_rfl (by
      change d + 1 + (need [x.N, x.D, x.w]).depth ≤ d + ((need [x.N, x.D, x.w]).depth + 1)
      omega))
  change Ends lim (P₀ ++ R) d (lopDetectBody p)
    ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (Tn [x.N, x.D, x.w] + 20 * x.w + 18) _
  -- the counts
  refine Ends.callToThen hm fun r μ₁ ⟨hseg, hk⟩ => ?_
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, ∀ i, f i = if μ₁ (x.out + i) = 0 then 0 else 1 := ⟨_, fun _ => rfl⟩
  -- for i < w: the first i counts have been replaced
  refine Ends.forFrame (fun j μ' => μ' = wrote μ₁ x.out f j) x.w wrote_zero.symm ?round ?done
    (hT := by simp; omega)
  case round =>
    rintro j _ hj rfl
    have hread : wrote μ₁ x.out f j (x.out + j) = μ₁ (x.out + j) := wrote_rest (by omega)
    rw [← wrote_succ]
    -- if out[i] ≠ 0 then out[i] := 1
    refine Ends.iteLast (fun hc => Ends.skip ⟨rfl, ?_⟩) fun hc =>
      Ends.storeTo (x.out + j) 1 ⟨rfl, ?_⟩
    · have hc : μ₁ (x.out + j) = 0 := by simpa [hread] using hc
      have e : f j = wrote μ₁ x.out f j (x.out + j) := by rw [hf, if_pos hc, hread, hc]
      rw [e, Function.update_eq_self]
    · have hc : μ₁ (x.out + j) ≠ 0 := by simpa [hread] using hc
      rw [hf, if_neg hc]
  case done =>
    rintro _ rfl
    refine ⟨fun i hi => ?_, fun a ha => (wrote_rest ha.2).trans (hk a ha)⟩
    have hi' : i < x.w := by simpa [hlen] using hi
    rw [List.getElem_map, ← hseg i (by omega), ← hf]
    exact wrote_done hi'

/-- The need of detect is polynomially bounded if that of the counting solver is. -/
theorem polyNeedN_detect {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN (lopDetectNeed need) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨1 + s, e, fun ps => ?_⟩
  have h1 := polyBound_le_succ s e ps
  obtain ⟨a, b, c⟩ := h ps
  simp only [lopDetectNeed]
  omega

end LopHosts

open LopHosts

/-- **Detection from counting** (proof of Corollary 15). -/
theorem claim_lopDetectFromCount : Claim.LopDetectFromCount lightModel := by
  refine ⟨20, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P ++ [lopDetectBody p], P.length, lopDetectTime Tn, lopDetectNeed need,
    polyNeedN_detect hneed, ?_, fun n D w w' hn hD hw => ?_⟩
  · refine ⟨lopDetectBody p, by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact detect_spec hsol hpre hok
  · have h1 := htime n D w w' hn hD hw
    have h2 : (w : ℝ) ≤ w' := by exact_mod_cast hw
    simp only [lopDetectTime, List.getD_cons_succ, List.getD_cons_zero]
    push_cast
    linarith

end Light.Sec3

end
end

section


/-!
# Theorem 17, first step: hashing modulo a prime

The first step of the proof of Theorem 17 reduces the weights modulo a prime `p` in the range
`[√D/2, √D)` with few false positives.

* **Counting.**  The number of triples with `S(a,b,c) ≡ 0 (mod p)` is `F(p) + Z₀`
  (`TriangleInstance.countZeroMod_eq`), and it can be read off the product of two matrices over
  `ℤ[x]/(x^p − 1)` (`TriangleInstance.coeff_matP_mul_matQ`,
  `TriangleInstance.F_add_Z₀_eq_sum_coeff`).  There are fewer than `√D` primes in the range
  (`card_primesInRange_lt`).
* **Selecting.**  The prime with the smallest count exists
  (`TriangleInstance.exists_isSelectedPrime`) and has the fewest false positives
  (`TriangleInstance.IsSelectedPrime.F_le`).
* **The bound on `F(p)`**, `TriangleInstance.F_le_of_le_card_primesInRange` and
  `TriangleInstance.exists_F_le`.  A triple is a false positive of at most `log_{√D/2}(3n^ν)` primes
  in the range (`TriangleInstance.card_falsePositive_primes_le`), so the numbers `F(q)` add up to at
  most `n³` times that (`TriangleInstance.sum_F_le`); there are `Ω(√D/log D)` primes in the range
  (`exists_le_card_primesInRange`); `F(p)` is at most the average
  (`TriangleInstance.IsSelectedPrime.F_mul_card_le_sum`); and `log D ≤ 4 log(√D/2)`
  (`log_le_four_mul_log_sqrt_div_two`).  The constant of the bound has a name,
  `Hashing.falsePositiveConst`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ### The primes in the range -/












/-! ### The ring `ℤ[x]/(x^p − 1)` -/






namespace CyclicRing

open Polynomial

variable {p : ℕ}











/-- The coefficient, in terms of the representing polynomial. -/
theorem coeff_apply (hp : p ≠ 0) (r : ℕ) (z : CyclicRing p) :
    coeff hp r z = (AdjoinRoot.modByMonicHom (monic_X_pow_sub_C (1 : ℤ) hp) z).coeff r :=
  rfl

/-- In `ℤ[x]/(x^p − 1)` we have `x^p = 1`. -/
private theorem x_pow_self (p : ℕ) : x p ^ p = 1 := by
  have h : AdjoinRoot.mk ((X : ℤ[X]) ^ p - C 1) ((X : ℤ[X]) ^ p - C 1) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, C_1, map_one] at h
  exact sub_eq_zero.1 h

/-- The coefficient of `x^r` in the power `x^k` of `ℤ[x]/(x^p − 1)` is 1 if `r = k mod p` and 0
otherwise. -/
theorem coeff_x_pow (hp : p ≠ 0) (k r : ℕ) :
    coeff hp r (x p ^ k) = if r = k % p then 1 else 0 := by
  have hred : x p ^ k = x p ^ (k % p) := by
    conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul, x_pow_self, one_pow, one_mul]
  have hdeg : ((X : ℤ[X]) ^ (k % p)).degree < ((X : ℤ[X]) ^ p - C 1).degree := by
    rw [degree_X_pow, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
    exact_mod_cast Nat.mod_lt k (Nat.pos_of_ne_zero hp)
  rw [coeff_apply, hred, x, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (monic_X_pow_sub_C (1 : ℤ) hp)).2 hdeg, coeff_X_pow]

end CyclicRing

/-- A number `r < p` is the sum of the residues of `u` and `v` in `{0, …, p − 1}`, reduced modulo
`p`, exactly if `u + v ≡ r`. -/
private theorem eq_add_toNat_emod_iff {p r : ℕ} (hp : p ≠ 0) (hr : r < p) (u v : ℤ) :
    r = ((u % (p : ℤ)).toNat + (v % (p : ℤ)).toNat) % p ↔ u + v ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [← Int.natCast_inj, Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (by exact_mod_cast hr),
    eq_comm]
  push_cast
  rw [Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp),
    Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp),
    ← Int.add_emod]

/-! ### Counting the triples with `S(a,b,c) ≡ 0 (mod p)` -/

namespace TriangleInstance

variable {n : ℕ} (T : TriangleInstance ℤ n)



































/-- Proof of Theorem 17: "the coefficient of x^r in (PQ)[a,b] is the number of c ∈ C with w(a,c) +
w(b,c) ≡ r (mod p)". -/
theorem coeff_matP_mul_matQ {p : ℕ} (hp : p ≠ 0) (a b : Fin n) (r : ℕ) (hr : r < p) :
    CyclicRing.coeff hp r ((T.matP p * T.matQ p) a b) =
      ((Finset.univ.filter fun c : Fin n =>
        T.wAC a c + T.wBC b c ≡ (r : ℤ) [ZMOD (p : ℤ)]).card : ℤ) := by
  classical
  -- `(PQ)[a,b]` is the sum over `c` of `x^(w(a,c) mod p + w(b,c) mod p)`, and the coefficient of
  -- `x^r` in each term is 1 or 0.
  rw [Matrix.mul_apply]
  simp only [matP, matQ, Matrix.of_apply, ← pow_add]
  rw [map_sum]
  simp only [CyclicRing.coeff_x_pow]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [eq_add_toNat_emod_iff hp hr]

/-- Proof of Theorem 17: "then F(p) + Z₀ is the sum over the pairs (a,b) ∈ A × B of the coefficient
of x^{−w(a,b) mod p} in (PQ)[a,b]". -/
theorem F_add_Z0_eq_sum_coeff {p : ℕ} (hp : p ≠ 0) :
    ((T.F p + T.Z₀ : ℕ) : ℤ) =
      ∑ a : Fin n, ∑ b : Fin n,
        CyclicRing.coeff hp ((-T.wAB a b) % (p : ℤ)).toNat ((T.matP p * T.matQ p) a b) := by
  classical
  rw [← countZeroMod_eq]
  unfold countZeroMod
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcast := Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) (-T.wAB a b)
  rw [T.coeff_matP_mul_matQ hp a b _ (Int.toNat_emod_lt (Nat.pos_of_ne_zero hp) _),
    Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  -- `S(a,b,c) ≡ 0` says the same as `w(a,c) + w(b,c) ≡ -w(a,b)`, and `-w(a,b)` is congruent to its
  -- residue.
  have hres : (-T.wAB a b) % (p : ℤ) ≡ -T.wAB a b [ZMOD (p : ℤ)] := Int.mod_modEq _ _
  have hiff : T.S a b c ≡ 0 [ZMOD (p : ℤ)] ↔
      T.wAC a c + T.wBC b c ≡ ((((-T.wAB a b) % (p : ℤ)).toNat : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
    rw [hcast, show T.wAC a c + T.wBC b c ≡ (-T.wAB a b) % (p : ℤ) [ZMOD (p : ℤ)] ↔
        T.wAC a c + T.wBC b c ≡ -T.wAB a b [ZMOD (p : ℤ)] from
      ⟨fun h => h.trans hres, fun h => h.trans hres.symm⟩,
      Int.modEq_iff_dvd, Int.modEq_iff_dvd,
      show 0 - T.S a b c = -T.wAB a b - (T.wAC a c + T.wBC b c) by
        simp only [S]; ring]
  simp only [hiff]

end TriangleInstance


















/-! ### Selecting the prime -/

namespace TriangleInstance

variable {n D p : ℕ} {κ : ℝ} (T : TriangleInstance ℤ n)

/-- Proof of Theorem 17.  There is a prime to select. -/
theorem exists_isSelectedPrime (D : ℕ) (hD : 16 ≤ D) : ∃ p, T.IsSelectedPrime D p := by
  obtain ⟨q, hq⟩ :=
    Nat.exists_prime_half_le_and_lt (Real.sqrt D) (Real.four_le_sqrt_natCast_of_sixteen_le hD)
  exact Finset.exists_min_image (primesInRange D) T.countZeroMod ⟨q, mem_primesInRange.2 hq⟩










/-! ### The bound on the number of false positives of the selected prime -/
















































































end TriangleInstance

































































































/-- The constant is at least 1. -/
theorem Hashing.one_le_falsePositiveConst : 1 ≤ Hashing.falsePositiveConst :=
  (Classical.choose_spec TriangleInstance.exists_F_le).1

/-- Proof of Theorem 17: "F(p) = [...] = O(ν n³ log n/√D)", with `Hashing.falsePositiveConst` as the
constant. -/
theorem Hashing.F_le_falsePositiveConst_mul {n D p : ℕ} {κ : ℝ} (hD : 16 ≤ D) (hDn : D ≤ n)
    (hκ : 1 ≤ κ) (T : TriangleInstance ℤ n) (hT : T.WeightsPolyBounded κ)
    (hp : T.IsSelectedPrime D p) :
    (T.F p : ℝ) ≤ Hashing.falsePositiveConst * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) :=
  (Classical.choose_spec TriangleInstance.exists_F_le).2 hD hDn hκ T hT hp

end ThreeSumApsp

end
end

section


/-!
# The ring `ℤ[x]/(x^p − 1)` as vectors of `p` integers

The proof of Theorem 17 computes with matrices over the ring `ℤ[x]/(x^p − 1)`.  For a program an
element of the ring is the list of its `p` coefficients (`cycVec`).  This file shows that the
operations of the ring are operations on lists that use no division:

* zero, sums and differences are entrywise (`cycVec_zero`, `cycVec_add`, `cycVec_sub`);
* a power of `x` is a unit vector (`cycVec_x_pow`);
* multiplication is cyclic convolution, "O(p²) word operations" (`cycVec_mul`).  For the proof both
  factors are expanded in powers of `x` (`eq_sum_coeff`), and `x^i x^j` contributes to the
  coefficient of `x^r` exactly if `i + j ≡ r (mod p)`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec




















variable {p : ℕ} (hp : p ≠ 0)

/-! ## Coefficients -/

/-- The representative of degree less than `p` has no coefficients from `p` on. -/
theorem coeff_eq_zero_of_le (z : CyclicRing p) {r : ℕ} (hr : p ≤ r) :
    CyclicRing.coeff hp r z = 0 := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [CyclicRing.coeff_apply, AdjoinRoot.modByMonicHom_mk]
  refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
    (Polynomial.degree_modByMonic_lt f (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp)) ?_)
  rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
  exact_mod_cast hr

/-- An element of the ring is the combination of the powers of `x` with its coefficients. -/
theorem eq_sum_coeff (z : CyclicRing p) :
    z = ∑ i ∈ Finset.range p, CyclicRing.coeff hp i z • CyclicRing.x p ^ i := by
  have hmk := AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp) z
  set f := AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp) z with hf
  have hdeg : f.natDegree < p := by
    by_contra hc
    have hlead : f.coeff f.natDegree = 0 := coeff_eq_zero_of_le hp z (not_lt.mp hc)
    rw [Polynomial.leadingCoeff_eq_zero.mp hlead, Polynomial.natDegree_zero] at hc
    exact hc (Nat.pos_of_ne_zero hp)
  conv_lhs => rw [← hmk, Polynomial.as_sum_range' f p hdeg, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    zsmul_eq_mul]
  simp [CyclicRing.coeff_apply, CyclicRing.x, hf]

/-- For `i, j, r < p`: `i + j ≡ r (mod p)` exactly if `j` is `r - i` or `r + p - i`. -/
private theorem eq_add_mod_iff {p i j r : ℕ} (hi : i < p) (hj : j < p) (hr : r < p) :
    r = (i + j) % p ↔ j = if i ≤ r then r - i else r + p - i := by
  by_cases h : i + j < p
  · rw [Nat.mod_eq_of_lt h]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

/-! ## Vectors -/

/-- A vector has `p` entries. -/
theorem length_cycVec (z : CyclicRing p) : (cycVec hp z).length = p := by
  simp [cycVec]

/-- Entry `r` of the vector is the coefficient of `x^r`. -/
theorem getD_cycVec (z : CyclicRing p) {r : ℕ} (hr : r < p) :
    (cycVec hp z).getD r 0 = CyclicRing.coeff hp r z :=
  List.getD_map_range _ hr 0

/-- The vector of 0. -/
theorem cycVec_zero : cycVec hp 0 = List.replicate p 0 := by
  rw [cycVec, List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hb
  exact map_zero (CyclicRing.coeff hp r)

/-- The vector of a sum. -/
theorem cycVec_add (z w : CyclicRing p) :
    cycVec hp (z + w) = vadd (cycVec hp z) (cycVec hp w) := by
  refine List.ext_getElem (by simp [vadd, length_cycVec]) fun r _ _ => ?_
  simp only [vadd, cycVec, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  exact map_add (CyclicRing.coeff hp r) z w

/-- The vector of a difference. -/
theorem cycVec_sub (z w : CyclicRing p) :
    cycVec hp (z - w) = vsub (cycVec hp z) (cycVec hp w) := by
  refine List.ext_getElem (by simp [vsub, length_cycVec]) fun r _ _ => ?_
  simp only [vsub, cycVec, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  exact map_sub (CyclicRing.coeff hp r) z w

/-- The vector of a power of `x`. -/
theorem cycVec_x_pow (k : ℕ) : cycVec hp (CyclicRing.x p ^ k) = vunit p (k % p) :=
  List.map_congr_left fun r _ => CyclicRing.coeff_x_pow hp k r

/-- Multiplication in the ring is cyclic convolution. -/
theorem cycVec_mul (z w : CyclicRing p) :
    cycVec hp (z * w) = cconv p (cycVec hp z) (cycVec hp w) := by
  refine List.map_congr_left fun r hr => ?_
  have hr' := List.mem_range.mp hr
  -- Expand both factors in powers of x.
  conv_lhs => rw [eq_sum_coeff hp z, eq_sum_coeff hp w, Finset.sum_mul_sum]
  rw [map_sum, List.sum_map_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  -- For each i, only one j contributes to the coefficient of x^r.
  have hj : (if i ≤ r then r - i else r + p - i) < p := by split_ifs <;> omega
  rw [getD_cycVec hp z hi', getD_cycVec hp w hj, map_sum]
  simp only [smul_mul_smul_comm, ← pow_add, map_zsmul, CyclicRing.coeff_x_pow, smul_eq_mul]
  rw [Finset.sum_eq_single (if i ≤ r then r - i else r + p - i)]
  · rw [if_pos ((eq_add_mod_iff hi' hj hr').mpr rfl), mul_one]
  · intro j hj' hne
    rw [if_neg fun h => hne ((eq_add_mod_iff hi' (Finset.mem_range.mp hj') hr').mp h), mul_zero]
  · exact fun h => absurd (Finset.mem_range.mpr hj) h

end ThreeSumApsp.Spec

end
end

section


/-!
# Hashing modulo a prime (proof of Theorem 17), on numbers and lists

The reduction of Theorem 17 hashes the weights modulo a prime `p` of the window `√D/2 ≤ p < √D` and
selects the prime with the fewest triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`, where
`S(a,b,c) = w(a,b) + w(b,c) + w(a,c)`.  This file has the parts of this step that a program
computes:

* the residue of a weight as a natural number below `p` (`resid`, `residList`);
* the entries of the matrices `P` and `Q` of the proof of Theorem 17 as unit vectors (`cycVec_matP`,
  `cycVec_matQ`), and the count of the triples, read off the vectors of `PQ` (`countZeroMod_eq`);
* the primes of the window by comparisons of integers (`primesList`, `primesInRange_eq`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Residues -/




/-- The residue, as an integer. -/
theorem resid_cast {p : ℕ} (hp : p ≠ 0) (w : ℤ) : (resid p w : ℤ) = w % (p : ℤ) :=
  Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) w

/-- The residue is less than `p`. -/
theorem resid_lt {p : ℕ} (hp : p ≠ 0) (w : ℤ) : resid p w < p :=
  Int.toNat_emod_lt (Nat.pos_of_ne_zero hp) w

/-- The residue is the number below `p` that is congruent to `w`. -/
theorem resid_eq_iff {p : ℕ} (hp : p ≠ 0) (w : ℤ) {r : ℕ} (hr : r < p) :
    resid p w = r ↔ w ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (Int.ofNat_lt.2 hr), ← resid_cast hp,
    Nat.cast_inj]

/-- The residue of `-w` from the residue of `w`. -/
theorem resid_neg {p : ℕ} (hp : p ≠ 0) (w : ℤ) : resid p (-w) = (p - resid p w) % p := by
  refine (resid_eq_iff hp _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hp))).2 ?_
  have hself : (p : ℤ) ≡ 0 [ZMOD (p : ℤ)] := Int.emod_self.trans (Int.zero_emod _).symm
  have hsub := (Int.mod_modEq ((p : ℤ) - w % p) p).trans (hself.sub (Int.mod_modEq w p))
  rw [Int.natCast_mod, Nat.cast_sub (resid_lt hp w).le, resid_cast hp]
  rw [zero_sub] at hsub
  exact hsub.symm




/-- The residues of a list, read with a default: beyond the end of the list both sides are 0. -/
theorem getD_residList (p : ℕ) (l : List ℤ) (i : ℕ) :
    (residList p l).getD i 0 = resid p (l.getD i 0) := by
  rw [residList, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [resid]







/-! ## The count of the proof of Theorem 17 -/

/-- Proof of Theorem 17: the entry `P[a,c] = x^{w(a,c) mod p}` is a unit vector. -/
theorem cycVec_matP {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ} (hp : p ≠ 0) (a c : Fin n) :
    cycVec hp (T.matP p a c) = vunit p (resid p (T.wAC a c)) := by
  rw [TriangleInstance.matP, Matrix.of_apply, cycVec_x_pow]
  exact congrArg (vunit p) (Nat.mod_eq_of_lt (resid_lt hp _))

/-- Proof of Theorem 17: the entry `Q[c,b] = x^{w(b,c) mod p}` is a unit vector. -/
theorem cycVec_matQ {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ} (hp : p ≠ 0) (c b : Fin n) :
    cycVec hp (T.matQ p c b) = vunit p (resid p (T.wBC b c)) := by
  rw [TriangleInstance.matQ, Matrix.of_apply, cycVec_x_pow]
  exact congrArg (vunit p) (Nat.mod_eq_of_lt (resid_lt hp _))

/-- Proof of Theorem 17: the count of the triples with `S(a,b,c) ≡ 0 (mod p)` is "the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]". -/
theorem countZeroMod_eq {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ} (hp : p ≠ 0) :
    (T.countZeroMod p : ℤ) =
      ∑ a, ∑ b, (cycVec hp ((T.matP p * T.matQ p) a b)).getD (resid p (-T.wAB a b)) 0 := by
  rw [TriangleInstance.countZeroMod_eq, TriangleInstance.F_add_Z0_eq_sum_coeff T hp]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    (getD_cycVec hp _ (resid_lt hp _)).symm

/-! ## The primes of the window -/





/-- The comparisons with `√D` are comparisons of integers. -/
theorem primesInRange_eq (D : ℕ) : primesInRange D = (primesList D).toFinset := by
  ext q
  have hlow : Real.sqrt D / 2 ≤ (q : ℝ) ↔ D ≤ 4 * q ^ 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), Real.sqrt_le_left (by positivity),
      show ((q : ℝ) * 2) ^ 2 = ((4 * q ^ 2 : ℕ) : ℝ) by push_cast; ring, Nat.cast_le]
  have hhigh : (q : ℝ) < Real.sqrt D ↔ q ^ 2 < D := by
    rw [Real.lt_sqrt (by positivity)]
    exact_mod_cast Iff.rfl
  simp [primesInRange, primesList, hlow, hhigh]

/-- The primes of the window, without the bound `q < D` of the search. -/
theorem mem_primesList {D q : ℕ} : q ∈ primesList D ↔ q.Prime ∧ D ≤ 4 * q ^ 2 ∧ q ^ 2 < D := by
  simp only [primesList, List.mem_filter, List.mem_range, decide_eq_true_eq, and_iff_right_iff_imp]
  exact fun h => (Nat.le_self_pow (by norm_num) q).trans_lt h.2.2

/-- A prime of the window is at most `⌊√D⌋`. -/
theorem le_sqrt_of_mem_primesList {D q : ℕ} (h : q ∈ primesList D) : q ≤ Nat.sqrt D :=
  Nat.le_sqrt'.2 (mem_primesList.1 h).2.2.le











end ThreeSumApsp.Spec

end
end

section


/-!
# The parameters of Theorems 17 and 19 in integer arithmetic

The proof of Theorem 19 chooses `D` and `g` as rounded real powers of `n`: "Let D be the largest
power of four with D ≤ n^{1/18}, […] and let g := ⌈D^{1/36}⌉" on the route through Theorem 5, and
"Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉" on the route through Corollary 26.  The reduction of
Theorem 17 cuts each residue class into chunks of at most `n²/√D` query pairs and splits `C` into
pieces of at most `⌈s/g⌉` vertices, where `s = ⌊√D⌋`.  A program finds all these numbers by
operations on natural numbers.

* `rootFloor e t` is `⌊t^{1/e}⌋` and `rootCeil e t` is `⌈t^{1/e}⌉` (`floor_rpow_inv`,
  `ceil_rpow_inv`); they are characterised by `x ≤ rootFloor e t ↔ x^e ≤ t` (`le_rootFloor_iff`) and
  `rootCeil e t ≤ g ↔ t ≤ g^e` (`rootCeil_le_iff`).
* The four functions `paramD₅Nat`, `paramG₅Nat`, `paramD₂₆Nat`, `paramG₂₆Nat` are the parameters
  of the proof of Theorem 19 (`paramD₅Nat_eq`, `paramG₅Nat_eq`, `paramD₂₆Nat_eq`, `paramG₂₆Nat_eq`);
  they are at least 1 and at most `n` or `D` (`paramD₂₆Nat_le`, `paramG₅Nat_le`, `paramG₂₆Nat_le`).
* The sizes of the proof of Theorem 17: `⌊n²/√D⌋ = ⌊√(n⁴/D)⌋` (`queryCapNat_eq`), `s` is the integer
  square root (`sOf_eq_sqrt`), and the rounded quotients are `a ⌈/⌉ b` (`pieceSizeNat_eq`,
  `numPiecesNat_eq`, `numChunks_eq`).  The middle part `C_k × ℤ_p` of an instance has at most `D`
  vertices (`pieceSize_mul_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Roots, rounded down and up -/







/-- The power of `rootFloor e t` does not exceed `t`. -/
theorem rootFloor_pow_le {e : ℕ} (he : e ≠ 0) (t : ℕ) : rootFloor e t ^ e ≤ t :=
  Nat.findGreatest_spec (P := fun x => x ^ e ≤ t) (Nat.zero_le t) (by simp [he])

/-- `rootFloor e t` is the greatest `x` with `x^e ≤ t`. -/
theorem le_rootFloor {e : ℕ} (he : e ≠ 0) {t x : ℕ} (h : x ^ e ≤ t) : x ≤ rootFloor e t :=
  Nat.le_findGreatest ((Nat.le_self_pow he x).trans h) h

/-- The characterisation of `rootFloor` by which a program finds it. -/
theorem le_rootFloor_iff {e : ℕ} (he : e ≠ 0) {t x : ℕ} : x ≤ rootFloor e t ↔ x ^ e ≤ t :=
  ⟨fun h => (Nat.pow_le_pow_left h e).trans (rootFloor_pow_le he t), le_rootFloor he⟩

/-- `rootFloor e t` is `⌊t^{1/e}⌋`. -/
theorem floor_rpow_inv {e : ℕ} (he : e ≠ 0) (t : ℕ) :
    ⌊(t : ℝ) ^ ((e : ℝ)⁻¹)⌋₊ = rootFloor e t := by
  refine eq_of_forall_le_iff fun x => ?_
  rw [Nat.le_floor_iff (by positivity), Real.natCast_le_rpow_inv_iff he, le_rootFloor_iff he]

/-- The power of `rootCeil e t` reaches `t`. -/
theorem le_rootCeil_pow {e : ℕ} (he : e ≠ 0) (t : ℕ) : t ≤ rootCeil e t ^ e := by
  unfold rootCeil
  set G := Nat.findGreatest (fun g => g ^ e < t) t
  rcases Nat.lt_or_ge t (G + 1) with h | h
  · exact h.le.trans (Nat.le_self_pow he _)
  · exact not_lt.1 (Nat.findGreatest_is_greatest (P := fun g => g ^ e < t) (Nat.lt_succ_self G) h)

/-- `rootCeil e t` is the least `g` with `t ≤ g^e`, for `t ≥ 1`. -/
theorem rootCeil_le {e : ℕ} (he : e ≠ 0) {t g : ℕ} (ht : 1 ≤ t) (h : t ≤ g ^ e) :
    rootCeil e t ≤ g := by
  have hspec : Nat.findGreatest (fun g => g ^ e < t) t ^ e < t :=
    Nat.findGreatest_spec (P := fun g => g ^ e < t) (Nat.zero_le t)
      (show 0 ^ e < t by rw [zero_pow he]; exact ht)
  exact lt_of_pow_lt_pow_left₀ e (Nat.zero_le g) (hspec.trans_le h)

/-- The characterisation of `rootCeil` by which a program finds it. -/
theorem rootCeil_le_iff {e : ℕ} (he : e ≠ 0) {t g : ℕ} (ht : 1 ≤ t) :
    rootCeil e t ≤ g ↔ t ≤ g ^ e :=
  ⟨fun h => (le_rootCeil_pow he t).trans (Nat.pow_le_pow_left h e), rootCeil_le he ht⟩

/-- `rootCeil e t` is `⌈t^{1/e}⌉`, for `t ≥ 1`. -/
theorem ceil_rpow_inv {e : ℕ} (he : e ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    ⌈(t : ℝ) ^ ((e : ℝ)⁻¹)⌉₊ = rootCeil e t := by
  refine eq_of_forall_ge_iff fun g => ?_
  rw [Nat.ceil_le, Real.rpow_inv_le_natCast_iff he, rootCeil_le_iff he ht]

/-! ## The parameters of the proof of Theorem 19 -/













/-- `⌊n^{1/18}⌋`, with the exponent as the paper writes it. -/
private theorem floor_rpow_one_div (n : ℕ) : ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊ = rootFloor 18 n := by
  rw [← floor_rpow_inv (by norm_num)]
  norm_num

/-- "Let D := ⌊n^{1/18}⌋". -/
theorem paramD₂₆Nat_eq (n : ℕ) : paramD₂₆Nat n = paramD₂₆ n := (floor_rpow_one_div n).symm

/-- `⌊n^{1/18}⌋ ≤ n`. -/
theorem paramD₂₆Nat_le (n : ℕ) : paramD₂₆Nat n ≤ n := Nat.findGreatest_le n

/-- `⌊n^{1/18}⌋ ≥ 1` for `n ≥ 1`. -/
theorem one_le_paramD₂₆Nat {n : ℕ} (hn : 1 ≤ n) : 1 ≤ paramD₂₆Nat n :=
  le_rootFloor (by norm_num) (by simpa using hn)




































/-- "and g := ⌈D^{0.0315}⌉". -/
theorem paramG₂₆Nat_eq {n : ℕ} (hn : 1 ≤ n) : paramG₂₆Nat (paramD₂₆ n) = paramG₂₆ n := by
  have hD : 1 ≤ paramD₂₆ n := paramD₂₆Nat_eq n ▸ one_le_paramD₂₆Nat hn
  rw [paramG₂₆Nat, paramG₂₆, ← ceil_rpow_inv (by norm_num) (Nat.one_le_pow _ _ hD)]
  congr 1
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num





/-- `⌈D^{0.0315}⌉ ≤ D`. -/
theorem paramG₂₆Nat_le {D : ℕ} (hD : 1 ≤ D) : paramG₂₆Nat D ≤ D :=
  rootCeil_le (by norm_num) (Nat.one_le_pow _ _ hD) (pow_le_pow_right₀ hD (by norm_num))

/-! ## The sizes of the instances of the proof of Theorem 17 -/










/-- `queryCapNat n D` is `⌊n²/√D⌋`: both are the greatest `c` with `c² D ≤ n⁴`. -/
theorem queryCapNat_eq (n : ℕ) {D : ℕ} (hD : 1 ≤ D) : queryCapNat n D = queryCap n D := by
  refine (eq_of_forall_le_iff fun c => ?_).symm
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr (Nat.cast_pos.2 hD)
  rw [queryCap, Nat.le_floor_iff (by positivity), le_div_iff₀ hs, queryCapNat, Nat.le_sqrt',
    Nat.le_div_iff_mul_le hD, ← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg D), ← pow_mul]
  exact_mod_cast Iff.rfl






















/-- `s = ⌊√D⌋` is the integer square root. -/
theorem sOf_eq_sqrt (D : ℕ) : sOf D = Nat.sqrt D := Real.nat_floor_real_sqrt_eq_nat_sqrt

/-- `pieceSizeNat D g` is the number `⌈s/g⌉` of vertices of a piece, where `s = ⌊√D⌋`. -/
theorem pieceSizeNat_eq (D : ℕ) {g : ℕ} (hg : 1 ≤ g) : pieceSizeNat D g = pieceSize D g := by
  rw [pieceSize, Nat.ceil_div_eq_ceilDiv _ hg, sOf_eq_sqrt]
  rfl

/-- `numPiecesNat n D g` is the number of pieces. -/
theorem numPiecesNat_eq (n D : ℕ) {g : ℕ} (hg : 1 ≤ g) (h : 1 ≤ pieceSize D g) :
    numPiecesNat n D g = numPieces n D g := by
  rw [numPiecesNat, pieceSizeNat_eq D hg, numPieces, Nat.ceil_div_eq_ceilDiv _ h]

/-- The number of chunks of a set of pairs in integer arithmetic. -/
theorem numChunks_eq {n : ℕ} (S : Finset (Fin n × Fin n)) {cap : ℕ} (hcap : 1 ≤ cap) :
    numChunks S cap = S.card ⌈/⌉ cap := by
  rw [numChunks, Nat.ceil_div_eq_ceilDiv _ hcap]

/-- A piece has at least one vertex, and the middle part `C_k × ℤ_p` of an instance has at most `D`
vertices. -/
theorem pieceSize_mul_le {D g p : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) (hp : p ∈ primesInRange D) :
    1 ≤ pieceSize D g ∧ pieceSize D g * p ≤ D := by
  rw [primesInRange_eq, List.mem_toFinset] at hp
  have hs : 4 ≤ Nat.sqrt D := Nat.le_sqrt'.2 (by omega)
  rw [← pieceSizeNat_eq D hg]
  refine ⟨(Nat.lt_ceilDiv_iff hg).2 (by omega), ?_⟩
  calc pieceSizeNat D g * p ≤ Nat.sqrt D * Nat.sqrt D :=
        Nat.mul_le_mul ((Nat.ceilDiv_le_iff hg).2 (Nat.le_mul_of_pos_right _ hg))
          (le_sqrt_of_mem_primesList hp)
    _ ≤ D := Nat.sqrt_le D

end ThreeSumApsp.Spec

end
end

section


/-!
# Cutting a set of pairs into chunks

Corollary 15 splits the query pairs "into sets of at most n²/√D query pairs", and the proof of
Theorem 17 cuts each set `W_ϱ` "into chunks of at most n²/√D query pairs".  In both, the chunk
number `j` of `S` holds the pairs of `S` whose rank in row-major order, divided by `cap`, is `j`.

* A chunk has at most `cap` pairs (`card_chunk_le`), because different pairs of `S` have different
  ranks (`rankIn_injOn`).
* The first `⌈|S|/cap⌉` chunks cover `S` (`biUnion_chunk`).
* In both uses `cap = ⌊n²/√D⌋`, which is at least 1 for `1 ≤ D ≤ n` (`one_le_queryCap`).
-/

public section

namespace ThreeSumApsp

variable {n : ℕ} {S : Finset (Fin n × Fin n)} {cap : ℕ}

/-! ### Ranks -/


























/-! ### Chunks -/

















/-! ### The size of the chunks in Corollary 15 and in Theorem 17 -/

/-- `√D ≤ D ≤ n`. -/
theorem sqrt_le_natCast {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : Real.sqrt D ≤ n :=
  calc Real.sqrt D ≤ Real.sqrt D * Real.sqrt D :=
        le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr (by exact_mod_cast hD))
    _ = D := Real.mul_self_sqrt (Nat.cast_nonneg D)
    _ ≤ n := by exact_mod_cast hDn

/-- The bound `⌊n²/√D⌋` on the size of a chunk is at least 1, because `√D ≤ n ≤ n²`. -/
theorem one_le_queryCap {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : 1 ≤ queryCap n D := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hD)), one_mul]
  exact (sqrt_le_natCast hD hDn).trans (le_self_pow₀ hn two_ne_zero)

end ThreeSumApsp

end
end

section


/-!
# The arithmetic behind the running-time claims of Section 3

Elementary inequalities that the deductions between running-time claims use silently.

* `⌈n^{1/3}⌉ ≥ 1` and `(log s + 1)^e ≥ 1`.
* Thin instances, `n ≥ D^18` (Theorem 5, Corollaries 15, 16 and 26): the overheads `n D`, `n² / √D`
  and `1` are at most `n² / D^a`, and so at most the bounds `n² log² D / D^{1/18}` and
  `n² / D^{0.063}`.
* The pieces into which Corollary 15 splits `W` have at most `n² / √D` query pairs (`splitCap_le`).
-/

public section

namespace ThreeSumApsp

/-! ## Two quantities that are at least 1 -/





/-- `(log s + 1)^e ≥ 1`. -/
theorem one_le_log_add_one_pow (s e : ℕ) : 1 ≤ (Real.log s + 1) ^ e :=
  one_le_pow₀ (le_add_of_nonneg_left (Real.log_natCast_nonneg s))

/-! ## Thin instances: `n ≥ D^18` -/

/-- `D^{1+a} ≤ n` for `a ≤ 17`. -/
theorem mul_rpow_le_of_pow_le {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    (D : ℝ) * (D : ℝ) ^ a ≤ n := by
  have hD1 : (1 : ℝ) ≤ D := Nat.one_le_cast.2 hD
  calc (D : ℝ) * (D : ℝ) ^ a = (D : ℝ) ^ (1 + a) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hD1), Real.rpow_one]
    _ ≤ (D : ℝ) ^ ((18 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by push_cast; linarith)
    _ = ((D ^ 18 : ℕ) : ℝ) := by rw [Real.rpow_natCast, Nat.cast_pow]
    _ ≤ n := Nat.cast_le.2 hDn

/-- Writing the matrices: `n D ≤ n² / D^a`. -/
theorem mul_le_sq_div_rpow {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    (n : ℝ) * (D : ℝ) ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.2 hD) a), mul_assoc, sq]
  exact mul_le_mul_of_nonneg_left (mul_rpow_le_of_pow_le hD hDn ha) n.cast_nonneg

/-- `1 ≤ n² / D^a`. -/
theorem one_le_sq_div_rpow {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    1 ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a :=
  (one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 ((Nat.one_le_pow _ _ hD).trans hDn))
    (Nat.one_le_cast.2 hD)).trans (mul_le_sq_div_rpow hD hDn ha)

/-- `n² / √D ≤ n² / D^a` for `a ≤ 1/2`. -/
theorem sq_div_sqrt_le_sq_div_rpow (n : ℕ) {D : ℕ} {a : ℝ} (hD : 1 ≤ D) (ha : a ≤ 1 / 2) :
    (n : ℝ) ^ 2 / Real.sqrt D ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a := by
  rw [Real.sqrt_eq_rpow]
  exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (Nat.cast_pos.2 hD) a)
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hD) ha)
































/-! ## The pieces of Corollary 15 -/

























/-- The second term of the bound of Corollaries 16 and 26 is at most the bound. -/
theorem sq_div_rpow_le_wantedBound (n D w : ℕ) :
    (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) ≤ wantedBound n D w :=
  le_add_of_nonneg_left (by positivity)

/-- `1 ≤ w D^{0.437} + n² / D^{0.063}`. -/
theorem one_le_wantedBound {n D : ℕ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (w : ℕ) :
    1 ≤ wantedBound n D w :=
  (one_le_sq_div_rpow hD hDn (by norm_num)).trans (sq_div_rpow_le_wantedBound n D w)

end ThreeSumApsp

end
end

section


/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## copy -/

namespace Copy







end Copy






















/-! ## fill -/

namespace Fill







end Fill








/-- **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else. -/
theorem fill_meets {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n :=
  .of_body hp (Ends.pass (fun _ => x) (fun i hi => by (((try have := Light.Std.space_le (by assumption)));
                                                        ((try have := Light.Std.const_le (by assumption)));
                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by ((try refine Light.SameOn.cell ?_);
                                                                                   (intro apspMacro_222980_0 apspMacro_222980_1);
                                                                                   (first
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_222980_2));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_222980_2 apspMacro_222980_0 (by omega)));
                                                                                                   (revert apspMacro_222980_2)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((simp [] at apspMacro_222980_1);
                                                                                         (((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_222980_3));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_222980_3 apspMacro_222980_0 (by omega)));
                                                                                                   (revert apspMacro_222980_3)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_222980_4));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_222980_4 apspMacro_222980_0 (by omega)));
                                                                                                   (revert apspMacro_222980_4)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (fail
                                                                                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                       its condition K x does not follow from the hypotheses."))))⟩
    hw hdst rfl rfl (hT := by first
                              |
                                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fillTime]);
                                  (first
                                    | omega
                                    | ((ring_nf); (omega))))
                              | omega
                              |
                                (simp [fillTime] <;>
                                    first
                                    | omega
                                    | ((ring_nf); (omega)))))

end Light

end
end

section


/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]





namespace PowTable









end PowTable

open PowTable




































































end Light

end
end

section


/-!
# Theorem 5 in the light language: sizes and places

The sizes of the tables and arrays of Theorem 5's program, and their places in the memory. No
program occurs here.

The program for Theorem 5 (the solver) and the data structure of Section 4 begin with the same
stage, the shared stage, which fills the shared block: a directory of 32 cells with the sizes and
the addresses of the areas (`dirList`), then the tables, then the encodings of all bands, then two
scratch areas. The solver has a private block behind it. The areas lie one after the other:
`Par.places` (the shared block) and `Par.places5` (the private block) say where every area begins
and ends. `Par.sizes` collects the inequalities between the sizes, each of which has a name of its
own.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/











namespace Par






















/-! ## The shared block, from its base address `b0` on -/











































end Par








/-! ## The private block of Theorem 5

The solver receives `N`, `D`, the number `w` of wanted positions, a bound `U` on the entries, the
addresses of `X`, `Y` (row by row), of the rows `WI` and the columns `WJ` of the wanted positions
and of the output, and as last argument the free pointer `fr`. All inputs and the output lie below
`fr`. The solver may write the output and the cells from `fr` on, and nothing is assumed about these
cells: a routine clears what it needs cleared. The shared block starts at `fr`, the private block
follows it. -/

namespace Par




























end Par

/-! ## The places and the sizes, as equations and inequalities -/

/-- The places of the shared block: each area begins where the one before it ends. -/
theorem Par.places (p : Par) (b0 : ℕ) :
    p.aDIR b0 = b0 ∧ p.aP3 b0 = b0 + 32 ∧ p.aP4 b0 = p.aP3 b0 + (p.L + 1)
      ∧ p.aP7 b0 = p.aP4 b0 + (p.L + 1)
      ∧ p.aP10 b0 = p.aP7 b0 + (p.L + 1) ∧ p.aPAS b0 = p.aP10 b0 + (p.L + 1)
      ∧ p.aPHI b0 = p.aPAS b0 + (p.L + 2) ∧ p.aPSI b0 = p.aPHI b0 + 70
      ∧ p.aMASK b0 = p.aPSI b0 + 70 ∧ p.aBAND b0 = p.aMASK b0 + p.KK * p.L
      ∧ p.aBLOCK b0 = p.aBAND b0 + p.N ∧ p.aDIG3 b0 = p.aBLOCK b0 + p.N
      ∧ p.aDIG4 b0 = p.aDIG3 b0 + p.N * p.Lo ∧ p.aENCA b0 = p.aDIG4 b0 + p.D * p.m
      ∧ p.aENCB b0 = p.aENCA b0 + p.nB * p.T ∧ p.aARR b0 = p.aENCB b0 + p.nB * p.T
      ∧ p.aZS b0 = p.aARR b0 + p.S7 ∧ p.sharedEnd b0 = p.aZS b0 + p.S7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Par
variable (p : Par)





























end Par











end Light.Sec2

end
end

section


/-!
# The alphabets of Schönhage's identity as digits

Section 2.2 names seven left variables, seven right variables, ten output variables and
ten terms; Section 2.3.1 indexes arrays by strings over these alphabets.  Here every
letter gets a digit, so that a string becomes a number (`codeStr`).

* The left variables `x₁ x₂ x₃ p₁₁ p₁₂ p₂₁ p₂₂` are the digits `0, …, 6`; likewise the right
  variables.
* The output variables `z₁₁ z₁₂ … z₃₃ z₀` are the digits `0, …, 9`, and the terms `P₁₁ … P₃₃ P₀`
  likewise, so that `z_ij` and `P_ij` have the same digit `3(i-1) + (j-1)`, and `z₀` and `P₀` have
  the digit 9.
* Left and right strings are numbers in base 7 (`codeL`, `codeR`), output strings, vertices and
  leaves in base 10 (`codeO`, `codeT`), strings of indices of outer variables in base 3
  (`codeOuter`) and of inner variables in base 4 (`codeInner`), always with level 1 most
  significant.
* Which output variables are inner, and which term contributes to which output variable (Section
  2.2), is read off the digits (`outVar_isInner_iff`, `contributes_iff`).
* The coefficients of the linear forms `φ_λ` and `ψ_λ` (Section 2.2) are written out as the rows of
  two 10 × 7 tables, `phiTable` and `psiTable`, which the programs store row after row
  (`phiFlat_spec`, `psiFlat_spec`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Digits -/





























































































/-! Applying one of the five bijections gives the digit. -/











/-! ## Codes of strings -/

























/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/




































/-! ## The structure of the identity, in digits -/

































/-! ## The coefficients of the linear forms, as tables -/





















/-- The table of the `φ_λ(s)` has 70 entries. -/
@[simp] theorem length_phiFlat : phiFlat.length = 70 := rfl

/-- The table of the `ψ_λ(t)` has 70 entries. -/
@[simp] theorem length_psiFlat : psiFlat.length = 70 := rfl













end ThreeSumApsp.Spec

end
end

section


/-!
# Arrays on strings as lists

Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u that is
a left string of length L."  In a program such an array is a list: an array on the strings of length
`n` over an alphabet of `b` letters is the list of its `b^n` entries in the order of the codes
(`arrStr`), so the entry at a string is the entry of the list at the code of the string
(`getD_arrStr`), and an entry of the list is 0 if the array is 0 at the string with that code
(`getD_arrStr_eq_zero`).  The arrays on left strings, on right strings and on leaves are the cases
`arrL`, `arrR` and `arrT`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)






/-- The list has `b^n` entries. -/
theorem length_arrStr : (arrStr e a).length = b ^ n := by
  simp [arrStr]



















end

/-! ## The three kinds of arrays of Section 2 that the programs store -/


















/-- The list of an array on the leaves has `10^n` entries. -/
theorem length_arrT {n : ℕ} (enc : Leaf n → ℤ) : (arrT enc).length = 10 ^ n :=
  length_arrStr termEquiv enc















end ThreeSumApsp.Spec

end
end

section


/-!
# The memory map of Theorem 5: what depends on which cells

SharedReady.dirs lists the cells of the directory that the solver reads. SharedTables are the tables
of the shared block without the directory and the encodings; they depend only on the cells between
these two (SharedTables.congr), and all that the shared stage leaves behind depends only on the
cells of the shared block, without the last of the 32 cells of the directory, which the shared stage
does not use (SharedReady.congr, SharedReady.of_agree).
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}























/-! ## Only the shared block matters -/

/-- The tables lie between the directory and the encodings: they are still there in a memory that
agrees on these cells. -/
theorem SharedTables.congr {p : Par} {b0 : ℕ} {μ μ' : ℕ → ℤ} (h : SharedTables p b0 μ)
    (he : ∀ x, p.aP3 b0 ≤ x → x < p.aENCA b0 → μ' x = μ x) : SharedTables p b0 μ' := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  have lphi := Spec.length_phiFlat
  have lpsi := Spec.length_psiFlat
  refine
    { p3 := h.p3.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p4 := h.p4.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p7 := h.p7.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p10 := h.p10.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      phi := h.phi.congr fun i hi => he _ (by omega) (by omega)
      psi := h.psi.congr fun i hi => he _ (by omega) (by omega)
      mask := fun s hs => (h.mask s hs).congr fun i hi => he _ (by omega) ?_
      band := fun I hI => (he _ (by omega) (by omega)).trans (h.band I hI)
      block := fun I hI => (he _ (by omega) (by omega)).trans (h.block I hI)
      dig3 := fun I hI => (h.dig3 I hI).congr fun i hi => he _ (by omega) ?_
      dig4 := fun x hx => (h.dig4 x hx).congr fun i hi => he _ (by omega) ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have := Nat.mul_add_lt_mul hI (show i < p.Lo by simpa [ThreeSumApsp.digitList] using hi)
    omega
  · have := Nat.mul_add_lt_mul hx (show i < p.m by simpa [ThreeSumApsp.digitList] using hi)
    omega

/-- What the shared stage leaves behind is kept by a memory that agrees on the cells of the shared
block, but for cell 31 of the directory, which the shared stage does not use. -/
theorem SharedReady.congr (h : SharedReady p hmL aX aY b0 X Y μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReady p hmL aX aY b0 X Y μ' := by
  have hplaces := p.places b0
  have tb : SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc : ∀ {a β i : ℕ}, p.aENCA b0 ≤ a → a + p.nB * p.T ≤ p.sharedEnd b0 → β < p.nB →
      i < p.T → μ' (a + β * p.T + i) = μ (a + β * p.T + i) := fun ha hend hβ hi => by
    have := Nat.mul_add_lt_mul hβ hi
    exact hag _ (by omega) (by omega) (by omega)
  refine
    { tb with
      dir := h.dir.congr fun i hi => ?_
      encA := fun β hβ => (h.encA β hβ).congr fun i hi =>
        henc le_rfl (by omega) hβ (by rwa [Spec.length_arrT] at hi)
      encB := fun β hβ => (h.encB β hβ).congr fun i hi =>
        henc (by omega) (by omega) hβ (by rwa [Spec.length_arrT] at hi) }
  simp only [dirList, List.length_map, List.length_cons, List.length_nil] at hi
  simp only [Par.aDIR]
  exact hag _ (by omega) (by omega) (by omega)








end Light.Sec2

end
end

section


/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/






















/-! ## Where the areas lie -/



















/-- The tables and the areas lie as Areas says. -/
theorem areas (p : Sec2.Par) (t b0 : ℕ) : Areas p t b0 := by
  have hplaces := p.places b0
  have hWD : aWD p b0 = p.sharedEnd b0 := rfl
  have hCUR : aCUR p b0 = aWD p b0 + p.L := rfl
  have hBOX : aBOX p b0 = aCUR p b0 + p.L := rfl
  have hSS : aSS p b0 = aBOX p b0 + p.L := rfl
  have hFP : aFP p b0 = aSS p b0 + p.m := rfl
  have hROOTS : aROOTS p b0 = aFP p b0 + 1 := rfl
  have hTR : aTR p b0 = aROOTS p b0 + p.nB * p.nB := rfl
  have hTOP : top p t b0 = aTR p b0 + trieCap p t + 1 := rfl
  constructor <;> omega










/-- The block holds more than its directory. -/
theorem base_add_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 + 32 < top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-- The block is not empty. -/
theorem base_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 < top p t b0 :=
  (Nat.le_add_right b0 32).trans_lt (base_add_lt_top p t b0)




/-- The scratch strings of a query lie in the block. -/
theorem scratch_in_block (p : Sec2.Par) (t b0 : ℕ) :
    b0 ≤ aWD p b0 ∧ aWD p b0 + (3 * p.L + p.m) ≤ top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-! ## The directory -/

namespace Dir




















end Dir

/-! ## The invariant -/



























section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- The invariant depends only on the cells from b0 on, without the scratch strings WD, CUR, BOX,
SS. -/
theorem DSReady.congr (h : DSReady p t hmL aX aY b0 X Y μ)
    (he : ∀ a, b0 ≤ a → Outside (aWD p b0) (3 * p.L + p.m) a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' := by
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  exact ⟨h.shared.congr fun a ha hlt _ => he a ha (by omega),
    by rw [he _ (by omega) (by omega)]; exact h.cellT,
    h.roots.congr fun i _ => he _ (by omega) (by omega),
    h.trie.congr fun i _ => he _ (by omega) (by omega)⟩







/-- The invariant of the data structure only depends on the cells from b0 on. -/
theorem dsReady_congr (h : DSReady p t hmL aX aY b0 X Y μ) (he : ∀ a, b0 ≤ a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' :=
  h.congr fun a ha _ => he a ha

end












/-! ## The two routines that know the map -/




































end Light.Sec4

end
end

section


/-!
# Section 4.4: the steps of the proof of Corollary 26 that hold for all parameters

The proof of Corollary 31 begins: "We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t :=
⌈θm⌉". This file has the parts of the proof of Corollary 26 that mention neither `L = 21m` nor
`t = ⌈m/9⌉`, under the headings of that proof. Both corollaries use them.

* Setting up. The inner dimension is padded to `D = 4^m` with `m = ⌈log_4 D⌉`
  (`Corollary26.setting_up`). This changes no entry of the product (`Corollary26.padding`), and it
  changes the bounds by a constant factor (`padded_le`). The switching order `t = ⌈θm⌉` is
  `switchOf θ m`, and `t ≤ m` (`switchOf_le`).
* Queries. `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` for every `x ≥ 1/9` (`sum_alpha_le`), and for
  `x = (1-θ)/θ` the right-hand side at `t = θm` is `D^q` (`rpow_mul_pow_eq_D_rpow_qOf`).
* Encodings. Inequality (10), whose left-hand side is `lhs10 L m γ`, bounds the last term of (8) and
  gives the hypothesis `N ≥ √K N₀` of Theorem 30 (`Equation10.last_term`, `Equation10.tile_fits`).
* Conclusion. The expression (8) from a bound on its first term and (10)
  (`dominated_cost8_of_eq_10`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given inner dimension, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/
















/-- Proof of Corollary 26, "Setting up": "pad the inner dimension to 4^m < 4D with zero columns of X
and zero rows of Y. This changes no entry of XY". -/
theorem Corollary26.padding {N D₀ : ℕ} (D' : ℕ) (hD : D₀ ≤ D') (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) :
    padInnerCols D' X * padInnerRows D' Y = X * Y := by
  ext I J
  rw [Matrix.mul_apply, Matrix.mul_apply]
  -- The sum over the `D'` columns has the `D₀` terms of `XY`, and zeros at the added columns.
  refine (Fintype.sum_of_injective (Fin.castLE hD) (Fin.castLE_injective hD) _ _
    (fun k hk => ?_) fun k => ?_).symm
  · have hk' : ¬ (k : ℕ) < D₀ := fun h => hk ⟨⟨k, h⟩, rfl⟩
    simp only [padInnerCols, dif_neg hk', zero_mul]
  · simp only [padInnerCols, padInnerRows, Fin.val_castLE, k.isLt, dite_true, Fin.eta]











































































/-! ### Queries -/









































/-! ### Encodings -/






























/-! ### Conclusion -/























end ThreeSumApsp

end
end

section


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters and map -/









/-! ## The query -/

namespace Query31










end Query31








theorem abs_padInnerCols_le {N D₀ D' : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {U : ℤ}
    (h : ∀ i j, |X i j| ≤ U) (hU : 0 ≤ U) (i : Fin N) (j : Fin D') :
    |padInnerCols D' X i j| ≤ U := by
  unfold padInnerCols
  split_ifs
  · exact h _ _
  · simpa using hU

theorem abs_padInnerRows_le {N D₀ D' : ℕ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ}
    (h : ∀ i j, |Y i j| ≤ U) (hU : 0 ≤ U) (i : Fin D') (j : Fin N) :
    |padInnerRows D' Y i j| ≤ U := by
  unfold padInnerRows
  split_ifs
  · exact h _ _
  · simpa using hU

theorem le_D_logFour (D₀ : ℕ) : D₀ ≤ D (logFour D₀) := Nat.le_pow_clog (by norm_num) D₀
















end Light.Sec4

end
end

section


/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters -/
















variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}















/-- t ≤ m. -/
theorem RatParams.t_le (G : RatParams) (m : ℕ) : G.t m ≤ m := by
  unfold RatParams.t
  have hq := G.hq
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have h1 : 10 * G.p * m ≤ 9 * G.q * m := Nat.mul_le_mul_right _ G.hθ.le
  have h2 : G.p * m ≤ G.q * m := by
    have e1 : 10 * G.p * m = 10 * (G.p * m) := by ring
    have e2 : 9 * G.q * m = 9 * (G.q * m) := by ring
    omega
  omega





































/-- Below the threshold a structure has three cells. -/
theorem structEnd_small (h : logFour D₀ < G.m₀) (N fr : ℕ) : structEnd G N D₀ fr = fr + 3 :=
  if_pos h

/-- For m ≥ m₀ a structure ends with the block of Theorem 30. -/
theorem structEnd_large (h : G.m₀ ≤ logFour D₀) (N fr : ℕ) :
    structEnd G N D₀ fr = G.blockEnd N D₀ fr :=
  if_neg (not_lt.2 h)

/-- The block of Theorem 30 begins after the first three cells. -/
theorem add_three_le_blockAt (N D₀ fr : ℕ) : fr + 3 ≤ blockAt N D₀ fr := by
  unfold blockAt
  omega

/-- The block of Theorem 30 is not empty. -/
theorem RatParams.blockAt_lt_blockEnd (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr < G.blockEnd N D₀ fr :=
  base_lt_top _ _ _

/-- The cells that a query of Theorem 30 writes lie in the block. -/
theorem RatParams.scratch_in_block (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr ≤ aWD (parOf G N D₀) (blockAt N D₀ fr) ∧
      aWD (parOf G N D₀) (blockAt N D₀ fr) + (3 * (parOf G N D₀).L + (parOf G N D₀).m)
        ≤ G.blockEnd N D₀ fr :=
  Sec4.scratch_in_block _ _ _

/-- A structure has at least three cells. -/
theorem add_three_le_structEnd (G : RatParams) (N D₀ fr : ℕ) : fr + 3 ≤ structEnd G N D₀ fr := by
  have hblock := add_three_le_blockAt N D₀ fr
  have hend := G.blockAt_lt_blockEnd N D₀ fr
  by_cases h : logFour D₀ < G.m₀
  · rw [structEnd_small h]
  · rw [structEnd_large (not_lt.1 h)]
    omega
























































theorem Input31.zero_le_U (h : Input31 lim G X Y aX aY fr U) : 0 ≤ U :=
  le_trans (abs_nonneg _) (h.absX ⟨0, h.one_le_N⟩ ⟨0, h.one_le_D⟩)

/-! ## The query: the text is query31Body -/
















/-- A query to the data structure of Theorem 30 changes only cells of its block, so that the
structure stays ready. -/
theorem Ready31.of_query (h : Ready31 G X Y aX aY fr μ) (bX : aX + N * D₀ ≤ fr)
    (bY : aY + D₀ * N ≤ fr) (hm : G.m₀ ≤ logFour D₀) (hkept : ∀ a < blockAt N D₀ fr, μ' a = μ a)
    (hDS : Built31 G X Y fr μ') : Ready31 G X Y aX aY fr μ' := by
  have hb0 := add_three_le_blockAt N D₀ fr
  obtain ⟨hflag, hbase, -⟩ := h.large hm
  exact ⟨h.matX.congr_below hkept (by omega), h.matY.congr_below hkept (by omega),
    fun hm' => absurd hm (by omega),
    fun _ => ⟨(hkept _ (by omega)).trans hflag, (hkept _ (by omega)).trans hbase, hDS⟩⟩

/-- query31 reads the flag and calls the query of Theorem 30 if it is 1 and the inner product
otherwise; it returns the entry (XY)[I, J] and keeps the structure ready. -/
theorem query31_meets (G : RatParams) (hP : P[Proc.query31]? = some query31Body)
    (hq : QueryAtSpec lim P) (hip : IpAtSpec lim P) : QuerySpec31 lim P G := by
  intro N D₀ aX aY fr X Y U μ I J hin hR
  have hlim := hin.lim
  have bX := hin.belowX
  have bY := hin.belowY
  refine fun d hd => ⟨query31Body, hP, ?_⟩
  have hw := hlim.std.space_le
  have h100 := hlim.std.const_le
  have hU0 := hin.zero_le_U
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hsp := hlim.space
  unfold query31Body
  -- if mem[fr] = 1
  refine Ends.iteLast (fun hflag => ?_) (fun hflag => ?_) (hT := by simp [tQuery31])
  · -- the data structure has been built: return queryAt(I, J, mem[fr + 1])
    have hlarge : G.m₀ ≤ logFour D₀ := by
      by_contra hc
      have hzero := hR.small (by omega)
      have hone : μ fr = 1 := by simpa using hflag
      omega
    obtain ⟨-, hbase, hDS⟩ := hR.large hlarge
    have haddr : ((fr : ℤ) + 1).toNat = fr + 1 := by omega
    refine Ends.callTo
      (hq (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
        (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ I J (G.t_le _) (hlim.large hlarge)
        (abs_padInnerCols_le hin.absX hU0) (abs_padInnerRows_le hin.absY hU0) hDS _ (by omega)) ?_
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hbase] <;> omega)))
      (hT := by simp [tQuery31, if_neg (not_lt.mpr hlarge), parOf]; omega)
    rintro r μ' ⟨hr, hDS', hout⟩
    have hscratch := G.scratch_in_block N D₀ fr
    have hb0 := add_three_le_blockAt N D₀ fr
    have htop := structEnd_large hlarge N fr
    refine ⟨?_, hR.of_query bX bY hlarge (fun a ha => hout a (by omega)) hDS',
      fun a ha => hout a (by omega)⟩
    -- padding changes no entry of the product
    exact hr.trans (congrFun (congrFun
      (Corollary26.padding (D (logFour D₀)) (le_D_logFour D₀) X Y) I) J)
  · -- m is below the threshold: return the inner product ipAt(I, J, N, D, aX, aY)
    have hsmall : logFour D₀ < G.m₀ := by
      by_contra hc
      exact hflag (by simpa using (hR.large (by omega)).1)
    refine Ends.callTo (hip N D₀ aX aY X Y U μ I J hin.one_le_D hR.matX hR.matY hin.absX hin.absY
      (by omega) (by omega) hlim.ip _ (by omega)) ?_
      (hT := by simp [tQuery31, if_pos hsmall]; omega)
    rintro r μ' ⟨hr, rfl⟩
    exact ⟨hr, hR, .refl⟩

/-! ## The preprocessing: text and interface -/









namespace Pre31



















end Pre31















































end Light.Sec4

end
end

section


/-!
# An entry of the product as an inner product

Proof of Corollary 26: "(For m < 60, D is bounded by a constant, and the corollary holds
trivially.)"; proof of Corollary 31: "for smaller m the corollary again holds trivially". In the
programs a query then computes an inner product, of a bounded number D of summands. The routine adds
the D products X[I, s] Y[s, J]. `ipPart` is the sum of the first s of them, with its recursion
(`ipPart_succ`), its bound (`abs_ipPart_le`) and its last value (`ipPart_full`); `ipAt_meets` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace IpAt















end IpAt











section
variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)




theorem ipPart_full : ipPart X Y I J D₀ = (X * Y) I J := by
  rw [Matrix.mul_apply, ipPart, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp

theorem ipPart_succ {s : ℕ} (hs : s < D₀) :
    ipPart X Y I J (s + 1) = ipPart X Y I J s + X I ⟨s, hs⟩ * Y ⟨s, hs⟩ J := by
  rw [ipPart, Finset.sum_range_succ, dif_pos hs]
  rfl

variable {X Y}

theorem abs_mul_entry_le {U : ℤ} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (s : Fin D₀) :
    |X I s * Y s J| ≤ U * U := by
  rw [abs_mul]
  exact mul_le_mul (hX _ _) (hY _ _) (abs_nonneg _) (le_trans (abs_nonneg _) (hX I s))

theorem abs_ipPart_le {U : ℤ} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) :
    ∀ s ≤ D₀, |ipPart X Y I J s| ≤ s * (U * U)
  | 0, _ => by simp [ipPart]
  | s + 1, hs => by
    rw [ipPart_succ X Y I J hs]
    refine (abs_add_le _ _).trans ?_
    have := abs_ipPart_le hX hY s (by omega)
    have := abs_mul_entry_le I J hX hY ⟨s, hs⟩
    push_cast
    linarith

end

theorem ipAt_meets {lim : Limits} {P : Program} (hP : P[Proc.ipAt]? = some ipAtBody)
    (hstd : Std lim) : IpAtSpec lim P := by
  intro N D₀ aX aY X Y U μ I J hD hmX hmY hX hY sX sY hU
  refine fun d _ => ⟨ipAtBody, hP, ?_⟩
  have hw := hstd.space_le
  have h100 := hstd.const_le
  have hrow : (I : ℕ) * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul I.isLt le_rfl
  have hcol : (J : ℕ) < N := J.isLt
  have hN : N ≤ D₀ * N := Nat.le_mul_of_pos_left _ hD
  -- every partial sum and every product fits in a word
  have hfits : ∀ s ≤ D₀, |ipPart X Y I J s| ≤ lim.word := fun s hs =>
    (abs_ipPart_le I J hX hY s hs).trans (le_trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hs)
        (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY ⟨0, hD⟩))) hU)
  have hprod : ∀ s : Fin D₀, |X I s * Y s J| ≤ lim.word := fun s =>
    (abs_mul_entry_le I J hX hY s).trans (le_trans (le_mul_of_one_le_left
      (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY s)) (by exact_mod_cast hD)) hU)
  unfold ipAtBody tIpAt
  -- s := 0 ; sum := 0 ; row := aX + I * D ; col := aY + J
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aX + (I : ℕ) * D₀ : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (aY + (J : ℕ) : ℕ)
            -- while s < D: sum := sum + mem[row + s] * mem[col + s * N] ; s := s + 1
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while s < D: sum := sum + mem[row + s] * mem[col + s * N] ; s := s + 1
  refine Ends.next _ (Ends.whileBlock (fun s σ => σ = ⟨frame [(I : ℕ), (J : ℕ), N, D₀, aX, aY, s,
      ipPart X Y I J s, ((aX + (I : ℕ) * D₀ : ℕ) : ℤ), ((aY + (J : ℕ) : ℕ) : ℤ)], μ⟩) D₀
    (by simp [ipPart]) ?round ?done (hT := le_rfl))
  case round =>
    rintro s _ hs rfl
    have hcell : s * N + N ≤ D₀ * N := Nat.mul_add_le_mul hs le_rfl
    have hx : μ (aX + (I : ℕ) * D₀ + s) = X I ⟨s, hs⟩ := hmX I ⟨s, hs⟩
    have hy : μ (aY + (J : ℕ) + s * N) = Y ⟨s, hs⟩ J := by
      rw [← hmY ⟨s, hs⟩ J]
      congr 1
      change aY + (J : ℕ) + s * N = aY + s * N + (J : ℕ)
      omega
    have haddrX : ((aX : ℤ) + (I : ℕ) * D₀ + s).toNat = aX + (I : ℕ) * D₀ + s := by
      rw [← Int.toNat_natCast (aX + (I : ℕ) * D₀ + s)]; push_cast; rfl
    have haddrY : ((aY : ℤ) + (J : ℕ) + s * N).toNat = aY + (J : ℕ) + s * N := by
      rw [← Int.toNat_natCast (aY + (J : ℕ) + s * N)]; push_cast; rfl
    have hsum := abs_le.1 (hfits (s + 1) hs)
    have hxy := abs_le.1 (hprod ⟨s, hs⟩)
    rw [ipPart_succ X Y I J hs] at hsum ⊢
    generalize ipPart X Y I J s = S at hsum ⊢
    generalize X I ⟨s, hs⟩ = x at hx hsum hxy ⊢
    generalize Y ⟨s, hs⟩ J = y at hy hsum hxy ⊢
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, by (((try have := Light.Std.space_le (by assumption)));
                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, haddrX, haddrY, hx, hy] <;>
                                                                                                      omega)),
      by simp [update_frame_setLocal, haddrX, haddrY, hx, hy]⟩
  case done =>
    rintro _ rfl
    -- return sum
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp, Ends.setTo (ipPart X Y I J D₀) ⟨ipPart_full X Y I J, rfl⟩⟩

end Light.Sec4

end
end

section


/-!
# Bounds on finite sums and products

General facts about sums and products over a finite set in an ordered ring or field.

* A sum of `s.card` numbers of absolute value at most `A` is at most `s.card * A` in absolute value
  (`Finset.abs_sum_le_card_mul`), also with coefficients of absolute value at most `1`
  (`Finset.abs_sum_mul_le`).
* A product of numbers of absolute value at most `1` has absolute value at most `1`
  (`Finset.abs_prod_le_one`). For integers, `Int.abs_le_one_iff` says that these are `0`, `1`, `-1`.
* A sum over the indices below `m * n` is a double sum (`Finset.sum_range_mul`).
* A part of a geometric series with ratio `0 < x < 1` is less than the whole series from its first
  term on (`geom_sum_Ico_lt_of_lt_one`).
-/

public section

namespace Finset

variable {ι R : Type*}



















/-- A sum over the indices below `m * n`, row by row: the index `a * n + b` has row `a` and column
`b`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (m n : ℕ) (F : ℕ → M) :
    ∑ i ∈ range (m * n), F i = ∑ a ∈ range m, ∑ b ∈ range n, F (a * n + b) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

end Finset













end
end

section


/-!
# Theorem 30, the offline form (9): preprocess, then one query for each wanted position

Theorem 30: "In particular, for every set W of positions of an N × N matrix, the entries (XY)[I, J],
(I, J) ∈ W, can be computed deterministically in time
O(L |W| ∑_{d=0}^{t} α_d + L m ρ^t/(1 - ρ) N² + N · 10^L/(√K N₀))."

wantedCore is relocatable: it receives the addresses of the matrices, of the two lists of indices,
of the output and of the free block. It meets its specification `WantedCoreSpec` in every program
that meets those of preCore and queryAt (`wantedCore_spec`): one call of preCore, then a loop whose
round asks one query and stores the answer (`wantedAsk_ends`), with the invariant `Answered`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One query for each wanted position: the invariant -/

section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}










/-- One round: a query that leaves the cells in Quiet alone, among them the output and the cells in
Kept, and the store of its answer behind the answers that are there. -/
theorem Answered.step (h : Answered Ready Kept out ans μ i μ') (hi : i < ans.length)
    (hquery : SameOn Quiet μ' μ'') (hout : ∀ j < i, Quiet (out + j)) (hkept : ∀ a, Kept a → Quiet a)
    (hready : Ready (Function.update μ'' (out + i) ans[i])) :
    Answered Ready Kept out ans μ (i + 1) (Function.update μ'' (out + i) ans[i]) := by
  have hlen : (ans.take i).length = i := by rw [List.length_take, Nat.min_eq_left hi.le]
  refine ⟨hready, ?_, ?_⟩
  · have hsnoc := (h.answers.of_sameOn hquery fun j hj => hout j (hlen ▸ hj)).snoc ans[i]
    rw [hlen] at hsnoc
    rwa [List.take_add_one, List.getElem?_eq_getElem hi]
  · exact ((h.same.mono fun a ha => ⟨by have := ha.1; omega, ha.2⟩).then hquery
      fun a ha => ⟨ha, hkept a ha.2⟩).write (by omega) _

/-- A cell of a list that stood in the memory at the start, away from the answers and in Kept, still
holds its entry. -/
theorem Answered.read (h : Answered Ready Kept out ans μ i μ') {a j : ℕ} {l : List ℤ}
    (hl : Seg μ a l) (hj : j < l.length) (hoff : Outside out i (a + j)) (hkept : Kept (a + j)) :
    μ' (a + j) = l[j] :=
  (h.same _ ⟨hoff, hkept⟩).trans (hl.get hj)

/-- After the last round all answers are in place. -/
theorem Answered.all (h : Answered Ready Kept out ans μ ans.length μ') : Seg μ' out ans := by
  simpa using h.answers

end

/-! ## The routine -/



namespace WantedCore




















end WantedCore


















section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}


















end






















































































end Light.Sec4

end
end

section


/-!
# Section 4.4, the offline form: preprocess, then one query for each wanted position

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". Its proof: "The
bound for a set W follows by asking |W| queries." Proof of Theorem 25: "ask one query for each
position of W"; for Corollary 32 the paper uses "the same argument", "With Corollary 31 in place of
Theorem 24".

offline32(N, D, w, U, x, y, wi, wj, out, fr) preprocesses the matrices at x and y (pre31, which uses
the cells from the free pointer fr on) and then asks one query for each of the w positions, whose
rows are at wi and whose columns are at wj; the answers go to out. The arguments are those of the
task `thinTask`. The text `offline32Body`, with the round `offlineAsk32` of its loop, serves all
rational parameters c and θ: they are in the body of the procedure pre31 (`pre31Body`).

A round adds one answer (`offlineAsk32_ends`), with the invariant `Answered` that the offline form
of Theorem 30 uses too, and the routine meets its specification `OfflineSpec32` for all parameters G
(`offline32_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The text -/






namespace Offline32

















end Offline32















/-! ## What it does -/

/-- What a query needs depends only on the cells of X, of Y, and on the cells from fr on. -/
theorem ready31_congr (h : Ready31 G X Y aX aY fr μ)
    (hX : ∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a)
    (hY : ∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) (hfr : ∀ a, fr ≤ a → μ' a = μ a) :
    Ready31 G X Y aX aY fr μ' := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun hs => ?_, fun hl => ?_⟩
  · rw [hX _ (by omega) ?_]
    · exact h.matX i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl D₀)
      have := j.isLt
      omega
  · rw [hY _ (by omega) ?_]
    · exact h.matY i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl N)
      have := j.isLt
      omega
  · rw [hfr _ le_rfl]
    exact h.small hs
  · obtain ⟨h1, h2, h3⟩ := h.large hl
    refine ⟨by rw [hfr _ le_rfl]; exact h1, by rw [hfr _ (by omega)]; exact h2,
      dsReady_congr h3 fun a ha => hfr a ?_⟩
    unfold blockAt at ha
    omega





































/-- The specification holds for the program with more procedures appended. -/
theorem OfflineSpec32.append {c : ℕ} (h : OfflineSpec32 lim P c G) (R : Program) :
    OfflineSpec32 lim (P ++ R) c G :=
  fun N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd =>
    (h N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd).append R

/-- **One round**: the answer for position i joins the answers that are there. -/
theorem offlineAsk32_ends (hq : QuerySpec31 lim P G) {aI aJ out d : ℕ}
    {u : ℤ} {WI WJ : List ℕ} (hg : Input31 lim G X Y aX aY fr U)
    (hin : OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ) (hd : d + 4 ≤ lim.depth) {i : ℕ}
    (hi : i < WI.length) (r : ℤ)
    (hinv : Answered (Ready31 G X Y aX aY fr) (· < fr) out
      ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ') :
    Ends lim P d offlineAsk32 ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩
      (tQuery31 G D₀ + 20) fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r'], μ''⟩ ∧
        Answered (Ready31 G X Y aX aY fr) (· < fr) out
          ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ (i + 1) μ'' := by
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hrows := hin.rows_le
  have hcols := hin.cols_le
  have hout := hin.out_le
  have hiJ : i < WJ.length := by omega
  have hIN : WI[i] < N := hin.rows_lt _ (List.getElem_mem hi)
  have hJN : WJ[i] < N := hin.cols_lt _ (List.getElem_mem hiJ)
  -- the two indices are still in place
  have hrow : μ' (aI + i) = ((WI[i] : ℕ) : ℤ) :=
    (hinv.read hin.rows (j := i) (by simpa using hi)
      (by rcases hin.out_rows with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  have hcol : μ' (aJ + i) = ((WJ[i] : ℕ) : ℤ) :=
    (hinv.read hin.cols (j := i) (by simpa using hiJ)
      (by rcases hin.out_cols with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  -- Res := query31(mem[Rows + Pos], mem[Cols + Pos], N, D, x, y, fr)
  refine Ends.callToThen (hq N D₀ aX aY fr X Y U μ' ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩ hg hinv.ready _
    (by omega)) ?_
    (ha := by (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hrow, hcol] <;> omega)))
  rintro _ μ₂ ⟨rfl, hready, hquery⟩
  -- mem[Out + Pos] := Res
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.storeToThen (out + i) ((X * Y) ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩) ?_ ?_
          ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hstep := hinv.step (by simpa [hlen] using hi) hquery (fun j hj => Or.inl (by omega))
    (fun a ha => Or.inl (by omega)) (ready31_congr hready
      (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matX with h | h <;> omega) _ _)
      (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matY with h | h <;> omega) _ _)
      fun a ha => Function.update_of_ne (by omega) _ _)
  rw [List.getElem_map, List.getElem_zip, entryN, dif_pos ⟨hIN, hJN⟩] at hstep
  exact ⟨_, _, rfl, hstep⟩

theorem offline32_meets {c : ℕ} (hP : P[Proc.offline32]? = some offline32Body)
    (hpre : PreSpec31 lim P c G) (hq : QuerySpec31 lim P G) : OfflineSpec32 lim P c G := by
  intro N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin
  refine fun d hd => ⟨offline32Body, hP, ?_⟩
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hout := hin.out_le
  have hzip : (WI.zip WJ).length = WI.length := by simp [hlen]
  -- Res := pre31(N, D, x, y, fr)
  refine Ends.callToThen (hpre N D₀ aX aY fr X Y U μ hg hin.matX hin.matY _ (by omega)) ?_
    (hT := by simp [tOffline32]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  -- for Pos < Count: offlineAsk32
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩ ∧
      Answered (Ready31 G X Y aX aY fr) (· < fr) out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ
        i μ')
    WI.length (tQuery31 G D₀ + 20) ?start ?round ?done ?bound
    (hT := by simp [tOffline32]; ring_nf; omega)
  case start =>
    exact ⟨r, μ₁, by rw [update_frame_setLocal]; rfl, hready, Seg.nil,
      SameOn.mono hblock fun a ha => Or.inl ha.2⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨r, μ', rfl, hinv⟩
    rw [← hzip, ← List.length_map (as := WI.zip WJ) fun q => entryN X Y q.1 q.2] at hinv
    refine ⟨hinv.all, fun a ha hoff => hinv.same a ⟨?_, ha⟩⟩
    simpa [hlen] using hoff
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hinv⟩
    refine (offlineAsk32_ends hq hg hin (by omega) hi r hinv).mono le_rfl ?_
    rintro _ ⟨r', μ'', rfl, hinv'⟩
    exact ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl, hinv'⟩

end Light.Sec4

end
end

section


/-!
# The integer square root by counting up

sqrt(K) returns ⌊√K⌋ within `sqrtTime K` steps (`sqrt_meets`), by running through the squares 1, 4,
9, …: after (k + 1)² comes (k + 1)² + 2k + 3.  It does not touch the memory.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sqrt







end Sqrt














/-- **sqrt(K)** returns ⌊√K⌋ and leaves the memory as it is. -/
theorem sqrt_meets {p K : ℕ} (hp : P[p]? = some sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [K] μ (sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by
  have hle : Nat.sqrt K * Nat.sqrt K ≤ K := Nat.sqrt_le K
  have hlt : K < (Nat.sqrt K + 1) * (Nat.sqrt K + 1) := Nat.lt_succ_sqrt K
  have hself : Nat.sqrt K ≤ K := Nat.sqrt_le_self K
  refine .of_body hp ?_
  unfold sqrtBody sqrtTime
  -- k := 0; sq := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          1
            -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [K, i, ((i + 1) * (i + 1) : ℕ)], μ⟩) (Nat.sqrt K) (by simp) ?round ?done
    le_rfl)
  case round =>
    rintro i _ hi rfl
    have hsq : (i + 1) * (i + 1) ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul (by omega) (by omega)
    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]
    generalize (i + 1) * (i + 1) = q at hsq
    -- The test is safe and holds.  sq := sq + 2 k + 3; k := k + 1 is safe and leads to the next
    -- state.
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize (Nat.sqrt K + 1) * (Nat.sqrt K + 1) = q at hlt
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- the result is k
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (Nat.sqrt K) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    exact ⟨rfl, rfl⟩

end Light

end
end

section


/-!
# The pure side of counting sort

`N` items `0, …, N - 1` have keys `kf 0, …, kf (N - 1)`.  A stable sort by key puts item `j` at the
place `sortPos kf N j`: the number of items with a smaller key plus the number of earlier items with
the same key.

This is a bijection of `{0, …, N - 1}` (`eq_of_sortPos_eq`, `exists_sortPos_eq`) that is increasing
for the order "smaller key, or same key and earlier" (`sortPos_lt_sortPos_iff`).
-/

@[expose] public section

namespace ThreeSumApsp










section
variable (kf : ℕ → ℕ)





@[simp] theorem cntLt_zero_left (j : ℕ) : cntLt kf 0 j = 0 := by simp [cntLt]

/-- One more item: it is counted if its key is `t`. -/
theorem cntEq_succ (t j : ℕ) : cntEq kf t (j + 1) = cntEq kf t j + if kf j = t then 1 else 0 :=
  Nat.count_succ _ _

/-- One more item: it is counted if its key is below `t`. -/
theorem cntLt_succ_right (t j : ℕ) :
    cntLt kf t (j + 1) = cntLt kf t j + if kf j < t then 1 else 0 := Nat.count_succ _ _

/-- Keys below `t + 1` are keys below `t` or equal to `t`. -/
theorem cntLt_succ_left (t j : ℕ) : cntLt kf (t + 1) j = cntLt kf t j + cntEq kf t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [cntLt_succ_right, cntLt_succ_right, cntEq_succ, ih]
    split_ifs <;> omega

/-- A larger bound counts more keys. -/
theorem cntLt_mono_left {s t : ℕ} (h : s ≤ t) (j : ℕ) : cntLt kf s j ≤ cntLt kf t j :=
  Nat.count_mono_left fun _ _ hlt => hlt.trans_le h

/-- At most all items are counted. -/
theorem cntLt_le (t j : ℕ) : cntLt kf t j ≤ j := Nat.count_le _

end

variable {kf : ℕ → ℕ} {N K : ℕ}







/-- If all keys are below `K`, all items are counted. -/
theorem cntLt_of_forall_lt (h : ∀ i < N, kf i < K) : cntLt kf K N = N :=
  Nat.count_iff_forall.mpr h

/-- Item `j` is itself one of the `N` items with its key. -/
theorem cntEq_lt_of_lt {j : ℕ} (hj : j < N) : cntEq kf (kf j) j < cntEq kf (kf j) N :=
  Nat.count_strict_mono (p := fun i => kf i = kf j) rfl hj

/-- The place of an item lies before the places of the larger keys. -/
theorem sortPos_lt_cntLt_succ {j : ℕ} (hj : j < N) : sortPos kf N j < cntLt kf (kf j + 1) N := by
  rw [cntLt_succ_left, sortPos]
  exact Nat.add_lt_add_left (cntEq_lt_of_lt hj) _

/-- The places are below `N`. -/
theorem sortPos_lt (kf : ℕ → ℕ) {j : ℕ} (hj : j < N) : sortPos kf N j < N :=
  calc sortPos kf N j < cntLt kf (kf j + 1) N := sortPos_lt_cntLt_succ hj
    _ ≤ N := cntLt_le ..

/-- A smaller key comes first; among equal keys the earlier item comes first. -/
theorem sortPos_lt_sortPos {i j : ℕ} (hi : i < N) (h : kf i < kf j ∨ (kf i = kf j ∧ i < j)) :
    sortPos kf N i < sortPos kf N j := by
  rcases h with hlt | ⟨heq, hij⟩
  · calc sortPos kf N i < cntLt kf (kf i + 1) N := sortPos_lt_cntLt_succ hi
      _ ≤ cntLt kf (kf j) N := cntLt_mono_left kf hlt N
      _ ≤ sortPos kf N j := Nat.le_add_right ..
  · rw [sortPos, sortPos, heq]
    exact Nat.add_lt_add_left (heq ▸ cntEq_lt_of_lt hij) _

/-- The order of the places is the order "smaller key, or same key and earlier". -/
theorem sortPos_lt_sortPos_iff {i j : ℕ} (hi : i < N) (hj : j < N) :
    sortPos kf N i < sortPos kf N j ↔ kf i < kf j ∨ (kf i = kf j ∧ i < j) := by
  refine ⟨fun h => ?_, sortPos_lt_sortPos hi⟩
  by_contra hc
  rcases (by omega : i = j ∨ kf j < kf i ∨ (kf j = kf i ∧ j < i)) with rfl | h'
  · omega
  · have := sortPos_lt_sortPos hj h'
    omega

/-- Different items get different places. -/
theorem eq_of_sortPos_eq {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : sortPos kf N i = sortPos kf N j) : i = j := by
  have hij := sortPos_lt_sortPos_iff (kf := kf) hi hj
  have hji := sortPos_lt_sortPos_iff (kf := kf) hj hi
  omega

/-- Every place is taken. -/
theorem exists_sortPos_eq (kf : ℕ → ℕ) {q : ℕ} (hq : q < N) : ∃ j < N, sortPos kf N j = q := by
  have hsurj := Finset.surjOn_of_injOn_of_card_le (s := Finset.range N) (t := Finset.range N)
    (sortPos kf N) (fun j hj => by simpa using sortPos_lt kf (by simpa using hj))
    (fun i hi j hj => eq_of_sortPos_eq (by simpa using hi) (by simpa using hj)) le_rfl
  simpa using hsurj (by simpa using hq)

end ThreeSumApsp

end
end

section


/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/

@[expose] public section

namespace Light.Sec4

































































/-- A query at a given place of the memory, for all limits. -/
theorem queryAtSpec_all {P : Program} (h : Has40 P)
    (h55 : P[Proc.queryAt]? = some queryAtBody) : ∀ lim, QueryAtSpec lim P :=
  fun _ p t hmL aX aY b0 X Y U μ I J ht hlim =>
    queryAt_spec h55 (specs40 h hlim.std).outDigits
      (specs40 h hlim.std).queryCore p t hmL aX aY b0 X Y U μ I J ht hlim

/-- A list that has forty procedures, then the routines of Section 4, then anything, holds them at
their numbers. -/
theorem has40_of_append {A B : List Stmt} (hA : A.length = 40) : Has40 (A ++ procs40 ++ B) := by
  intro i hi
  have hlen : procs40.length = 14 := rfl
  rw [List.append_assoc, List.getElem?_append_right (by omega), hA, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega)]

end Light.Sec4

end
end

section


/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam








theorem length_base58 : base58.length = 58 := rfl

/-- A procedure of base58 is a procedure, with the same number, of every program that begins with
base58. -/
theorem at_base58 {p : ℕ} {body : Stmt} (h : base58[p]? = some body) (R : Program) :
    (base58 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R




theorem has40_base58 (R : Program) : Has40 (base58 ++ R) := by
  have h := has40_of_append (A := Sec2.programThin ++ List.replicate 11 .skip)
    (B := [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) rfl
  rwa [← List.append_assoc] at h
















/-- **A query at a given place of the memory**, in every program that begins with base58. -/
theorem queryAt_base58 (R : Program) : ∀ lim, QueryAtSpec lim (base58 ++ R) :=
  queryAtSpec_all (has40_base58 R) (at_base58 rfl R)




end Light.Sec4

end
end

section


/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/












/-! ## The program -/










/-- The routines stand at their numbers. -/
theorem program31_at (G : RatParams) (n : ℕ) {body : Stmt} (hn : 58 ≤ n := by norm_num)
    (h : (procs31 G)[n - 58]? = some body := by rfl) : (program31 G)[n]? = some body := by
  rw [program31, List.getElem?_append_right (by rw [length_base58]; exact hn), length_base58]
  exact h
















/-- **A query**, for all limits. -/
theorem query31_program31 (G : RatParams) : ∀ lim, QuerySpec31 lim (program31 G) G := by
  intro lim N D₀ aX aY fr X Y U μ I J hin
  have hip : IpAtSpec lim (program31 G) := ipAt_meets (program31_at G Proc.ipAt) hin.lim.std
  exact query31_meets G (program31_at G Proc.query31) (queryAt_base58 _ lim) hip
    N D₀ aX aY fr X Y U μ I J hin

/-- **The offline routine**, for all limits. -/
theorem offline32_program31 (G : RatParams) : ∀ lim, OfflineSpec32 lim (program31 G) cShared30 G :=
  fun lim => offline32_meets (program31_at G Proc.offline32) (pre31_program31 G lim)
    (query31_program31 G lim)













/-! ## The program on the word RAM -/







































end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Time and need -/


















/-! ## The test -/





















/-! ## The limits -/

section need

variable {lim : Limits} {N D₀ w U fr d : ℕ}










































































end need

/-! ## The matrices of an instance -/



































/-! ## The routine -/


























































































/-! ## The time in the regime -/


















/-! ## The need is polynomial in the parameters -/

private theorem le_pow_twenty {Q x : ℕ} (hQ : 1 ≤ Q) (i : ℕ) (hi : i ≤ 20) (h : x ≤ Q ^ i) :
    x ≤ Q ^ 20 :=
  h.trans (Nat.pow_le_pow_right hQ hi)

section summands

variable {N D U Q : ℕ}

/-- The largest number that allInstances26 forms. -/
private theorem word_le (hN : N + 1 ≤ Q) (hD : D ≤ Q) (hU : U ≤ Q) :
    1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) +
      7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5 ≤ 2 ^ 11 * Q ^ 20 := by
  have hQ : 1 ≤ Q := by omega
  have hN' : N ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hD1 : D ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hD)
  have hND : N * D ≤ Q ^ 20 := le_pow_twenty hQ 2 (by norm_num) <|
    calc N * D ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hDUU : D * (U * U) ≤ Q ^ 20 := le_pow_twenty hQ 3 (by norm_num) <|
    calc D * (U * U) ≤ Q * (Q * Q) := by gcongr
      _ = Q ^ 3 := by ring
  have hvalue : ((N + 1) ^ 5) ^ 3 * (U * U) ≤ Q ^ 20 := le_pow_twenty hQ 17 (by norm_num) <|
    calc ((N + 1) ^ 5) ^ 3 * (U * U) ≤ (Q ^ 5) ^ 3 * (Q * Q) := by gcongr
      _ = Q ^ 17 := by ring
  have henc : (N + 1) ^ 5 * U ≤ Q ^ 20 := le_pow_twenty hQ 6 (by norm_num) <|
    calc (N + 1) ^ 5 * U ≤ Q ^ 5 * Q := by gcongr
      _ = Q ^ 6 := by ring
  have hpow : (N + 1) ^ 5 ≤ Q ^ 20 := le_pow_twenty hQ 5 (by norm_num) (by gcongr)
  -- 1000 + 100 + 1 + 1 + 1 + 7 + 10 = 1120 ≤ 2^11
  omega

/-- The cells that allInstances26 uses. -/
private theorem cells_le (hN : N + 1 ≤ Q) (hD : D ≤ Q) :
    4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4 ≤ 2 ^ 11 * Q ^ 20 := by
  have hQ : 1 ≤ Q := by omega
  have hN' : N ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hN1 : N ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hN')
  have hND : N * D ≤ Q ^ 20 := le_pow_twenty hQ 2 (by norm_num) <|
    calc N * D ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hblock : ((N + 1) ^ 5) ^ 4 ≤ Q ^ 20 :=
    calc ((N + 1) ^ 5) ^ 4 ≤ (Q ^ 5) ^ 4 := by gcongr
      _ = Q ^ 20 := by ring
  omega

/-- The levels of calls that allInstances26 needs. -/
private theorem depth_le (hQ : 1 ≤ Q) (hD : D ≤ Q) : 84 * D + 12 ≤ 2 ^ 11 * Q ^ 20 := by
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hD1 : D ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hD)
  omega

end summands

/-- Three of four positive factors are at most the product. -/
private theorem le_prod_four {a b c e : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≤ a * (b * (c * e)) ∧ b ≤ a * (b * (c * e)) ∧ e ≤ a * (b * (c * e)) :=
  ⟨Nat.le_mul_of_pos_right a (by positivity),
    (Nat.le_mul_of_pos_right b (by positivity)).trans (Nat.le_mul_of_pos_left _ ha),
    ((Nat.le_mul_of_pos_left e hc).trans (Nat.le_mul_of_pos_left _ hb)).trans
      (Nat.le_mul_of_pos_left _ ha)⟩

/-- The need is polynomial in the parameters. -/
theorem allInstancesNeed26_poly : PolyNeedN allInstancesNeed26 := by
  refine ⟨11, 20, fun ps => ?_⟩
  match ps with
  | [N, D, w, U] =>
    obtain ⟨hN, hD, hU⟩ := le_prod_four N.succ_pos D.succ_pos w.succ_pos U.succ_pos
    rw [show polyBound 11 20 [N, D, w, U] =
      2 ^ 11 * ((N + 1) * ((D + 1) * ((w + 1) * (U + 1)))) ^ 20 by simp [polyBound]]
    generalize (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) = Q at *
    exact ⟨word_le hN (by omega) (by omega), cells_le hN (by omega), depth_le (by omega) (by omega)⟩
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, for programs of the light language

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". This is
`Claim.Corollary_26_wanted`, here with "is solved in time T" read as a statement about programs of
the light language (`claim_corollary_26_wanted`).

The program is `program26`: for m = ⌈log₄ D⌉ ≥ 60 it builds and asks the data structure of Theorem
30 with L = 21 m and t = ⌈m/9⌉, and for m < 60 it computes inner products. The procedure
allInstances26 of that program solves the task on all instances (`allInstances26_program26`), with a
polynomially bounded need (`allInstancesNeed26_poly`), and for N ≥ D^18 its time is within the bound
(`allInstancesTime26_le`).

This is the form of Corollary 26 on which Corollary 16, and through it the second bounds of Theorems
19 and 22, rest: a procedure that other procedures call. The statement about one program that reads
the input of the problem is `wordRam_corollary_26_wanted`.
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-- The time of allInstances26 is monotone in the number of wanted positions and does not depend on
the bound on the entries. -/
private theorem allInstancesTime26_mono (c N D₀ : ℕ) {w w' : ℕ} (U U' : ℕ) (hw : w ≤ w') :
    allInstancesTime26 c [N, D₀, w, U] ≤ allInstancesTime26 c [N, D₀, w', U'] := by
  change 400 + (if D₀ ^ 18 ≤ N then tOffline32 c ratParams26 N D₀ w else 40 * ((w + 1) * (D₀ + 1)))
    ≤ 400 + (if D₀ ^ 18 ≤ N then tOffline32 c ratParams26 N D₀ w' else 40 * ((w' + 1) * (D₀ + 1)))
  split_ifs
  · unfold tOffline32
    have := Nat.mul_le_mul_right (tQuery31 ratParams26 D₀ + 30) hw
    omega
  · have := Nat.mul_le_mul_right (D₀ + 1) (show w + 1 ≤ w' + 1 by omega)
    omega

/-- **The procedure allInstances26 of `program26` solves the task on all instances**: the program
holds allInstances26, regimeTest26 and the brute force at their numbers. -/
theorem allInstances26_program26 : SolvesN thinTask program26 Proc.allInstances26
    (allInstancesTime26 cShared30) allInstancesNeed26 :=
  allInstances26_solves (program31_at _ Proc.allInstances26) (program31_at _ Proc.regimeTest26)
    (at_base58 rfl _) fun R lim => (offline32_program31 _ lim).append R

/-- **Corollary 26, last sentence, for programs of the light language.** -/
theorem claim_corollary_26_wanted : Claim.Corollary_26_wanted lightModel := by
  intro _
  obtain ⟨C, hC⟩ := allInstancesTime26_le cShared30
  refine ⟨C, fun N D₀ w _ => (allInstancesTime26 cShared30 [N, D₀, w, 0] : ℝ),
    ⟨_, _, _, _, allInstancesNeed26_poly, allInstances26_program26,
      fun N D₀ w w' U u _ _ _ hw _ => ?_⟩,
    fun N D₀ w u hD hN _ => hC N D₀ w 0 hD hN⟩
  change (allInstancesTime26 cShared30 [N, D₀, w, U] : ℝ) ≤
      (allInstancesTime26 cShared30 [N, D₀, w', 0] : ℝ)
  exact_mod_cast allInstancesTime26_mono cShared30 N D₀ U 0 hw

end Light.Sec4

end
end

section


/-!
# Running-time claims of Section 3.1: Corollaries 15 and 16

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".

* Corollary 15, first case, from Theorem 5 ("Apply Theorem 5 with N = n to the two biadjacency
  matrices"): `Corollary15.first_of_theorem_5`.
* Corollary 15, general case ("splitting W into sets of at most n²/√D query pairs"):
  `Corollary15.general_of_theorem_5`.  One call costs `O(n² log² D / D^{1/18})`, and all calls
  with the overhead cost `O((n² + |W| √D) log² D / D^{1/18})` (`dominated_calls`).
* Corollary 16 from Corollary 26 ("This is Corollary 26 with N = n"):
  `Corollary16.of_corollary_26`.

In each deduction the overheads `n D`, `|W|` and `1` of writing the matrices and copying the answers
are at most the bound of the corollary, because `n ≥ D^18`.  The bounds are added up by the calculus
of `Dominated` on the parameters `n`, `D`, `w`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## The calculus on the parameters `n`, `D`, `w` -/











/-- From the time `T` for the product of the two biadjacency matrices to the times for counting and
for detection (the claims `LopCountFromThinProduct` and `LopDetectFromCount`): if `T` and the
overheads `n D`, `w` and `1` are `O(g)`, so are the two times, with one constant. -/
private theorem exists_const_count_detect {dom : LopSize → Prop} {T g : LopSize → ℝ} (C₁ C₃ : ℝ)
    (hT : Dominated dom T g) (hnD : Dominated dom (fun p => (p.n : ℝ) * p.D) g)
    (hw : Dominated dom (fun p => (p.w : ℝ)) g) (hone : Dominated dom (fun _ => (1 : ℝ)) g)
    (hg : ∀ p, dom p → 0 ≤ g p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, dom p → T p + C₁ * ((p.n : ℝ) * p.D + p.w + 1) ≤ C * g p ∧
      T p + C₁ * ((p.n : ℝ) * p.D + p.w + 1) + C₃ * ((p.w : ℝ) + 1) ≤ C * g p := by
  have hcount := hT.add (((hnD.add hw).add hone).const_mul_of_nonneg C₁ fun p _ => by positivity)
  exact hcount.exists_const_and
    (hcount.add ((hw.add hone).const_mul_of_nonneg C₃ fun p _ => by positivity)) hg hg

/-! ## Corollary 15, the first case -/























/-! ## Corollary 15, the general case -/





















































/-! ## Corollary 16 -/

/-- The deduction of Corollary 16 from Corollary 26: "This is Corollary 26 with N = n,
applied to the two biadjacency matrices as above." -/
theorem Corollary16.of_corollary_26 (M : DetTimeModel)
    (h26 : Claim.Corollary_26_wanted M) (hlop : Claim.LopCountFromThinProduct M)
    (hdet : Claim.LopDetectFromCount M) : Claim.Corollary_16 M := by
  obtain ⟨C₁, hlop⟩ := hlop
  obtain ⟨C₃, hdet⟩ := hdet
  obtain ⟨C, T, hT, hb⟩ := h26 0
  obtain ⟨K, hK0, hK⟩ := exists_const_count_detect C₁ C₃
    (dom := fun p => 1 ≤ p.D ∧ p.D ^ 18 ≤ p.n) (T := fun p => T p.n p.D p.w 1)
    (g := fun p => wantedBound p.n p.D p.w)
    (.of_exists_const ⟨C, fun p ⟨hD, hDn⟩ => hb p.n p.D p.w 1 hD hDn (Real.rpow_zero _).ge⟩
      fun p _ => by positivity)
    (.of_le fun p ⟨hD, hDn⟩ => (mul_le_sq_div_rpow hD hDn (by norm_num)).trans
      (sq_div_rpow_le_wantedBound p.n p.D p.w))
    (.of_le fun p ⟨hD, _⟩ => (le_mul_of_one_le_right p.w.cast_nonneg
      (Real.one_le_rpow (Nat.one_le_cast.2 hD) (by norm_num))).trans
        (le_add_of_nonneg_right (by positivity)))
    (.of_le fun p ⟨hD, hDn⟩ => one_le_wantedBound hD hDn p.w)
    fun p _ => by positivity
  exact ⟨K, _, _, hK0, hlop T hT, hdet _ (hlop T hT), fun n D w hD hDn => hK ⟨n, D, w⟩ ⟨hD, hDn⟩⟩

end ThreeSumApsp

end
end

section


/-!
# Corollaries 15 and 16 on the word RAM

The route, as in the paper.  The number of triangles through a query pair is an entry of the product
of the two biadjacency matrices, and detection follows from counting.  So Theorem 5 gives the first
case of Corollary 15; splitting the query pairs into pieces gives the general case; and the offline
form of Corollary 26 gives Corollary 16.  These are claims about programs of the light language
(`claim_corollary_15_first`, `claim_corollary_15`, `claim_corollary_16`).  The outermost procedures
for the input layout and the compiler (`Light.Sec3.realized_lopCount`,
`Light.Sec3.realized_lopDetect`, together `lopRealized`) carry them to the word RAM.
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3











/-- Corollary 16 for programs of the light language. -/
theorem claim_corollary_16 : Claim.Corollary_16 lightModel :=
  Corollary16.of_corollary_26 _ Sec4.claim_corollary_26_wanted
    claim_lopCountFromThinProduct claim_lopDetectFromCount






end Light.Sec3

namespace ThreeSumApsp









end ThreeSumApsp

end
end

section


/-!
# Theorem 17, second step: the instances

With `s = ⌊√D⌋`, the part `C` is split into `h` pieces of at most `⌈s/g⌉` vertices, the pairs
`(a,b)` are grouped by `ϱ = w(a,b) mod p` into the sets `W_ϱ`, and every `W_ϱ` is cut into chunks of
at most `n²/√D` pairs.  There is one instance of Lop-AE-SparseTri(n, D) for each chunk and each
piece.  As in the paper:

* the pieces, and `h ≤ ⌈ng/s⌉` (`existsUnique_mem_piece`, `card_piece_le`,
  `numPieces_le`);
* the sets `W_ϱ` and their chunks (`TriangleInstance.existsUnique_mem_residueClass`,
  `TriangleInstance.card_chunkOf_le`);
* there are at most `p + √D ≤ 2√D` chunks in all (`TriangleInstance.totalChunks_le`); as a chunk
  holds a whole number of pairs, this rests on `n² < (s + 1)⌊n²/√D⌋ + p` (`sq_lt_mul_queryCap_add`);
* the middle part has at most `sp ≤ D` vertices (`TriangleInstance.middleAtMost_lopInstance`);
* within a chunk, `S(a,b,c) ≡ 0 (mod p)` is an equality of labels
  (`TriangleInstance.S_modEq_zero_iff`), so a query pair has a common neighbor if and only if some
  `c` in the piece has `S(a,b,c) ≡ 0 (mod p)` (`TriangleInstance.inTriangle_lopInstance_iff`);
* there are at most `2√D h ≤ 4ng` instances (`le_sOf_and_sqrt_le`,
  `TriangleInstance.card_instanceIndices_le`).

The file ends with a remark of Section 3.1 and of Remark 20: a vertex of `A` or `B` has at most
`⌈s/g⌉` neighbors in an instance (`TriangleInstance.ncard_nbr_lopInstance_le`).  Nothing else rests
on it.
-/

@[expose] public section

namespace ThreeSumApsp

variable {n D g p : ℕ}

/-! ### The pieces -/

/-- `s = ⌊√D⌋ ≤ √D`. -/
theorem sOf_le_sqrt (D : ℕ) : (sOf D : ℝ) ≤ Real.sqrt D := Nat.floor_le (Real.sqrt_nonneg _)

/-- `√D < s + 1`. -/
theorem sqrt_lt_sOf_add_one (D : ℕ) : Real.sqrt D < (sOf D : ℝ) + 1 := Nat.lt_floor_add_one _

/-- `s > 0` because `D ≥ 16`. -/
private theorem sOf_pos (hD : 16 ≤ D) : (0 : ℝ) < sOf D := by
  linarith [Real.four_le_sqrt_natCast_of_sixteen_le hD, sqrt_lt_sOf_add_one D]

/-- The bound `⌈s/g⌉` on the size of a piece is at least 1. -/
theorem pieceSize_pos (hD : 16 ≤ D) (hg1 : 1 ≤ g) : 0 < pieceSize D g :=
  Nat.ceil_pos.mpr (div_pos (sOf_pos hD) (by exact_mod_cast hg1))

























/-- Proof of Theorem 17: "so that h ≤ ⌈ng/s⌉". -/
theorem numPieces_le (hD : 16 ≤ D) (hg1 : 1 ≤ g) :
    numPieces n D g ≤ ⌈(n : ℝ) * (g : ℝ) / (sOf D : ℝ)⌉₊ := by
  have hsize : (0 : ℝ) < pieceSize D g := by exact_mod_cast pieceSize_pos hD hg1
  have hg : (0 : ℝ) < g := by exact_mod_cast hg1
  -- `s ≤ ⌈s/g⌉ g`
  have hs : (sOf D : ℝ) ≤ (pieceSize D g : ℝ) * (g : ℝ) := (div_le_iff₀ hg).mp (Nat.le_ceil _)
  refine Nat.ceil_mono ?_
  rw [div_le_div_iff₀ hsize (sOf_pos hD)]
  calc (n : ℝ) * (sOf D : ℝ) ≤ (n : ℝ) * ((pieceSize D g : ℝ) * (g : ℝ)) := by gcongr
    _ = (n : ℝ) * (g : ℝ) * (pieceSize D g : ℝ) := by ring

/-! ### Residues -/





/-- The residue of `x` is congruent to `x`. -/
theorem resFin_modEq (hp : p ≠ 0) (x : ℤ) : ((resFin hp x : ℕ) : ℤ) ≡ x [ZMOD (p : ℤ)] := by
  rw [resFin, Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp)]
  exact Int.mod_modEq x p

/-- An element of `Fin p` is congruent to `x` modulo `p` exactly if it is the residue of `x`. -/
private theorem modEq_iff_eq_resFin (hp : p ≠ 0) (σ : Fin p) (x : ℤ) :
    ((σ : ℕ) : ℤ) ≡ x [ZMOD (p : ℤ)] ↔ σ = resFin hp x := by
  refine ⟨fun h => ?_, fun h => h ▸ resFin_modEq hp x⟩
  -- Two congruent numbers in `{0, …, p − 1}` are equal.
  have hmod : (σ : ℕ) ≡ (resFin hp x : ℕ) [MOD p] :=
    (Int.natCast_modEq_iff).mp (h.trans (resFin_modEq hp x).symm)
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod σ.isLt (resFin hp x).isLt)

/-! ### The arithmetic behind the two counts -/

/-- The number `⌈|S|/cap⌉` of chunks of `S` satisfies `⌈|S|/cap⌉ cap ≤ |S| + cap − 1`. -/
private theorem numChunks_mul_le (S : Finset (Fin n × Fin n)) (cap : ℕ) (hcap : 1 ≤ cap) :
    numChunks S cap * cap + 1 ≤ S.card + cap := by
  rw [numChunks, Nat.ceil_div_eq_ceilDiv _ hcap]
  exact Nat.ceilDiv_mul_lt hcap

/-- `s + 1` exceeds `√D` by at least `1/(2√D + 1)`: since `(s + 1)²` and `D` are integers,
`1 ≤ (s + 1)² − D = (s + 1 − √D)(s + 1 + √D)`. -/
private theorem one_le_gap_mul (D : ℕ) :
    1 ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) := by
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
  have hle := sOf_le_sqrt D
  have hlt := sqrt_lt_sOf_add_one D
  have hinteger : (D : ℝ) + 1 ≤ ((sOf D : ℝ) + 1) ^ 2 := by
    have hreal : (D : ℝ) < ((sOf D : ℝ) + 1) ^ 2 :=
      hsq ▸ pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) two_ne_zero
    have hnat : D < (sOf D + 1) ^ 2 := by exact_mod_cast hreal
    exact_mod_cast hnat
  calc (1 : ℝ) ≤ ((sOf D : ℝ) + 1) ^ 2 - Real.sqrt D ^ 2 := by linarith [hinteger, hsq]
    _ = ((sOf D : ℝ) + 1 - Real.sqrt D) * ((sOf D : ℝ) + 1 + Real.sqrt D) := by ring
    _ ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- The inequality behind "at most p + √D [...] chunks": `n² < (s + 1) ⌊n²/√D⌋ + p`.

Write `r = √D`, `x = n²/r` and `δ = s + 1 − r`.  Then
`(s + 1)⌊x⌋ > (s + 1)(x − 1) = n² + xδ − (s + 1)`, so it is enough that `xδ ≥ r/2 + 1 ≥ s + 1 − p`.
This holds because `x ≥ r³` (as `D ≤ n`), `δ ≥ 1/(2r + 1)` (as `D` is an integer) and `r ≥ 4`. -/
private theorem sq_lt_mul_queryCap_add (hD : 16 ≤ D) (hDn : D ≤ n)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : n ^ 2 < (sOf D + 1) * queryCap n D + p := by
  have hgap := one_le_gap_mul D
  have hs := sOf_le_sqrt D
  set r := Real.sqrt D with hr
  set δ := (sOf D : ℝ) + 1 - r with hδ
  set x := (n : ℝ) ^ 2 / r with hx
  have hr4 : 4 ≤ r := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hxr : x * r = (n : ℝ) ^ 2 := div_mul_cancel₀ _ (by linarith)
  have hx3 : r ^ 3 ≤ x := by
    rw [hx, le_div_iff₀ (by linarith)]
    calc r ^ 3 * r = (r ^ 2) ^ 2 := by ring
      _ = (D : ℝ) ^ 2 := by rw [hr, Real.sq_sqrt (Nat.cast_nonneg D)]
      _ ≤ (n : ℝ) ^ 2 := by gcongr
  have hxδ : r / 2 + 1 ≤ x * δ := by
    refine le_of_mul_le_mul_right ?_ (show 0 < 2 * r + 1 by linarith)
    calc (r / 2 + 1) * (2 * r + 1) ≤ r ^ 3 := by
          -- `r³ ≥ 4r²` and `r² ≥ 4r`
          linarith [mul_le_mul_of_nonneg_right hr4 (sq_nonneg r),
            mul_le_mul_of_nonneg_right hr4 (show 0 ≤ r by linarith)]
      _ ≤ x * 1 := by rw [mul_one]; exact hx3
      _ ≤ x * (δ * (2 * r + 1)) :=
          mul_le_mul_of_nonneg_left hgap (le_trans (by positivity) hx3)
      _ = x * δ * (2 * r + 1) := by ring
  have hfloor : x < (queryCap n D : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmain : (n : ℝ) ^ 2 < ((sOf D : ℝ) + 1) * (queryCap n D : ℝ) + p :=
    calc (n : ℝ) ^ 2 = x * r := hxr.symm
      _ ≤ x * r + x * δ - ((sOf D : ℝ) + 1) + r / 2 := by
          -- `s + 1 ≤ r + 1 ≤ xδ + r/2`
          linarith [hxδ, hs]
      _ = ((sOf D : ℝ) + 1) * (x - 1) + r / 2 := by rw [hδ]; ring
      _ < ((sOf D : ℝ) + 1) * (queryCap n D : ℝ) + p :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (by linarith [hfloor]) (by positivity)) hp
  exact_mod_cast hmain

/-- Proof of Theorem 17: the two facts used for the count of the instances, "s ≥ √D − 1 ≥ 3√D/4
because D ≥ 16, and √D ≤ √n ≤ 2n/3 because D ≤ n and we may assume n ≥ 3". -/
theorem le_sOf_and_sqrt_le (hD : 16 ≤ D) (hDn : D ≤ n) :
    3 * Real.sqrt D / 4 ≤ (sOf D : ℝ) ∧ Real.sqrt D ≤ 2 * (n : ℝ) / 3 := by
  have hsqrtD := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hsqrtn := Real.four_le_sqrt_natCast_of_sixteen_le (hD.trans hDn)
  constructor
  · calc 3 * Real.sqrt D / 4 ≤ Real.sqrt D - 1 := by linarith
      _ ≤ (sOf D : ℝ) := by linarith [sqrt_lt_sOf_add_one D]
  · calc Real.sqrt D ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hDn)
      _ ≤ 2 * (n : ℝ) / 3 := by
          -- `n = √n √n ≥ 4√n`
          linarith [mul_le_mul_of_nonneg_right hsqrtn (Real.sqrt_nonneg n),
            Real.mul_self_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

namespace TriangleInstance

variable (T : TriangleInstance ℤ n)

/-! ### The sets `W_ϱ` -/

/-- A pair lies in `W_ϱ` exactly if `ϱ` is the residue of its weight. -/
theorem mem_residueClass (hp : p ≠ 0) (ϱ : Fin p) (q : Fin n × Fin n) :
    q ∈ T.residueClass p ϱ ↔ ϱ = resFin hp (T.wAB q.1 q.2) := by
  rw [← modEq_iff_eq_resFin]
  simp only [residueClass, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Int.ModEq.symm, Int.ModEq.symm⟩








/-- The sets `W_ϱ` have `n²` pairs in all. -/
private theorem sum_card_residueClass (hp : p ≠ 0) :
    ∑ ϱ : Fin p, (T.residueClass p ϱ).card = n ^ 2 := by
  calc ∑ ϱ : Fin p, (T.residueClass p ϱ).card
      = ∑ ϱ : Fin p, ((Finset.univ : Finset (Fin n × Fin n)).filter
          fun q => resFin hp (T.wAB q.1 q.2) = ϱ).card := by
        refine Finset.sum_congr rfl fun ϱ _ => congrArg Finset.card ?_
        ext q
        rw [T.mem_residueClass hp]
        simp [eq_comm]
    _ = (Finset.univ : Finset (Fin n × Fin n)).card :=
        (Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)).symm
    _ = n ^ 2 := by simp [sq]

/-! ### The chunks -/









/-- There are at most `p + s` chunks in all.  Each `W_ϱ` has at most `(|W_ϱ| + cap − 1)/cap` chunks,
where `cap = ⌊n²/√D⌋`, so `p + s + 1` chunks or more would need `n² ≥ (s + 1) cap + p` pairs. -/
private theorem totalChunks_le_add_sOf (hD : 16 ≤ D) (hDn : D ≤ n) (hp0 : p ≠ 0)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : T.totalChunks D p ≤ p + sOf D := by
  have hsum : T.totalChunks D p * queryCap n D + p ≤ n ^ 2 + p * queryCap n D := by
    have h := Finset.sum_le_sum fun ϱ (_ : ϱ ∈ (Finset.univ : Finset (Fin p))) =>
      numChunks_mul_le (T.residueClass p ϱ) (queryCap n D) (one_le_queryCap (by omega) hDn)
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] at h
    rwa [T.sum_card_residueClass hp0] at h
  have hpairs := sq_lt_mul_queryCap_add hD hDn hp
  by_contra hmany
  have hmul : (p + sOf D + 1) * queryCap n D ≤ T.totalChunks D p * queryCap n D :=
    Nat.mul_le_mul_right _ (by omega)
  rw [show (p + sOf D + 1) * queryCap n D = p * queryCap n D + (sOf D + 1) * queryCap n D by
    ring] at hmul
  -- `hsum` and `hmul` give `(s + 1) cap + p ≤ n²`, against `hpairs`.
  omega

/-- Proof of Theorem 17: "There are at most p + √D ≤ 2√D chunks in all."

NOTE.  A chunk holds a whole number of pairs, at most `⌊n²/√D⌋`, so the count is at most
`p + (n² − p)/⌊n²/√D⌋`, and the second term can exceed `√D` slightly.  The printed bound is still
true, because the count is an integer, `D` is an integer and `D ≤ n` (`sq_lt_mul_queryCap_add`). -/
theorem totalChunks_le (hD : 16 ≤ D) (hDn : D ≤ n) (hp : p ∈ primesInRange D) :
    (T.totalChunks D p : ℝ) ≤ (p : ℝ) + Real.sqrt D ∧
    (p : ℝ) + Real.sqrt D ≤ 2 * Real.sqrt D := by
  obtain ⟨hprime, hge, hlt⟩ := mem_primesInRange.mp hp
  have hnat : (T.totalChunks D p : ℝ) ≤ (p : ℝ) + (sOf D : ℝ) := by
    exact_mod_cast T.totalChunks_le_add_sOf hD hDn hprime.ne_zero hge
  exact ⟨by linarith [sOf_le_sqrt D], by linarith⟩

/-! ### The instances -/













































































/-- Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances". -/
theorem card_instanceIndices_le (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (hp : p ∈ primesInRange D) :
    ((T.instanceIndices D g p).card : ℝ) ≤ 4 * (n : ℝ) * (g : ℝ) := by
  obtain ⟨hs, hsqrt⟩ := le_sOf_and_sqrt_le hD hDn
  obtain ⟨hchunks, hchunks'⟩ := T.totalChunks_le hD hDn hp
  have hs0 := sOf_pos hD
  have hpieces : (numPieces n D g : ℝ) ≤ (n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1 :=
    calc (numPieces n D g : ℝ) ≤ (⌈(n : ℝ) * (g : ℝ) / (sOf D : ℝ)⌉₊ : ℝ) := by
          exact_mod_cast numPieces_le hD hg1
      _ ≤ (n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  -- `2√D · ng/s ≤ 8ng/3` because `s ≥ 3√D/4`, and `2√D ≤ 4n/3 ≤ 4ng/3`.
  have hmain :
      Real.sqrt D * ((n : ℝ) * (g : ℝ) / (sOf D : ℝ)) ≤ 4 / 3 * ((n : ℝ) * (g : ℝ)) := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    calc Real.sqrt D * ((n : ℝ) * (g : ℝ))
        = 4 / 3 * ((n : ℝ) * (g : ℝ)) * (3 * Real.sqrt D / 4) := by ring
      _ ≤ 4 / 3 * ((n : ℝ) * (g : ℝ)) * (sOf D : ℝ) := by gcongr
  have hng : (n : ℝ) ≤ (n : ℝ) * (g : ℝ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg n) (by exact_mod_cast hg1)
  calc ((T.instanceIndices D g p).card : ℝ)
      = (T.totalChunks D p : ℝ) * (numPieces n D g : ℝ) := by
        rw [card_instanceIndices, Nat.cast_mul]
    _ ≤ 2 * Real.sqrt D * (numPieces n D g : ℝ) := by gcongr; exact hchunks.trans hchunks'
    _ ≤ 2 * Real.sqrt D * ((n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1) := by gcongr
    _ ≤ 4 * (n : ℝ) * (g : ℝ) := by linarith [hmain, hng, hsqrt]

end TriangleInstance

/-! ### The neighborhoods in an instance -/






































end ThreeSumApsp

end
end

section


/-!
# Theorem 17, third step: witnesses

For every query pair that the oracle accepts, the piece `C_k` of its instance is scanned for a `c`
with `S(a,b,c) = 0`, and the scans stop at the first zero triangle.  As in the paper:

* a zero triangle is always found (`TriangleInstance.exists_mem_acceptedPairs`);
* a failed scan contains a false positive of `p`
  (`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`), and distinct scans contain
  distinct false positives (`TriangleInstance.eq_of_mem_acceptedPairs`), so there are at most `F(p)`
  failed scans (`TriangleInstance.card_le_F_of_distinct_scans`,
  `TriangleInstance.card_failedScans_le`);
* a scan looks at at most `⌈s/g⌉ ≤ 2√D/g` vertices (`pieceSize_le_two_mul_sqrt_div`), so the scans
  cost `O((F(p) + 1)√D/g) = O(κ n³ log n/g)` (`TriangleInstance.F_add_one_mul_pieceSize_le`).

`Theorem17.correctness` puts the first two together.

The program for Theorem 17 works on lists, and for its lists the sentences of this step are lemmas
of their own: `HostData.found_m` answers `TriangleInstance.exists_mem_acceptedPairs`,
`HostData.exists_false_positive` answers
`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`, `HostData.Valid.eq_of_place_eq`
answers `TriangleInstance.eq_of_mem_acceptedPairs`, and `HostData.sum_fails_le` answers
`TriangleInstance.card_failedScans_le`.  The two proofs share `F(p)`, the first step of the
proof, the number of instances and the counting step `TriangleInstance.card_le_F_of_distinct_scans`;
no theorem about programs rests on another lemma of this file.
-/

@[expose] public section

namespace ThreeSumApsp

variable {n D g p : ℕ}

namespace TriangleInstance

variable {T : TriangleInstance ℤ n}

/-! ### Scans and accepted pairs -/
















variable (T) (D g)






































variable (p) (ans : InstanceIndex p → Fin n × Fin n → Bool)











variable {T D g p ans}








/-! ### The sentences of the paragraph "Witnesses" -/














































/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans", for any finite family `s` of scans and any notion "the scan `x` contains the triple
`t`".  The scans of the accepted pairs (`card_failedScans_le`) and the scans of the program
(`HostData.sum_fails_le`) are two such families. -/
theorem card_le_F_of_distinct_scans (T : TriangleInstance ℤ n) {σ : Type*} (s : Finset σ)
    (contains : σ → Fin n × Fin n × Fin n → Prop)
    (hfalse : ∀ x ∈ s, ∃ t, contains x t ∧ T.IsFalsePositive p t)
    (hdistinct : ∀ t, ∀ x ∈ s, ∀ y ∈ s, contains x t → contains y t → x = y) :
    s.card ≤ T.F p := by
  classical
  refine Finset.card_le_card_of_forall_subsingleton contains (fun x hx => ?_)
    fun t _ x hx y hy => hdistinct t x hx.1 y hy.1 hx.2 hy.2
  obtain ⟨t, ht, hfp⟩ := hfalse x hx
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfp⟩, ht⟩













end TriangleInstance







































/-! ### The output of the reduction -/


























end ThreeSumApsp

end
end

section


/-!
# The cost analysis of Theorem 19 for a general choice of the parameters

The two halves of the proof of Theorem 19 are the same computation with different numbers.  Both
apply Theorem 17 with a number `D ≥ 16` between `n^{1/18}/c` and `n^{1/18}` and with `g = ⌈D^η⌉`,
and solve each of the at most `4ng` instances with a saving `D^{2η}`.  Such a pair `D`, `η` is a
`Choice`, and the computation is carried out here for every choice.

1. A choice satisfies the hypotheses `16 ≤ D ≤ n` and `1 ≤ g ≤ √D` of Theorem 17 and the hypothesis
   `D^18 ≤ n` of Corollaries 15 and 16 (`Choice.sixteen_le`, `Choice.le_n`, `Choice.one_le_ceil`,
   `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. The lower bound on `D` gives `D^{-η} ≤ c^η n^{-η/18}` (`Choice.saving`), and the upper bound
   gives `D^a ≤ n^{a/18}` (`Choice.rpow_le_rpow_div`).
3. Each of the four terms of the running time is `O(n^{3-η/18})` up to logarithms: the instances
   (`Choice.instances_le`) and the scans (`Choice.scans_le`) by the first bound, the choice of `p`
   (`Choice.strassen_le`) and building the instances (`Choice.build_le`) by the second.
4. So is their sum (`exists_total_le`).
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem19

















/-- `x ≤ n^{1/18}` says that `x^18 ≤ n`. -/
theorem le_root_iff (x n : ℕ) : (x : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ) ↔ x ^ 18 ≤ n := by
  have h := Real.natCast_le_rpow_inv_iff (e := 18) (by norm_num) x n
  rwa [show ((18 : ℕ) : ℝ)⁻¹ = 1 / 18 by norm_num] at h

/-- `n^{1/18} ≥ 16` for `n ≥ 16^18`. -/
theorem sixteen_le_root {n : ℕ} (hn : 16 ^ 18 ≤ n) : (16 : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ) := by
  exact_mod_cast (le_root_iff 16 n).mpr hn

namespace Choice

variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P

/-! ### The hypotheses of Theorem 17 and of Corollaries 15 and 16 -/

/-- "Corollary 15 [...] applies because D^{18} ≤ n", and likewise Corollary 16. -/
theorem pow_eighteen_le : D ^ 18 ≤ n :=
  (le_root_iff D n).mp P.le_root

/-- `D ≤ n`, as Theorem 17 asks. -/
theorem le_n : D ≤ n :=
  (Nat.le_self_pow (by norm_num) D).trans P.pow_eighteen_le

private theorem one_le_D : (1 : ℝ) ≤ D :=
  Nat.one_le_cast.mpr (le_trans (by norm_num) P.sixteen_le)

private theorem D_pos : (0 : ℝ) < D :=
  zero_lt_one.trans_le P.one_le_D

private theorem one_le_n : (1 : ℝ) ≤ n :=
  P.one_le_D.trans (Nat.cast_le.mpr P.le_n)

private theorem n_pos : (0 : ℝ) < n :=
  zero_lt_one.trans_le P.one_le_n

private theorem one_le_rpow : 1 ≤ (D : ℝ) ^ η :=
  Real.one_le_rpow P.one_le_D P.η_nonneg

/-- `g ≥ 1`, as Theorem 17 asks. -/
theorem one_le_ceil : 1 ≤ ⌈(D : ℝ) ^ η⌉₊ :=
  Nat.ceil_pos.mpr (zero_lt_one.trans_le P.one_le_rpow)

/-- `g ≤ 2 D^η`: rounding up a number that is at least 1 at most doubles it. -/
private theorem ceil_le : (⌈(D : ℝ) ^ η⌉₊ : ℝ) ≤ 2 * (D : ℝ) ^ η :=
  Nat.ceil_le_two_mul ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans P.one_le_rpow)


















/-! ### Logarithms -/

/-- `log n ≥ 1`, because `n ≥ D ≥ 16`. -/
theorem one_le_log : 1 ≤ Real.log n :=
  Real.one_le_log_natCast_of_three_le ((by norm_num : 3 ≤ 16).trans (P.sixteen_le.trans P.le_n))





/-! ### Powers of `D` in terms of `n` -/

/-- "Finally D^{−1/36} ≤ 4^{1/36} n^{−1/648}", and "D ≥ n^{1/18}/2 gives D^{−0.0315} ≤ 2
n^{−0.0315/18}".  In general, `D ≥ n^{1/18}/c` gives `D^{-η} ≤ c^η n^{-η/18}`. -/
private theorem saving : (D : ℝ) ^ (-η) ≤ c ^ η * (n : ℝ) ^ (-(η / 18)) := by
  have hroot : 0 < (n : ℝ) ^ (1 / 18 : ℝ) := Real.rpow_pos_of_pos P.n_pos _
  calc (D : ℝ) ^ (-η) ≤ ((n : ℝ) ^ (1 / 18 : ℝ) / c) ^ (-η) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hroot P.c_pos) P.root_div_le
          (neg_nonpos.mpr P.η_nonneg)
    _ = ((n : ℝ) ^ (1 / 18 : ℝ)) ^ (-η) / c ^ (-η) := Real.div_rpow hroot.le P.c_pos.le _
    _ = c ^ η * (n : ℝ) ^ (-(η / 18)) := by
        rw [← Real.rpow_mul P.n_pos.le, Real.rpow_neg P.c_pos.le, div_inv_eq_mul, mul_comm,
          show 1 / 18 * -η = -(η / 18) by ring]

/-- `n³ D^{-η} ≤ c^η n^{3-η/18}`. -/
private theorem cube_mul_saving_le :
    (n : ℝ) ^ 3 * (D : ℝ) ^ (-η) ≤ c ^ η * (n : ℝ) ^ (3 - η / 18) :=
  calc (n : ℝ) ^ 3 * (D : ℝ) ^ (-η) ≤ (n : ℝ) ^ 3 * (c ^ η * (n : ℝ) ^ (-(η / 18))) := by
        gcongr
        exact P.saving
    _ = c ^ η * (n : ℝ) ^ (3 - η / 18) := by
        rw [sub_eq_add_neg, Real.rpow_add P.n_pos, Real.rpow_ofNat]
        ring

/-- `D^a ≤ n^{a/18}` for `a ≥ 0`. -/
private theorem rpow_le_rpow_div {a : ℝ} (ha : 0 ≤ a) : (D : ℝ) ^ a ≤ (n : ℝ) ^ (a / 18) :=
  calc (D : ℝ) ^ a ≤ ((n : ℝ) ^ (1 / 18 : ℝ)) ^ a := Real.rpow_le_rpow D.cast_nonneg P.le_root ha
    _ = (n : ℝ) ^ (a / 18) := by
        rw [← Real.rpow_mul n.cast_nonneg, show 1 / 18 * a = a / 18 by ring]

/-- A power `n^b` with `b ≤ 2.9` is at most `n^{3-η/18} Λ`, for every factor `Λ ≥ 1`. -/
private theorem rpow_le_of_le {b Λ : ℝ} (hb : b ≤ 2.9) (hΛ : 1 ≤ Λ) :
    (n : ℝ) ^ b ≤ (n : ℝ) ^ (3 - η / 18) * Λ :=
  (Real.rpow_le_rpow_of_exponent_le P.one_le_n (by linarith [P.η_le])).trans
    (le_mul_of_one_le_right (Real.rpow_nonneg n.cast_nonneg _) hΛ)

/-! ### The four terms of the running time

`Λ` is the logarithmic factor of the result, `log² n` or `log n`. -/

/-- "The O(nD^{1/36}) instances cost O(n² log² D/D^{1/18}) each, so O(n³ D^{−1/36} log² n) in all",
and "The instances cost O(nD^{0.0315}) · O(n²/D^{0.063}) = O(n³ D^{−0.0315})".  `X` is the
logarithmic factor in the cost of one instance, `log² D` or 1. -/
private theorem instances_le {X Λ : ℝ} (hX : 0 ≤ X) (hXΛ : X ≤ Λ) :
    4 * (n : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ) * ((n : ℝ) ^ 2 * X / (D : ℝ) ^ (2 * η))
      ≤ 8 * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) := by
  have hΛ : 0 ≤ Λ := hX.trans hXΛ
  have hdiv : (D : ℝ) ^ η / (D : ℝ) ^ (2 * η) = (D : ℝ) ^ (-η) := by
    rw [← Real.rpow_sub P.D_pos, show η - 2 * η = -η by ring]
  calc 4 * (n : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ) * ((n : ℝ) ^ 2 * X / (D : ℝ) ^ (2 * η))
      ≤ 4 * (n : ℝ) * (2 * (D : ℝ) ^ η) * ((n : ℝ) ^ 2 * Λ / (D : ℝ) ^ (2 * η)) := by
        gcongr
        exact P.ceil_le
    _ = 8 * ((n : ℝ) ^ 3 * ((D : ℝ) ^ η / (D : ℝ) ^ (2 * η)) * Λ) := by ring
    _ ≤ 8 * (c ^ η * (n : ℝ) ^ (3 - η / 18) * Λ) := by
        rw [hdiv]
        gcongr 8 * (?_ * Λ)
        exact P.cube_mul_saving_le
    _ = 8 * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) := by ring

/-- "the scans cost O(n³ D^{−1/36} log n)", and "the scans O(n³ D^{−0.0315} log n)", from the term
`κ n³ log n/g` of Theorem 17. -/
private theorem scans_le {κ Λ : ℝ} (hκ : 0 ≤ κ) (hΛ : Real.log n ≤ Λ) :
    termScans n ⌈(D : ℝ) ^ η⌉₊ κ ≤ κ * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) := by
  have hpos : 0 < (D : ℝ) ^ η := Real.rpow_pos_of_pos P.D_pos η
  have hΛ0 : 0 ≤ Λ := (Real.log_natCast_nonneg n).trans hΛ
  calc κ * (n : ℝ) ^ 3 * Real.log n / (⌈(D : ℝ) ^ η⌉₊ : ℝ)
      ≤ κ * (n : ℝ) ^ 3 * Λ / (D : ℝ) ^ η := by
        gcongr
        exact Nat.le_ceil _
    _ = κ * ((n : ℝ) ^ 3 * (D : ℝ) ^ (-η) * Λ) := by
        rw [Real.rpow_neg P.D_pos.le]
        ring
    _ ≤ κ * (c ^ η * (n : ℝ) ^ (3 - η / 18) * Λ) := by
        gcongr κ * (?_ * Λ)
        exact P.cube_mul_saving_le
    _ = κ * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) := by ring

/-- "the choice of p costs O(n^{log₂ 7} D^{3/2}) = O(n^{2.9}) with Strassen's algorithm" (both
cases): `log₂ 7 + (3/2)/18 < 2.81 + 0.09`.  Strassen's exponent stands for the `ω + o(1)` of
Theorem 17. -/
private theorem strassen_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    termPrime strassen n D ≤ (n : ℝ) ^ (3 - η / 18) * Λ :=
  calc (n : ℝ) ^ (Real.logb 2 7) * (D : ℝ) ^ (3 / 2 : ℝ)
      ≤ (n : ℝ) ^ (Real.logb 2 7) * (n : ℝ) ^ (3 / 2 / 18 : ℝ) := by
        gcongr
        exact P.rpow_le_rpow_div (by norm_num)
    _ = (n : ℝ) ^ (Real.logb 2 7 + 3 / 2 / 18) := (Real.rpow_add P.n_pos _ _).symm
    _ ≤ (n : ℝ) ^ (3 - η / 18) * Λ := P.rpow_le_of_le (by linarith [Real.logb_two_seven_lt]) hΛ

/-- "building the instances costs O(n² D^{1.03})", respectively "O(n² D^{1.04})", from the term
`n² D g` of Theorem 17: it is at most `2 n² D^{1+η} ≤ 2 n^{2+(1+η)/18}`. -/
private theorem build_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    termBuild n D ⌈(D : ℝ) ^ η⌉₊ ≤ 2 * ((n : ℝ) ^ (3 - η / 18) * Λ) :=
  calc (n : ℝ) ^ 2 * (D : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ)
      ≤ (n : ℝ) ^ 2 * (D : ℝ) * (2 * (D : ℝ) ^ η) := by
        gcongr
        exact P.ceil_le
    _ = 2 * ((n : ℝ) ^ 2 * (D : ℝ) ^ (1 + η)) := by
        rw [Real.rpow_add P.D_pos, Real.rpow_one]
        ring
    _ ≤ 2 * ((n : ℝ) ^ 2 * (n : ℝ) ^ ((1 + η) / 18)) := by
        gcongr
        exact P.rpow_le_rpow_div (by linarith [P.η_nonneg])
    _ = 2 * (n : ℝ) ^ (2 + (1 + η) / 18) := by rw [Real.rpow_add P.n_pos, Real.rpow_ofNat]
    _ ≤ 2 * ((n : ℝ) ^ (3 - η / 18) * Λ) := by
        gcongr
        exact P.rpow_le_of_le (by linarith [P.η_le]) hΛ

end Choice

/-- **The cost analysis of Theorem 19**, for every choice of the parameters: the time is `O(κ
n^{3-η/18} Λ)`.  The left side is the bound of Theorem 17: the number `4ng` of instances times the
cost `a n² X/D^{2η}` of one instance, plus `b` times the three terms of the additional time (with
Strassen's exponent).  `a` and `b` stand for the constants hidden in the two `O(·)`, `X` is the
logarithmic factor in the cost of one instance, and `Λ` the one in the result.  `κ` is the exponent
in the bound on the weights, the paper's ν; the paper hides it in the `O(·)`.  The constant `C`
depends only on `c` and `η` and is chosen before `n` and `D`, which is why `c ≥ 0` is asked for
separately. -/
theorem exists_total_le {c : ℝ} (hc : 0 ≤ c) (η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n D : ℕ}, Choice n D η c → ∀ {a b κ X Λ : ℝ}, 0 ≤ a → 0 ≤ b → 1 ≤ κ →
      0 ≤ X → X ≤ Λ → Real.log n ≤ Λ →
      4 * (n : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ) * (a * ((n : ℝ) ^ 2 * X / (D : ℝ) ^ (2 * η)))
        + b * (termScans n ⌈(D : ℝ) ^ η⌉₊ κ + termPrime strassen n D + termBuild n D ⌈(D : ℝ) ^ η⌉₊)
        ≤ C * ((a + b) * (κ * ((n : ℝ) ^ (3 - η / 18) * Λ))) := by
  have hcη : 0 ≤ c ^ η := Real.rpow_nonneg hc η
  refine ⟨8 * c ^ η + 3, by positivity, fun {n D} P {a b κ X Λ} ha hb hκ hX hXΛ hlogΛ => ?_⟩
  -- The scans carry the factor `κ`.  The other three terms are bounded with the logarithmic factor
  -- `κ Λ`, which is at least `Λ`, hence at least `X` and 1.
  have hΛ : 1 ≤ Λ := P.one_le_log.trans hlogΛ
  have hΛκ : Λ ≤ κ * Λ := le_mul_of_one_le_left (zero_le_one.trans hΛ) hκ
  have hinstances := P.instances_le hX (hXΛ.trans hΛκ)
  have hscans := P.scans_le (zero_le_one.trans hκ) hlogΛ
  have hstrassen := P.strassen_le (hΛ.trans hΛκ)
  have hbuild := P.build_le (hΛ.trans hΛκ)
  set R := (n : ℝ) ^ (3 - η / 18) * (κ * Λ) with hR
  have hR0 : 0 ≤ R := by positivity
  have hcηR : 0 ≤ c ^ η * R := mul_nonneg hcη hR0
  rw [show κ * (c ^ η * ((n : ℝ) ^ (3 - η / 18) * Λ)) = c ^ η * R by rw [hR]; ring] at hscans
  -- Now `hinstances` bounds the instances by `8 c^η R`, `hscans` the scans by `c^η R`,
  -- `hstrassen` the choice of `p` by `R`, and `hbuild` the building by `2 R`.
  calc _ = a * (4 * (n : ℝ) * (⌈(D : ℝ) ^ η⌉₊ : ℝ) * ((n : ℝ) ^ 2 * X / (D : ℝ) ^ (2 * η)))
        + b * (termScans n ⌈(D : ℝ) ^ η⌉₊ κ + termPrime strassen n D
          + termBuild n D ⌈(D : ℝ) ^ η⌉₊) := by ring
    _ ≤ a * ((8 * c ^ η + 3) * R) + b * ((8 * c ^ η + 3) * R) := by
        gcongr a * ?_ + b * ?_
        · linarith [hinstances, hR0]
        · linarith [hscans, hstrassen, hbuild, hcηR]
    _ = (8 * c ^ η + 3) * ((a + b) * (κ * ((n : ℝ) ^ (3 - η / 18) * Λ))) := by
        rw [hR]
        ring

end Theorem19

end ThreeSumApsp

end
end

section


/-!
# Theorem 19 and Remark 20: Exact Triangle in truly subcubic time (Section 3.3)

Theorem 19 applies the reduction of Theorem 17 with `D` about `n^{1/18}` and `g = ⌈D^η⌉`, and solves
each instance by a corollary of Section 3.1: by Corollary 15 with `η = 1/36`, where `D` is the
largest power of four with `D ≤ n^{1/18}`, and by Corollary 16 with `η = 0.0315`, where
`D = ⌊n^{1/18}⌋`.  This file has the arithmetic of the proof.  The deduction of the running time
from Theorem 17 that uses it is `Theorem19.explicit_of_theorem_17_corollary_15` and
`Theorem19.explicit_of_theorem_17_corollary_16`, and the theorem about programs is
`wordRam_theorem_19`.

1. Both choices of the parameters, `paramD₅` with `paramG₅` and `paramD₂₆` with `paramG₂₆`, are a
   `Theorem19.Choice` (`Theorem19.choice_theorem_5`, `Theorem19.choice_corollary_26`).  So they
   satisfy the hypotheses of Theorem 17 and of the two corollaries (`Choice.sixteen_le`,
   `Choice.le_n`, `Choice.one_le_ceil`, `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. By the cost analysis for a general choice (`Theorem19.exists_total_le`), the number of instances
   times the cost of one instance, plus the additional time of Theorem 17, is
   `O(n^{3-1/648} log² n)`, respectively `O(n^{3-0.00175} log n)` (`Theorem19.total_theorem_5`,
   `Theorem19.total_corollary_26`).  The step "O(n^{3−ε'} log n) ≤ O(n^{3−ε_T})" of the
   statement is the general fact that a larger exponent absorbs logarithms
   (`IsPowPolylog.isBigOPow`); it is applied in `Theorem19.second_of_explicit`.

NOTE.  "Assume n is larger than a constant depending on ν": the two choices of `D` below are stated
for `n ≥ 16^18`, which makes `D ≥ 16`.

Remark 20 explains the values of `η`: the exponents `η - γ` of the instances and `-η` of the scans
balance at `η = γ/2` (`remark_20_balance`, `remark_20_numbers`), and the straightforward algorithm
for the instances gives back the bound `n³` (`remark_20_brute_force`).
-/

public section

namespace ThreeSumApsp

/-! ### The two choices of the parameters -/











































/-- Proof of Theorem 19, by Corollary 26: "Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉", and
"D ≥ n^{1/18}/2". -/
theorem Theorem19.choice_corollary_26 {n : ℕ} (hn : 16 ^ 18 ≤ n) :
    Theorem19.Choice n (paramD₂₆ n) 0.0315 2 where
  sixteen_le := Nat.le_floor (by exact_mod_cast Theorem19.sixteen_le_root hn)
  le_root := Nat.floor_le (by positivity)
  root_div_le := by
    -- With `r = n^{1/18} ≥ 16`: `D > r - 1 ≥ r/2`.
    have hlt : (n : ℝ) ^ (1 / 18 : ℝ) < (paramD₂₆ n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith [Theorem19.sixteen_le_root hn, hlt]
  c_pos := by norm_num
  η_nonneg := by norm_num
  η_le := by norm_num

/-! ### The costs added up -/























/-- **Theorem 19, second bound**, the costs added up: "so the time is O(n^{3−ε'} log n)",
`ε' = 0.00175`.  The letters are as in `Theorem19.total_theorem_5`, with Corollary 16 in place of
Corollary 15. -/
theorem Theorem19.total_corollary_26 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 16 ^ 18 ≤ n → ∀ {a b κ : ℝ}, 0 ≤ a → 0 ≤ b → 1 ≤ κ →
      4 * (n : ℝ) * (paramG₂₆ n : ℝ) * (a * ((n : ℝ) ^ 2 / (paramD₂₆ n : ℝ) ^ (0.063 : ℝ)))
        + b * (termScans n (paramG₂₆ n) κ + termPrime strassen n (paramD₂₆ n)
          + termBuild n (paramD₂₆ n) (paramG₂₆ n))
        ≤ C * ((a + b) * (κ * ((n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n))) := by
  obtain ⟨C, hC, htotal⟩ := Theorem19.exists_total_le (c := 2) (by norm_num) 0.0315
  refine ⟨C, hC, fun {n} hn {a b κ} ha hb hκ => ?_⟩
  have P := Theorem19.choice_corollary_26 hn
  -- The cost of one instance has no logarithmic factor: `X = 1 ≤ log n`.
  have h := htotal P ha hb hκ zero_le_one P.one_le_log le_rfl
  rwa [mul_one, show (2 * 0.0315 : ℝ) = 0.063 by norm_num,
    show (3 - 0.0315 / 18 : ℝ) = 3 - 0.00175 by norm_num] at h

/-! ### Remark 20 -/









































end ThreeSumApsp

end
end

section


/-!
# Theorem 19 from Theorem 17 and Corollaries 15 and 16

Theorem 17 reduces Exact Triangle to `4 n g` calls of Lop-AE-SparseTri plus some extra time.  The
proof of Theorem 19 puts in the cost of one call (Corollary 15 or Corollary 16) and the parameters
`D` and `g`, and adds up.  Both routes have the same three steps:

1. the parameters satisfy the hypotheses of Theorem 17 and of the corollary (`Theorem19.choice_*`);
2. one call, with the reading of its answers, costs `O(I)` (`call_cost_corollary_15` and
   `call_cost_corollary_16`);
3. the sum of all terms is `O(κ P)` (`Theorem19.total_*`, the calculation of the proof of
   Theorem 19).

`time_le_of_calls` puts the three steps together.  The result keeps the dependence on `κ`
(`Claim.Theorem_19_explicit`).  From it follow the two bounds as printed, for every constant `κ`
(`Claim.Theorem_19_explicit.eventually_le`), and a bound for all sizes and all bounds on the
weights, which is what Theorem 21 is applied to (`exactTriangleUniform_of_explicit`): small sizes by
brute force (`dominated_bruteForce`), large sizes by the explicit bound with
`κ = max 1 (log u / log s)` (`dominated_explicit`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- **How both routes of Theorem 19 end.**  Theorem 17 bounds the time by
`calls · call + C · extra`.  If one call costs at most `c I`, and if the calculation of the proof of
Theorem 19 bounds `calls · c I + C · extra` by `B`, then the time is at most `B`. -/
theorem time_le_of_calls {T calls call I extra B C c : ℝ}
    (h17 : T ≤ calls * call + C * extra) (hcall : call ≤ c * I)
    (hsum : calls * (c * I) + C * extra ≤ B) (hcalls : 0 ≤ calls) : T ≤ B :=
  (h17.trans (add_le_add (mul_le_mul_of_nonneg_left hcall hcalls) le_rfl)).trans hsum

/-- One call on the route through Corollary 16, with the reading of its answers, costs
`O(n²/D^{0.063})`: an instance has `|W| ≤ n²/√D` query pairs, so `|W| D^{0.437} ≤ n²/D^{0.063}`. -/
theorem call_cost_corollary_16 {n D : ℕ} {t C C₁₆ : ℝ} (hD : 1 ≤ D) (hC : 0 ≤ C) (hC₁₆ : 0 ≤ C₁₆)
    (ht : t ≤ C₁₆ * wantedBound n D (queryCap n D)) :
    t + C * ((n : ℝ) ^ 2 / Real.sqrt D)
      ≤ (2 * C₁₆ + C) * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hpos₁ : 0 < (D : ℝ) ^ (0.437 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hpos₂ : 0 < (D : ℝ) ^ (0.063 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hsqrt : Real.sqrt D = (D : ℝ) ^ (0.437 : ℝ) * (D : ℝ) ^ (0.063 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD0]
    norm_num
  have hquery : (queryCap n D : ℝ) * (D : ℝ) ^ (0.437 : ℝ)
      ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) :=
    calc (queryCap n D : ℝ) * (D : ℝ) ^ (0.437 : ℝ)
        ≤ (n : ℝ) ^ 2 / Real.sqrt D * (D : ℝ) ^ (0.437 : ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hpos₁.le
      _ = (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) := by
          rw [hsqrt]
          field_simp
  have hread := sq_div_sqrt_le_sq_div_rpow n hD (a := 0.063) (by norm_num)
  calc t + C * ((n : ℝ) ^ 2 / Real.sqrt D)
      ≤ C₁₆ * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) + (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ))
          + C * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) :=
        add_le_add (ht.trans (mul_le_mul_of_nonneg_left (add_le_add hquery le_rfl) hC₁₆))
          (mul_le_mul_of_nonneg_left hread hC)
    _ = (2 * C₁₆ + C) * ((n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) := by ring

































/-- The deduction "By Corollary 26" in the proof of Theorem 19: from Theorem 17 (with
Strassen's algorithm) and Corollary 16, with `D = ⌊n^{1/18}⌋` and `g = ⌈D^{0.0315}⌉`. -/
theorem Theorem19.explicit_of_theorem_17_corollary_16 (M : DetTimeModel)
    (h17 : Claim.Theorem_17 M strassen paramD₂₆ paramG₂₆)
    (h16 : Claim.Corollary_16 M) : Claim.Theorem_19_explicit M 0.00175 1 := by
  obtain ⟨C, hC, h17⟩ := h17
  obtain ⟨C₁₆, _, Td, hC₁₆, -, hTd, h16⟩ := h16
  obtain ⟨T, hT, h17⟩ := h17 Td hTd
  obtain ⟨C₀, -, htotal⟩ := Theorem19.total_corollary_26
  refine ⟨C₀ * (2 * C₁₆ + C + C), T, hT, fun n κ u hn hκ hu => ?_⟩
  -- Step 1: the parameters.
  have P := Theorem19.choice_corollary_26 hn
  have hD16 := P.sixteen_le
  have h17 := h17 n κ u hD16 P.le_n P.one_le_ceil P.ceil_le_sqrt hκ hu
  -- Step 2: one call.
  have hcall := call_cost_corollary_16 (by omega) hC hC₁₆
    (h16 n _ (queryCap n (paramD₂₆ n)) (by omega) P.pow_eighteen_le).2
  -- Step 3: the sum of the proof of Theorem 19.
  have hsum := htotal hn (a := 2 * C₁₆ + C) (b := C) (by positivity) hC hκ
  rw [pow_one]
  exact (time_le_of_calls h17 hcall hsum (by positivity)).trans_eq (by ring)

/-! ## The bounds as printed -/





































/-! ## A bound for all sizes and all bounds on the weights -/












/-- Each of the three factors of `uniformShape` is at least 1. -/
private theorem one_le_uniformShape {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1) {p : SizeBound} (hs : 1 ≤ p.s) :
    1 ≤ uniformShape δ e p :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (Nat.one_le_cast.2 hs) (by linarith)) (one_le_log_add_one_pow p.s e))
    (one_le_pow₀ (one_le_one_add_logU p.u))

/-- "Smaller instances are solved by brute force": below a fixed size `n₀`, the time
`s³ (1 + log u)` is `O(s^{3-δ} (log s + 1)^e (1 + log u)²)`, because `s^δ ≤ n₀^δ`. -/
private theorem dominated_bruteForce {δ : ℝ} (e n₀ : ℕ) (hδ0 : 0 ≤ δ) :
    Dominated (fun p : SizeBound => (1 ≤ p.s ∧ 1 ≤ p.u) ∧ p.s < n₀)
      (fun p => (p.s : ℝ) ^ 3 * (1 + logU p.u)) (uniformShape δ e) := by
  refine .of_le_const_mul (C := (n₀ : ℝ) ^ δ) (by positivity) fun p hp => ?_
  have hlog := one_le_log_add_one_pow p.s e
  have hwords := one_le_one_add_logU p.u
  have hs0 : (0 : ℝ) < p.s := Nat.cast_pos.2 hp.1.1
  have hsplit : (p.s : ℝ) ^ 3 = (p.s : ℝ) ^ δ * (p.s : ℝ) ^ (3 - δ) := by
    rw [← Real.rpow_add hs0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hsmall : (p.s : ℝ) ^ δ ≤ (n₀ : ℝ) ^ δ :=
    Real.rpow_le_rpow hs0.le (Nat.cast_le.2 hp.2.le) hδ0
  calc (p.s : ℝ) ^ 3 * (1 + logU p.u)
      = (p.s : ℝ) ^ δ * ((p.s : ℝ) ^ (3 - δ) * 1 * (1 + logU p.u) ^ 1) := by rw [hsplit]; ring
    _ ≤ (n₀ : ℝ) ^ δ * ((p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e * (1 + logU p.u) ^ 2) := by
        gcongr
        norm_num

/-- Weights up to `u` are weights up to `s^κ` for `κ = max 1 (log u / log s)`. -/
private theorem le_rpow_max_log_div {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    u ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) := by
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.2 (by omega)
  have hlogs : 1 ≤ Real.log s := Real.one_le_log_natCast_of_three_le hs
  calc u = (s : ℝ) ^ (Real.log u / Real.log s) := by
        rw [Real.rpow_def_of_pos hs0, mul_div_cancel₀ _ (by linarith),
          Real.exp_log (zero_lt_one.trans_le hu)]
    _ ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) :=
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (by omega)) (le_max_right _ _)

/-- The exponent `max 1 (log u / log s)` is at most `1 + log u`. -/
private theorem max_log_div_le {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    max 1 (Real.log u / Real.log s) ≤ 1 + logU u := by
  refine max_le (one_le_one_add_logU u) ?_
  linarith [div_le_self (Real.log_nonneg hu) (Real.one_le_log_natCast_of_three_le hs),
    log_le_logU (zero_lt_one.trans_le hu)]

/-- From the size `16^18` on: the explicit bound of Theorem 19 with `κ = max 1 (log u / log s)`. -/
private theorem dominated_explicit {T : ℕ → ℝ → ℝ} {K δ : ℝ} {e : ℕ}
    (hb : ∀ (n : ℕ) (κ u : ℝ), 16 ^ 18 ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))) :
    Dominated (fun p : SizeBound => (1 ≤ p.s ∧ 1 ≤ p.u) ∧ ¬ p.s < 16 ^ 18) (fun p => T p.s p.u)
      (uniformShape δ e) := by
  have h3 : ∀ p : SizeBound, ¬ p.s < 16 ^ 18 → 3 ≤ p.s := fun p hp =>
    (by norm_num : 3 ≤ 16 ^ 18).trans (not_lt.1 hp)
  refine (Dominated.of_exists_const (g := fun p => max 1 (Real.log p.u / Real.log p.s) *
    ((p.s : ℝ) ^ (3 - δ) * Real.log p.s ^ e)) ⟨K, fun p hp => ?_⟩ fun p _ => ?_).trans
    (.of_le fun p hp => ?_)
  · exact hb p.s _ p.u (not_lt.1 hp.2) (le_max_left _ _) (le_rpow_max_log_div (h3 p hp.2) hp.1.2)
  · positivity
  · have hκ := max_log_div_le (h3 p hp.2) hp.1.2
    have hlog := Real.log_natCast_nonneg p.s
    have hwords := le_self_pow₀ (one_le_one_add_logU p.u) two_ne_zero
    calc max 1 (Real.log p.u / Real.log p.s) * ((p.s : ℝ) ^ (3 - δ) * Real.log p.s ^ e)
        ≤ (1 + logU p.u) ^ 2 * ((p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e) := by
          gcongr
          · exact hκ.trans hwords
          · linarith
      _ = uniformShape δ e p := by ring

/-- From the explicit form of Theorem 19, brute force for small instances
("smaller instances are solved by brute force") and two closure properties: Exact Triangle in time
`K s^{3-δ} (log s + 1)^e (1 + log u)²` for all `s` and `u`.

NOTE.  This step is not in the paper; see `Claim.ExactTriangleUniform` for why our rendering of
"Plug Theorem 19 into Theorem 21" needs it. -/
theorem exactTriangleUniform_of_explicit (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hex : Claim.Theorem_19_explicit M δ e) (hbf : Claim.BruteForce M)
    (hch : Closure.ChooseBySize M) (hmono : Closure.MonoExactTriangle M) :
    Claim.ExactTriangleUniform M δ e := by
  obtain ⟨K, T, hT, hb⟩ := hex
  obtain ⟨C, hbf⟩ := hbf
  obtain ⟨C₀, hch⟩ := hch (16 ^ 18)
  have hshape : ∀ p : SizeBound, 1 ≤ p.s ∧ 1 ≤ p.u → 1 ≤ uniformShape δ e p := fun p hp =>
    one_le_uniformShape e hδ1 hp.1
  have hsmall := (dominated_bruteForce e (16 ^ 18) hδ0).const_mul_of_nonneg C fun p _ =>
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_one_add_logU p.u))
  obtain ⟨K', hK'0, hK'⟩ := (Dominated.ite hsmall (dominated_explicit hb) fun p hp =>
    zero_le_one.trans (hshape p hp)).add (.const C₀ hshape)
  refine ⟨1 + K', le_add_of_nonneg_right hK'0,
    hmono _ _ (fun s u hs hu => ?_) (hch _ T hbf hT)⟩
  exact (hK' ⟨s, u⟩ ⟨hs, hu⟩).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
    (zero_le_one.trans (hshape ⟨s, u⟩ ⟨hs, hu⟩)))

end ThreeSumApsp

end
end

section


/-! Reuse of the original parameter and exponent analysis for the new output task. -/

namespace APSPImprovement.AllEdges

open Light ThreeSumApsp ThreeSumApsp.Spec

/-- The same proved sparse-triangle algorithm is the oracle for the new host. -/
theorem corollary16_allEdgesModel : Claim.Corollary_16 allEdgesModel :=
  Light.Sec3.claim_corollary_16

/-- Once the all-edges host obeys Theorem 17, its exponent is exactly the source's
`3 - 0.00175`, without the old decision-to-all-pairs loss of a factor of three. -/
theorem explicit_of_allEdges_host
    (h17 : Claim.Theorem_17 allEdgesModel strassen paramD₂₆ paramG₂₆) :
    Claim.Theorem_19_explicit allEdgesModel 0.00175 1 :=
  Theorem19.explicit_of_theorem_17_corollary_16 _ h17 corollary16_allEdgesModel

/-- Precise uniform interface consumed by the same-size all-edges reductions.
The three premises are explicit algorithm obligations, not assumptions hidden in
the model: the new host, its small-size fallback and a verified size-based choice. -/
theorem uniform_of_allEdges_host
    (h17 : Claim.Theorem_17 allEdgesModel strassen paramD₂₆ paramG₂₆)
    (hbrute : Claim.BruteForce allEdgesModel) (hchoose : Closure.ChooseBySize allEdgesModel) :
    ∃ K : ℝ, 1 ≤ K ∧ SolvedIn allEdgesTask (uniformTime K 0.00175 1) := by
  exact exactTriangleUniform_of_explicit allEdgesModel 1 (by norm_num) (by norm_num)
    (explicit_of_allEdges_host h17) hbrute hchoose mono_allEdges

/-- The actual small-case algorithm and size selector discharge their obligations.
Only the large-case all-edges Theorem 17 host remains as an explicit premise. -/
theorem uniform_from_host
    (h17 : Claim.Theorem_17 allEdgesModel strassen paramD₂₆ paramG₂₆) :
    ∃ K : ℝ, 1 ≤ K ∧ SolvedIn allEdgesTask (uniformTime K 0.00175 1) :=
  uniform_of_allEdges_host h17 claim_bruteForce closure_chooseBySize

end APSPImprovement.AllEdges




end

section


/-!
# Reading the answers of one instance and scanning for witnesses

Proof of Theorem 17: "For every query pair that the oracle accepts, scan the piece C_k of its
instance for a c with S(a,b,c) = 0 [...].  We stop as soon as a zero triangle is found."

scanPairs(out, qa, qb, w, f, ab, bc, ac, n, c0, len): for every query pair number `i < w` whose
answer `out[i]` is not 0, scan the piece `{c0, …, c0 + len - 1}` for a zero triangle through the
pair `(qa[i], qb[i])`, as long as none has been found (`f = 0`).  The result is the new value of `f`
(`scanPairs_spec`).  No scan is made after the first successful one, so the number of scans is at
most the number of failed scans plus one (`execsUpto_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

















theorem foundAt_zero (acc hit : ℕ → Bool) (f : Bool) : foundAt acc hit f 0 = f := by simp [foundAt]

theorem foundAt_succ (acc hit : ℕ → Bool) (f : Bool) (i : ℕ) :
    foundAt acc hit f (i + 1) = (foundAt acc hit f i || (acc i && hit i)) := by
  simp [foundAt, List.range_succ, Bool.or_assoc]

theorem execsUpto_succ (acc hit : ℕ → Bool) (f : Bool) (w : ℕ) :
    execsUpto acc hit f (w + 1) =
      execsUpto acc hit f w + (if execAt acc hit f w then 1 else 0) := by
  simp only [execsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

theorem failsUpto_succ (acc hit : ℕ → Bool) (w : ℕ) :
    failsUpto acc hit (w + 1) = failsUpto acc hit w + (if acc w && !hit w then 1 else 0) := by
  simp only [failsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

/-- **All scans but one fail.** -/
theorem execsUpto_le (acc hit : ℕ → Bool) (f : Bool) (w : ℕ) :
    execsUpto acc hit f w + f.toNat ≤ failsUpto acc hit w + (foundAt acc hit f w).toNat := by
  induction w with
  | zero => simp [execsUpto, failsUpto, foundAt_zero]
  | succ w ih =>
    rw [execsUpto_succ, failsUpto_succ, foundAt_succ, execAt]
    rcases ha : acc w <;> rcases hh : hit w <;> rcases hf : foundAt acc hit f w <;>
      simp [hf] at ih ⊢ <;> omega

/-! ## The routine -/

namespace ScanPairs

















end ScanPairs



































section

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w ab bc ac n c0 len U : ℕ} {OUT AB BC AC : List ℤ}
  {QA QB : List ℕ} {f : Bool}

































































































end

end Light.Sec3

end
end

section


/-!
# The table of the chunks (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p), and cut it into
chunks of at most n²/√D query pairs."  The routine lists the pairs class after class (`sortedIdx`).
Then a class is a segment of the list, from `classStart ϱ` to `classStart (ϱ + 1)`, and a chunk is a
segment of a class.  The table `chunkTab` has one entry for each chunk: its residue, the place where
it starts, and its number of pairs.

* The list has every pair once (`sortedIdx_nodup`, `classStart_eq_sq`), and the places of a class
  hold pairs of that class (`getD_sortedIdx_class`).
* An entry of the table is a nonempty segment of at most `cap` places (`chunkTab_entry`) whose pairs
  have the residue of the entry (`chunkTab_class`).
* The chunks follow each other (`chunkTab_pairwise`), so every place lies in exactly one chunk
  (`chunkTab_cover`, `chunkTab_unique`).
* "There are at most p + √D ≤ 2√D chunks in all" (`length_chunkTab_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

variable {n p cap : ℕ} {RAB : List ℕ}

/-! ## The classes and the list of all the pairs -/















/-- The places of a class. -/
theorem mem_classIdx {rho x : ℕ} : x ∈ classIdx n RAB rho ↔ x < n * n ∧ RAB.getD x 0 = rho := by
  simp [classIdx]

/-- The list holds places of pairs. -/
theorem lt_of_mem_sortedIdx {x : ℕ} (h : x ∈ sortedIdx n p RAB) : x < n * n := by
  obtain ⟨rho, -, hx⟩ := List.mem_flatMap.1 h
  exact (mem_classIdx.1 hx).1

/-- No pair is listed twice. -/
theorem sortedIdx_nodup (n p : ℕ) (RAB : List ℕ) : (sortedIdx n p RAB).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun rho _ => List.nodup_range.filter _, ?_⟩
  refine (List.nodup_range (n := p)).imp fun {a b} hab x hxa hxb => ?_
  exact hab ((mem_classIdx.1 hxa).2.symm.trans (mem_classIdx.1 hxb).2)

/-! ## The starts of the classes -/








/-- The next class starts where the class ends. -/
theorem classStart_succ (n : ℕ) (RAB : List ℕ) (rho : ℕ) :
    classStart n RAB (rho + 1) = classStart n RAB rho + (classIdx n RAB rho).length :=
  List.sum_range_succ _ _

/-- Later classes start later. -/
theorem classStart_mono (n : ℕ) (RAB : List ℕ) {a b : ℕ} (h : a ≤ b) :
    classStart n RAB a ≤ classStart n RAB b :=
  List.sum_map_range_mono _ h

/-- The list `classStarts` holds the starts of the classes. -/
theorem getD_classStarts_eq (n p : ℕ) (RAB : List ℕ) {rho : ℕ} (h : rho ≤ p) :
    (classStarts n p RAB).getD rho 0 = classStart n RAB rho :=
  List.getD_map_range _ (Nat.lt_succ_of_le h) 0

/-- The list of all the pairs ends where the class `p` would start. -/
theorem length_sortedIdx_eq (n p : ℕ) (RAB : List ℕ) :
    (sortedIdx n p RAB).length = classStart n RAB p :=
  List.length_flatMap

/-- The class `p` starts after the pairs with a residue below `p`. -/
theorem classStart_eq_length_filter (n : ℕ) (RAB : List ℕ) (p : ℕ) :
    classStart n RAB p =
      ((List.range (n * n)).filter fun i => decide (RAB.getD i 0 < p)).length := by
  induction p with
  | zero => simp [classStart]
  | succ p ih =>
    rw [classStart_succ, ih, List.length_filter_lt_succ fun i => RAB.getD i 0]
    rfl

/-- All the pairs are listed if all the residues are below `p`. -/
theorem classStart_eq_sq (hlt : ∀ i < n * n, RAB.getD i 0 < p) : classStart n RAB p = n * n := by
  rw [classStart_eq_length_filter, List.filter_eq_self.2, List.length_range]
  exact fun i hi => decide_eq_true (hlt i (List.mem_range.1 hi))












/-- The places from the start of the class `rho` to the start of the next class hold pairs with the
residue `rho`. -/
theorem getD_sortedIdx_class {rho j : ℕ} (hrho : rho < p) (hlo : classStart n RAB rho ≤ j)
    (hhi : j < classStart n RAB (rho + 1)) : RAB.getD ((sortedIdx n p RAB).getD j 0) 0 = rho := by
  rw [classStart_succ] at hhi
  obtain ⟨o, rfl⟩ := Nat.exists_eq_add_of_le hlo
  have ho : o < (classIdx n RAB rho).length := by omega
  rw [sortedIdx, classStart, List.getD_flatMap_range_sum _ hrho ho, List.getD_eq_getElem _ 0 ho]
  exact (mem_classIdx.1 (List.getElem_mem ho)).2

/-! ## The chunks -/






































/-- The table, in terms of the starts of the classes. -/
theorem chunkTab_eq (n p cap : ℕ) (RAB : List ℕ) :
    chunkTab n p cap RAB = (List.range p).flatMap fun rho =>
      (List.range ((classIdx n RAB rho).length ⌈/⌉ cap)).map (chunkAt n cap RAB rho) := by
  unfold chunkTab chunkTabOf
  refine List.flatMap_congr fun rho hrho => ?_
  have h := List.mem_range.1 hrho
  rw [getD_classStarts_eq n p RAB (by omega), getD_classStarts_eq n p RAB (by omega), chunksOf,
    classStart_succ, Nat.add_sub_cancel_left]
  rfl

/-- The entries of the table: chunk number `i` of the class `rho`. -/
theorem mem_chunkTab (x : Chunk) :
    x ∈ chunkTab n p cap RAB ↔
      ∃ rho < p, ∃ i < (classIdx n RAB rho).length ⌈/⌉ cap, x = chunkAt n cap RAB rho i := by
  simp only [chunkTab_eq, List.mem_flatMap, List.mem_range, List.mem_map, eq_comm (a := x)]

/-- An entry of the table has a residue below `p`, and it is a nonempty segment of at most `cap`
places of the list. -/
theorem chunkTab_entry (hcap : 1 ≤ cap) (hlt : ∀ i < n * n, RAB.getD i 0 < p) {x : Chunk}
    (hx : x ∈ chunkTab n p cap RAB) : x.Fits n p cap := by
  obtain ⟨rho, hrho, i, hi, rfl⟩ := (mem_chunkTab x).1 hx
  have hleft := (Nat.lt_ceilDiv_iff hcap).1 hi
  have hend := classStart_mono n RAB (show rho + 1 ≤ p by omega)
  rw [classStart_succ, classStart_eq_sq hlt] at hend
  constructor <;> simp only [chunkAt] <;> omega

/-- The pairs of a chunk have the residue of its entry. -/
theorem chunkTab_class (hcap : 1 ≤ cap) {x : Chunk} (hx : x ∈ chunkTab n p cap RAB) {i : ℕ}
    (hi : i < x.len) : RAB.getD ((sortedIdx n p RAB).getD (x.start + i) 0) 0 = x.residue := by
  obtain ⟨rho, hrho, i', hi', rfl⟩ := (mem_chunkTab x).1 hx
  have hleft := (Nat.lt_ceilDiv_iff hcap).1 hi'
  simp only [chunkAt] at hi ⊢
  exact getD_sortedIdx_class hrho (by omega) (by rw [classStart_succ]; omega)








































/-- A place lies in one chunk only. -/
theorem chunkTab_unique (hcap : 1 ≤ cap) {j k k' : ℕ} (h : k < (chunkTab n p cap RAB).length)
    (h' : k' < (chunkTab n p cap RAB).length) (hj : (chunkTab n p cap RAB)[k].Contains j)
    (hj' : (chunkTab n p cap RAB)[k'].Contains j) : k = k' := by
  have hpair := List.pairwise_iff_getElem.1 (chunkTab_pairwise (n := n) (p := p) (RAB := RAB) hcap)
  obtain ⟨hlo, hhi⟩ := hj
  obtain ⟨hlo', hhi'⟩ := hj'
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := hpair k k' h h' hlt
    omega
  · exact heq
  · have := hpair k' k h' h hgt
    omega

/-- The number of chunks, class by class. -/
theorem length_chunkTab (n p cap : ℕ) (RAB : List ℕ) :
    (chunkTab n p cap RAB).length =
      ((List.range p).map fun rho => (classIdx n RAB rho).length ⌈/⌉ cap).sum := by
  rw [chunkTab_eq, List.length_flatMap]
  simp




















end ThreeSumApsp.Spec

end
end

section


/-!
# The host of Theorem 17: what is true of the list of its instances

Proof of Theorem 17.  A `HostData` describes the instances that the host forms after the prime has
been chosen, the answers of the solver, and the scans.  This file proves, without any program in
sight:

* the instances are well formed: pieces, chunks, query pairs and matrices have the sizes that the
  solver asks for (`Valid.piece_le`, `Valid.lo_add_le`, `Valid.length_WI`, `length_matX`, …);
* the query pair number `i` of instance `t` is `(rowOf t i, colOf t i)`, read off its place
  `a n + b` (`getD_WI`, `getD_WJ`), which is the entry at position `lo t + i` of the list of all
  pairs; every pair meets every vertex of `C` in some instance (`Valid.exists_query`);
* a query pair `(a, b)` is accepted if and only if the piece has a vertex `c` with `p ∣ S(a,b,c)`,
  where `S(a,b,c) = w(a,b) + w(b,c) + w(a,c)` is `sumAt` (`acc_iff`), and its scan succeeds if and
  only if the piece has a `c` with `S(a,b,c) = 0` (`hit_iff`);
* a zero triangle is found if and only if there is one (`found_m`; for the reduction on finite sets,
  of which `theorem_17` speaks, the same sentence is `TriangleInstance.exists_mem_acceptedPairs`,
  and neither proof uses the other);
* all scans but one fail (`sum_execs_le`);
* the parameters of Theorem 17 give valid data (`valid_of_params`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostData













variable {X : HostData}

/-! ## Residues, pieces and chunks -/

/-- The prime is not 0. -/
theorem Valid.p_ne (hv : X.Valid) : X.p ≠ 0 := Nat.ne_of_gt hv.p_pos

/-- All residues are below `p`. -/
theorem Valid.rab_lt (hv : X.Valid) (i : ℕ) : X.RAB.getD i 0 < X.p := by
  rw [RAB, getD_residList]
  exact resid_lt hv.p_ne _

/-- The list of all pairs has `n²` entries. -/
theorem Valid.length_sortedIdx (hv : X.Valid) : (sortedIdx X.n X.p X.RAB).length = X.n * X.n := by
  rw [length_sortedIdx_eq, classStart_eq_sq fun i _ => hv.rab_lt i]

/-- The number `t / chunkCount` of the piece of an instance `t < m` is below the number of pieces.
-/
theorem div_chunkCount_lt {t : ℕ} (ht : t < X.m) : t / X.chunkCount < X.h :=
  Nat.div_lt_of_lt_mul' ht

/-- The number `t % chunkCount` of the chunk of an instance `t < m` is below the number of chunks.
-/
theorem mod_chunkCount_lt {t : ℕ} (ht : t < X.m) : t % X.chunkCount < X.chunkCount :=
  Nat.mod_lt_of_lt_mul ht

/-- The chunk of an instance is an entry of the table of the chunks. -/
theorem chunk_mem {t : ℕ} (ht : t < X.m) : X.chunk t ∈ chunkTab X.n X.p X.cap X.RAB := by
  rw [chunk, List.getD_eq_getElem _ _ (mod_chunkCount_lt ht)]
  exact List.getElem_mem _

/-- The residue of a chunk is below `p`; a chunk has between 1 and `cap` pairs, and it ends within
the list of all pairs. -/
theorem Valid.chunk_entry (hv : X.Valid) {t : ℕ} (ht : t < X.m) :
    (X.chunk t).Fits X.n X.p X.cap :=
  chunkTab_entry hv.cap_pos (fun i _ => hv.rab_lt i) (chunk_mem ht)

/-- The residue of a chunk is below `p`. -/
theorem Valid.rho_lt (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.rho t < X.p :=
  (hv.chunk_entry ht).residue_lt

/-- A chunk has at most `cap` pairs. -/
theorem w_le_cap (X : HostData) {t : ℕ} (ht : t < X.m) : X.w t ≤ X.cap := by
  obtain ⟨rho, -, i, -, h⟩ := (mem_chunkTab _).1 (chunk_mem ht)
  rw [w, h]
  exact Nat.min_le_left _ _

/-- A chunk ends within the list of all pairs. -/
theorem Valid.lo_add_le (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.lo t + X.w t ≤ X.n * X.n :=
  (hv.chunk_entry ht).end_le

/-- A piece starts below `n`. -/
theorem Valid.c0_lt (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.c0 t < X.n :=
  (Nat.lt_ceilDiv_iff hv.q_pos).1 (div_chunkCount_lt ht)

/-- A piece has at most `q` vertices. -/
theorem len_le (X : HostData) (t : ℕ) : X.len t ≤ X.q := Nat.min_le_left _ _

/-- A piece ends within `C`. -/
theorem Valid.piece_le (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.c0 t + X.len t ≤ X.n := by
  have := hv.c0_lt ht
  rw [len]
  omega

/-- A piece with its labels fits into the middle part. -/
theorem Valid.len_mul_le (hv : X.Valid) (t : ℕ) : X.len t * X.p ≤ X.D :=
  (Nat.mul_le_mul_right _ (X.len_le t)).trans hv.qp_le

/-! ## The query pairs of an instance -/











/-- The rows of the query pairs, as the host lists them. -/
theorem getD_WI {t i : ℕ} (hi : i < X.w t) : (X.WI t).getD i 0 = X.rowOf t i := by
  rw [WI, List.getD_take_of_lt _ hi, List.getD_drop, QI, queryRows, rowOf, place]
  simpa using List.getD_map (l := sortedIdx X.n X.p X.RAB) (d := 0) (n := X.lo t + i) (· / X.n)

/-- The columns of the query pairs, as the host lists them. -/
theorem getD_WJ {t i : ℕ} (hi : i < X.w t) : (X.WJ t).getD i 0 = X.colOf t i := by
  rw [WJ, List.getD_take_of_lt _ hi, List.getD_drop, QJ, queryCols, colOf, place]
  simpa using List.getD_map (l := sortedIdx X.n X.p X.RAB) (d := 0) (n := X.lo t + i) (· % X.n)

/-- A place is below `n²`. -/
theorem Valid.place_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.place t i < X.n * X.n := by
  have hend := hv.lo_add_le ht
  have hlen := hv.length_sortedIdx
  rw [place, List.getD_eq_getElem _ _ (by omega)]
  exact lt_of_mem_sortedIdx (List.getElem_mem _)

/-- The row of a query pair is a vertex of `A`. -/
theorem Valid.rowOf_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.rowOf t i < X.n := Nat.div_lt_of_lt_mul' (hv.place_lt ht hi)

/-- The column of a query pair is a vertex of `B`. -/
theorem Valid.colOf_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.colOf t i < X.n := Nat.mod_lt_of_lt_mul (hv.place_lt ht hi)

/-- The pair gives the place back. -/
theorem rowOf_mul_add_colOf (X : HostData) (t i : ℕ) :
    X.rowOf t i * X.n + X.colOf t i = X.place t i := Nat.div_add_mod' _ _

/-- The weight `w(a,b)` of a query pair has the residue of its chunk. -/
theorem Valid.rab_place (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.RAB.getD (X.place t i) 0 = X.rho t := chunkTab_class hv.cap_pos (chunk_mem ht) hi

/-- The query pairs of an instance, from the places. -/
theorem zip_eq (X : HostData) (t : ℕ) :
    (X.WI t).zip (X.WJ t) =
      (((sortedIdx X.n X.p X.RAB).drop (X.lo t)).take (X.w t)).map fun s => (s / X.n, s % X.n) := by
  rw [WI, WJ, QI, QJ, queryRows, queryCols, ← List.map_drop, ← List.map_drop, ← List.map_take,
    ← List.map_take, List.zip_map']

/-- No query pair is listed twice. -/
theorem nodup_zip (X : HostData) (t : ℕ) : ((X.WI t).zip (X.WJ t)).Nodup := by
  rw [zip_eq]
  refine (((sortedIdx_nodup X.n X.p X.RAB).sublist (List.drop_sublist _ _)).sublist
    (List.take_sublist _ _)).map fun s s' h => ?_
  simp only [Prod.mk.injEq] at h
  rw [← Nat.div_add_mod s X.n, ← Nat.div_add_mod s' X.n, h.1, h.2]

/-- The rows of the query pairs are vertices of `A`. -/
theorem lt_of_mem_WI {t a : ℕ} (ha : a ∈ X.WI t) : a < X.n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  exact Nat.div_lt_of_lt_mul' (lt_of_mem_sortedIdx hs)

/-- The columns of the query pairs are vertices of `B`. -/
theorem lt_of_mem_WJ {t b : ℕ} (hb : b ∈ X.WJ t) : b < X.n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  exact Nat.mod_lt_of_lt_mul (lt_of_mem_sortedIdx hs)

/-- The list of the rows of all pairs has `n²` entries. -/
theorem Valid.length_QI (hv : X.Valid) : X.QI.length = X.n * X.n := by
  rw [QI, queryRows, List.length_map, hv.length_sortedIdx]

/-- The list of the columns of all pairs has `n²` entries. -/
theorem Valid.length_QJ (hv : X.Valid) : X.QJ.length = X.n * X.n := by
  rw [QJ, queryCols, List.length_map, hv.length_sortedIdx]

/-- An instance lists the row of each of its query pairs. -/
theorem Valid.length_WI (hv : X.Valid) {t : ℕ} (ht : t < X.m) : (X.WI t).length = X.w t := by
  have := hv.lo_add_le ht
  rw [WI, List.length_take, List.length_drop, hv.length_QI]
  omega

/-- An instance lists the column of each of its query pairs. -/
theorem Valid.length_WJ (hv : X.Valid) {t : ℕ} (ht : t < X.m) : (X.WJ t).length = X.w t := by
  have := hv.lo_add_le ht
  rw [WJ, List.length_take, List.length_drop, hv.length_QJ]
  omega

/-! ## The two matrices of an instance -/

/-- The matrix `X` has `n` rows and `D` columns. -/
theorem length_matX (X : HostData) (t : ℕ) : (X.matX t).length = X.n * X.D := by simp [matX, xList]

/-- The matrix `Y` has `D` rows and `n` columns. -/
theorem length_matY (X : HostData) (t : ℕ) : (X.matY t).length = X.D * X.n := by simp [matY, yList]

/-- The entries of `X` are 0 and 1. -/
theorem matX_zero_or_one (X : HostData) (t : ℕ) : ∀ e ∈ X.matX t, e = 0 ∨ e = 1 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact (ite_eq_or_eq _ _ _).symm

/-- The entries of `Y` are 0 and 1. -/
theorem matY_zero_or_one (X : HostData) (t : ℕ) : ∀ e ∈ X.matY t, e = 0 ∨ e = 1 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact (ite_eq_or_eq _ _ _).symm

/-- Every place stands at some position of the list of all pairs. -/
theorem Valid.exists_getD_sortedIdx (hv : X.Valid) {s : ℕ} (hs : s < X.n * X.n) :
    ∃ j < X.n * X.n, (sortedIdx X.n X.p X.RAB).getD j 0 = s := by
  have hmem : s ∈ sortedIdx X.n X.p X.RAB :=
    List.mem_flatMap.2 ⟨X.RAB.getD s 0, List.mem_range.2 (hv.rab_lt s), mem_classIdx.2 ⟨hs, rfl⟩⟩
  obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hmem
  exact ⟨j, hv.length_sortedIdx ▸ hj, (List.getD_eq_getElem _ _ hj).trans hjs⟩

/-- Proof of Theorem 17, "its c lies in some piece": every pair `(a, b)` is a query pair of an
instance whose piece contains a given vertex `c`. -/
theorem Valid.exists_query (hv : X.Valid) {a b c : ℕ} (ha : a < X.n) (hb : b < X.n)
    (hc : c < X.n) :
    ∃ t < X.m, ∃ i < X.w t,
      X.rowOf t i = a ∧ X.colOf t i = b ∧ ∃ c' < X.len t, X.c0 t + c' = c := by
  -- The position `j` of the pair in the list of all pairs, and the chunk `k` of that position.
  obtain ⟨j, hj, hplace⟩ := hv.exists_getD_sortedIdx (Nat.mul_add_lt_mul ha hb)
  obtain ⟨y, hy, hlo, hhi⟩ := chunkTab_cover hv.cap_pos (fun i _ => hv.rab_lt i) hj
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  -- The instance of that chunk and of the piece of `c`.
  have hpiece : c / X.q < X.h :=
    (Nat.lt_ceilDiv_iff hv.q_pos).2 (lt_of_le_of_lt (Nat.div_mul_le_self c X.q) hc)
  obtain ⟨t, ht, hdiv, hmod⟩ : ∃ t < X.m, t / X.chunkCount = c / X.q ∧ t % X.chunkCount = k :=
    ⟨_, Nat.mul_add_lt_mul hpiece hk, Nat.mul_add_div_of_lt hk, Nat.mul_add_mod_of_lt hk⟩
  have hentry : X.chunk t = (chunkTab X.n X.p X.cap X.RAB)[k] := by
    rw [chunk, hmod]
    exact List.getD_eq_getElem _ _ hk
  have hlo' : X.lo t ≤ j := by rw [lo, hentry]; exact hlo
  have hhi' : j < X.lo t + X.w t := by rw [lo, w, hentry]; exact hhi
  have hpair : X.place t (j - X.lo t) = a * X.n + b := by
    rw [place, Nat.add_sub_cancel' hlo', hplace]
  have hdivmod := Nat.div_add_mod' c X.q
  refine ⟨t, ht, j - X.lo t, by omega, ?_, ?_, c % X.q, ?_, ?_⟩
  · rw [rowOf, hpair, Nat.mul_add_div_of_lt hb]
  · rw [colOf, hpair, Nat.mul_add_mod_of_lt hb]
  · have := Nat.mod_lt c hv.q_pos
    rw [len, c0, hdiv]
    omega
  · rw [c0, hdiv, hdivmod]

/-! ## Acceptance -/






/-- A sum of numbers that are 0 or 1 is not 0 if and only if one of them is 1. -/
private theorem sum_ne_zero_iff (f : ℕ → ℤ) (N : ℕ) (h01 : ∀ k < N, f k = 0 ∨ f k = 1) :
    ((List.range N).map f).sum ≠ 0 ↔ ∃ k < N, f k = 1 := by
  have hnonneg : ∀ k ∈ Finset.range N, 0 ≤ f k := fun k hk => by
    rcases h01 k (Finset.mem_range.1 hk) with h | h <;> omega
  rw [List.sum_map_range, Ne, Finset.sum_eq_zero_iff_of_nonneg hnonneg]
  constructor
  · intro hne
    by_contra hnone
    exact hne fun k hk => (h01 k (Finset.mem_range.1 hk)).resolve_right
      fun hone => hnone ⟨k, Finset.mem_range.1 hk, hone⟩
  · rintro ⟨k, hk, hone⟩ hall
    have := hall k (Finset.mem_range.2 hk)
    omega

/-- Proof of Theorem 17: "the condition S(a,b,c) ≡ 0 (mod p) has become the equality w(a,c) + ϱ ≡
−w(b,c) of a label of (a,c) and a label of (b,c)".  Here `wAC`, `wAB` and `wBC` are the three
weights, and `ϱ` is the residue of `wAB`. -/
private theorem labels_eq_iff {p : ℕ} (hp : p ≠ 0) (wAC wAB wBC : ℤ) :
    (resid p wAC + resid p wAB) % p = (p - resid p wBC) % p ↔ (p : ℤ) ∣ wAB + wBC + wAC := by
  have hleft : ((resid p wAC + resid p wAB : ℕ) : ℤ) ≡ wAC + wAB [ZMOD (p : ℤ)] := by
    push_cast
    rw [resid_cast hp, resid_cast hp]
    exact (Int.mod_modEq wAC p).add (Int.mod_modEq wAB p)
  have hright : ((p - resid p wBC : ℕ) : ℤ) ≡ -wBC [ZMOD (p : ℤ)] := by
    rw [Nat.cast_sub (resid_lt hp wBC).le, resid_cast hp]
    simpa using (Int.modEq_zero_iff_dvd.2 (dvd_refl (p : ℤ))).sub (Int.mod_modEq wBC p)
  have hiff : wAC + wAB ≡ -wBC [ZMOD (p : ℤ)] ↔ (p : ℤ) ∣ wAB + wBC + wAC := by
    rw [Int.modEq_iff_dvd, ← dvd_neg, show -(-wBC - (wAC + wAB)) = wAB + wBC + wAC by ring]
  rw [← hiff, ← Nat.ModEq, ← Int.natCast_modEq_iff]
  exact ⟨fun h => (hleft.symm.trans h).trans hright, fun h => (hleft.trans h).trans hright.symm⟩

/-- An entry of the matrix `X` of an instance. -/
private theorem getD_xList {n D p c0 len rho : ℕ} {RAC : List ℕ} {a k : ℕ} (ha : a < n)
    (hk : k < D) :
    (xList n D p c0 len rho RAC).getD (a * D + k) 0 =
      if k / p < len ∧ k % p = (RAC.getD (a * n + c0 + k / p) 0 + rho) % p then 1 else 0 := by
  rw [xList, List.getD_map_range _ (Nat.mul_add_lt_mul ha hk), Nat.mul_add_mod_of_lt hk,
    Nat.mul_add_div_of_lt hk]

/-- An entry of the matrix `Y` of an instance. -/
private theorem getD_yList {n D p c0 len : ℕ} {RBC : List ℕ} {b k : ℕ} (hb : b < n) (hk : k < D) :
    (yList n D p c0 len RBC).getD (k * n + b) 0 =
      if k / p < len ∧ k % p = (p - RBC.getD (b * n + c0 + k / p) 0) % p then 1 else 0 := by
  rw [yList, List.getD_map_range _ (Nat.mul_add_lt_mul hk hb), Nat.mul_add_mod_of_lt hb,
    Nat.mul_add_div_of_lt hb]

/-- The entry `(XY)[a, b]` of an instance is not 0 if and only if the labels of `a` and `b` agree at
some vertex of the piece. -/
private theorem thinEntry_ne_zero_iff {n D p c0 len rho : ℕ} {RAC RBC : List ℕ} {a b : ℕ}
    (hp : p ≠ 0) (hlen : len * p ≤ D) (ha : a < n) (hb : b < n) :
    thinEntry n D (xList n D p c0 len rho RAC) (yList n D p c0 len RBC) a b ≠ 0 ↔
      ∃ c < len,
        (RAC.getD (a * n + c0 + c) 0 + rho) % p = (p - RBC.getD (b * n + c0 + c) 0) % p := by
  rw [thinEntry, sum_ne_zero_iff]
  · constructor
    · -- The column `k` is the middle vertex `(c, σ)` with `c = k / p` and `σ = k % p`.
      rintro ⟨k, hk, hone⟩
      rw [getD_xList ha hk, getD_yList hb hk] at hone
      split_ifs at hone with hX hY
      · exact ⟨k / p, hX.1, hX.2.symm.trans hY.2⟩
      all_goals simp at hone
    · -- The middle vertex `(c, σ)` with the common label `σ` is the column `c p + σ`.
      rintro ⟨c, hc, hlabel⟩
      have hσ : (RAC.getD (a * n + c0 + c) 0 + rho) % p < p := Nat.mod_lt _ (Nat.pos_of_ne_zero hp)
      have hk := (Nat.mul_add_lt_mul hc hσ).trans_le hlen
      refine ⟨_, hk, ?_⟩
      rw [getD_xList ha hk, getD_yList hb hk, Nat.mul_add_div_of_lt hσ, Nat.mul_add_mod_of_lt hσ,
        if_pos ⟨hc, rfl⟩, if_pos ⟨hc, hlabel⟩, mul_one]
  · intro k hk
    rw [getD_xList ha hk, getD_yList hb hk]
    split_ifs <;> simp

/-- The answer of the solver for a query pair: 1 if `(XY)[a, b] ≠ 0`, and 0 otherwise. -/
theorem Valid.getD_ans (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    (X.ans t).getD i 0 =
      if thinEntry X.n X.D (X.matX t) (X.matY t) (X.rowOf t i) (X.colOf t i) = 0 then 0 else 1 := by
  have hiI : i < (X.WI t).length := by rw [hv.length_WI ht]; exact hi
  have hiJ : i < (X.WJ t).length := by rw [hv.length_WJ ht]; exact hi
  have hzip : i < ((X.WI t).zip (X.WJ t)).length := by rw [List.length_zip]; omega
  rw [← getD_WI hi, ← getD_WJ hi, ans, thinOut, List.getD_eq_getElem _ _ (by simpa using hzip),
    List.getElem_map, List.getElem_map, List.getElem_zip, List.getD_eq_getElem _ _ hiI,
    List.getD_eq_getElem _ _ hiJ]

/-- Proof of Theorem 17: "a query pair (a,b) ∈ 𝒬 has a common neighbor if and only if some c ∈ C_k
has S(a,b,c) ≡ 0 (mod p)". -/
theorem acc_iff (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.acc t i = true ↔
      ∃ c < X.len t, (X.p : ℤ) ∣ X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) := by
  have hentry : X.acc t i = true ↔
      thinEntry X.n X.D (X.matX t) (X.matY t) (X.rowOf t i) (X.colOf t i) ≠ 0 := by
    rw [acc, decide_eq_true_eq, hv.getD_ans ht hi]
    split_ifs with h <;> simp [h]
  rw [hentry, matX, matY, thinEntry_ne_zero_iff hv.p_ne (hv.len_mul_le t) (hv.rowOf_lt ht hi)
    (hv.colOf_lt ht hi)]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [RAC, RBC, getD_residList, getD_residList, ← hv.rab_place ht hi, RAB, getD_residList,
    labels_eq_iff hv.p_ne, ← rowOf_mul_add_colOf, sumAt, Nat.add_assoc, Nat.add_assoc]

/-- Proof of Theorem 17, "scan the piece C_k of its instance for a c with S(a,b,c) = 0": when the
scan succeeds.
-/
theorem hit_iff {t i : ℕ} (hi : i < X.w t) :
    X.hit t i = true ↔ ∃ c < X.len t, X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) = 0 := by
  rw [hit, getD_WI hi, getD_WJ hi]
  simp [scanHit, sumAt, Nat.add_assoc]

/-! ## Correctness -/







































/-- Proof of Theorem 17: "We stop as soon as a zero triangle is found", so all scans but one fail.
-/
theorem sum_execs_le (X : HostData) :
    ∑ t ∈ Finset.range X.m, X.execs t ≤ ∑ t ∈ Finset.range X.m, X.fails t + 1 := by
  have key : ∀ T, ∑ t ∈ Finset.range T, X.execs t
      ≤ ∑ t ∈ Finset.range T, X.fails t + (X.found T).toNat := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have hstep : X.execs T + (X.found T).toNat ≤ X.fails T + (X.found (T + 1)).toNat :=
        execsUpto_le (X.acc T) (X.hit T) (X.found T) (X.w T)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega
  have hone : (X.found X.m).toNat ≤ 1 := Bool.toNat_le _
  have := key X.m
  omega

/-- The parameters of Theorem 17 give valid data. -/
theorem valid_of_params {n D g p : ℕ} {AB BC AC : List ℤ} (h : BigCase n D g)
    (hp : p ∈ primesInRange D) (lenAB : AB.length = n * n) (lenBC : BC.length = n * n)
    (lenAC : AC.length = n * n) :
    (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).Valid where
  n_pos := le_trans (by norm_num) (h.sixteen_le.trans h.le_n)
  p_pos := (mem_primesInRange.mp hp).1.one_le
  q_pos := by
    simp only
    rw [pieceSizeNat_eq D h.one_le_g]
    exact (pieceSize_mul_le h.sixteen_le h.one_le_g hp).1
  cap_pos := by
    have hD := h.sixteen_le
    have hDn := h.le_n
    simp only
    rw [queryCapNat, Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega)]
    have : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
    omega
  qp_le := by
    simp only
    rw [pieceSizeNat_eq D h.one_le_g]
    exact (pieceSize_mul_le h.sixteen_le h.one_le_g hp).2
  lenAB := lenAB
  lenBC := lenBC
  lenAC := lenAC

end HostData

end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: failed scans and false positives

Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans" (`HostData.sum_fails_le`).  An accepted query pair `(a, b)` of an instance whose scan
fails has a vertex `c` in the piece of the instance with `p ∣ S(a,b,c)` and `S(a,b,c) ≠ 0`
(`exists_false_positive`); such a triple is a false positive of `p`, and `F(p)` is their number.
Different pairs (instance, query pair) give different triples (`Valid.eq_of_place_eq`): `c`
determines the piece; `(a, b)` determines the place `a n + b`; the place determines the position in
the list of all pairs, which has no repetition; and the position determines the chunk.

The statement `theorem_17` is about the reduction on finite sets, and there the same sentences are
`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`,
`TriangleInstance.eq_of_mem_acceptedPairs` and `TriangleInstance.card_failedScans_le`.  The two
proofs run in parallel.  They share `F(p)` and the counting step, which is stated for any family of
scans (`TriangleInstance.card_le_F_of_distinct_scans`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace HostData

variable {X : HostData}

/-- Two query pairs at the same place, of instances with the same piece, are the same. -/
theorem Valid.eq_of_place_eq (hv : X.Valid) {t t' i i' : ℕ} (ht : t < X.m) (ht' : t' < X.m)
    (hi : i < X.w t) (hi' : i' < X.w t') (hplace : X.place t i = X.place t' i')
    (hpiece : t / X.chunkCount = t' / X.chunkCount) : t = t' ∧ i = i' := by
  have hlen := hv.length_sortedIdx
  have hend := hv.lo_add_le ht
  have hend' := hv.lo_add_le ht'
  -- The list of all pairs has no repetition, so the two pairs stand at the same position in it.
  have hpos : X.lo t + i = X.lo t' + i' := by
    rw [place, place, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      at hplace
    exact (List.Nodup.getElem_inj_iff (sortedIdx_nodup X.n X.p X.RAB)).1 hplace
  -- A position lies in one chunk only.
  have hchunk : ∀ s (hs : s % X.chunkCount < (chunkTab X.n X.p X.cap X.RAB).length),
      (chunkTab X.n X.p X.cap X.RAB)[s % X.chunkCount] = X.chunk s := fun s hs =>
    (List.getD_eq_getElem _ _ hs).symm
  have hmod : t % X.chunkCount = t' % X.chunkCount :=
    chunkTab_unique hv.cap_pos (j := X.lo t + i) (mod_chunkCount_lt ht) (mod_chunkCount_lt ht')
      (hchunk t _ ▸ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩)
      (hchunk t' _ ▸ hpos ▸ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi' _⟩)
  obtain rfl : t = t' := by
    rw [← Nat.div_add_mod t X.chunkCount, ← Nat.div_add_mod t' X.chunkCount, hpiece, hmod]
  exact ⟨rfl, by omega⟩

/-- Proof of Theorem 17: "A failed scan [...] contains a c ∈ C_k with S(a,b,c) ≡ 0 (mod p) but
S(a,b,c) ≠ 0". -/
theorem exists_false_positive (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t)
    (hacc : X.acc t i = true) (hhit : X.hit t i = false) :
    ∃ c < X.len t, (X.p : ℤ) ∣ X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) ∧
      X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) ≠ 0 := by
  obtain ⟨c, hc, hdvd⟩ := (acc_iff hv ht hi).1 hacc
  refine ⟨c, hc, hdvd, fun hzero => ?_⟩
  rw [(hit_iff hi).2 ⟨c, hc, hzero⟩] at hhit
  exact absurd hhit (by decide)

/-- A vertex of the piece of an instance determines the number of the piece. -/
theorem c0_add_div {t c : ℕ} (hc : c < X.len t) : (X.c0 t + c) / X.q = t / X.chunkCount := by
  rw [c0, Nat.mul_add_div_of_lt (hc.trans_le (X.len_le t))]

/-- The length of a filtered range, as the size of a set. -/
private theorem length_filter_range (k : ℕ) (f : ℕ → Bool) :
    ((List.range k).filter f).length = #{i ∈ range k | f i = true} := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range]

/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans". -/
theorem sum_fails_le (hv : X.Valid) :
    ∑ t ∈ range X.m, X.fails t ≤ (triOf X.n X.AB X.BC X.AC).F X.p := by
  -- The failed scans, as a set of pairs (instance, query pair).
  set failed : Finset (Σ _ : ℕ, ℕ) :=
    (range X.m).sigma fun t => {i ∈ range (X.w t) | (X.acc t i && !X.hit t i) = true} with hfailed
  have hcard : ∑ t ∈ range X.m, X.fails t = failed.card := by
    rw [hfailed, Finset.card_sigma]
    exact Finset.sum_congr rfl fun t _ => length_filter_range _ _
  have hmem : ∀ z ∈ failed,
      z.1 < X.m ∧ z.2 < X.w z.1 ∧ X.acc z.1 z.2 = true ∧ X.hit z.1 z.2 = false := by
    intro z hz
    simpa [hfailed, and_assoc] using hz
  rw [hcard]
  -- The scan `z` contains the triples of its query pair and a vertex of its piece.
  refine TriangleInstance.card_le_F_of_distinct_scans _ failed
    (fun z τ => τ.1.val = X.rowOf z.1 z.2 ∧ τ.2.1.val = X.colOf z.1 z.2 ∧
      ∃ c < X.len z.1, τ.2.2.val = X.c0 z.1 + c) (fun z hz => ?_) ?_
  · obtain ⟨ht, hi, hacc, hhit⟩ := hmem z hz
    obtain ⟨c, hc, hdvd, hne⟩ := exists_false_positive hv ht hi hacc hhit
    have hpiece := hv.piece_le ht
    exact ⟨(⟨_, hv.rowOf_lt ht hi⟩, ⟨_, hv.colOf_lt ht hi⟩, ⟨X.c0 z.1 + c, by omega⟩),
      ⟨rfl, rfl, c, hc, rfl⟩, hne, hdvd⟩
  · rintro τ z hz z' hz' ⟨hrow, hcol, c, hc, hvertex⟩ ⟨hrow', hcol', c', hc', hvertex'⟩
    obtain ⟨ht, hi, -, -⟩ := hmem z hz
    obtain ⟨ht', hi', -, -⟩ := hmem z' hz'
    have hplace : X.place z.1 z.2 = X.place z'.1 z'.2 := by
      rw [← rowOf_mul_add_colOf, ← rowOf_mul_add_colOf, ← hrow, ← hcol, hrow', hcol']
    have hpiece : z.1 / X.chunkCount = z'.1 / X.chunkCount := by
      rw [← c0_add_div hc, ← c0_add_div hc', ← hvertex, hvertex']
    obtain ⟨ht_eq, hi_eq⟩ := hv.eq_of_place_eq ht ht' hi hi' hplace hpiece
    exact Sigma.ext ht_eq (heq_of_eq hi_eq)

end HostData

end Light.Sec3

end
end

section


/-!
The all-edges modification of Theorem 17 maintains one persistent flag per pair.
This executable pure scheduler skips a query exactly when its pair is already solved
or its sparse-triangle answer is negative. It records every successful pair and
charges each executed scan either to a failed query or to a newly set flag.
-/

namespace APSPImprovement.AllEdges

structure Query where
  pair : ℕ
  accepted : Bool
  hit : Bool
  deriving DecidableEq

structure ScanResult where
  scans : ℕ
  found : Finset ℕ

/-- Execute the queries in order, retaining a separate success flag for each pair. -/
def run : List Query → Finset ℕ → ScanResult
  | [], found => ⟨0, found⟩
  | q :: qs, found =>
    if q.accepted && decide (q.pair ∉ found) then
      let rest := run qs (if q.hit then insert q.pair found else found)
      ⟨rest.scans + 1, rest.found⟩
    else run qs found

/-- Count all accepted queries whose scan fails, including queries skipped after success. -/
def failures (qs : List Query) : ℕ :=
  (qs.filter fun q => q.accepted && !q.hit).length

theorem failures_cons (q : Query) (qs : List Query) :
    failures (q :: qs) = failures qs + if q.accepted && !q.hit then 1 else 0 := by
  simp only [failures, List.filter_cons]
  split <;> simp_all [Nat.add_comm]

/-- The exact potential argument: a successful scan sets a previously unset flag. -/
theorem scans_add_initial_le (qs : List Query) (found : Finset ℕ) :
    (run qs found).scans + found.card ≤ failures qs + (run qs found).found.card := by
  induction qs generalizing found with
  | nil => simp [run, failures]
  | cons q qs ih =>
    rw [failures_cons]
    by_cases hm : q.pair ∈ found
    · have h := ih found
      simp only [run, hm, not_true_eq_false, decide_false, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte]
      omega
    · cases ha : q.accepted <;> cases hh : q.hit
      · simpa [run, ha, hh] using ih found
      · simpa [run, ha, hh] using ih found
      · have h := ih found
        simp [run, ha, hh, hm]
        omega
      · have h := ih (insert q.pair found)
        simp only [Finset.card_insert_of_notMem hm] at h
        simp [run, ha, hh, hm]
        omega

/-- A final flag means it was initially set or some accepted query found a witness. -/
theorem mem_found_iff (qs : List Query) (found : Finset ℕ) (pair : ℕ) :
    pair ∈ (run qs found).found ↔
      pair ∈ found ∨ ∃ q ∈ qs, q.pair = pair ∧ q.accepted = true ∧ q.hit = true := by
  induction qs generalizing found with
  | nil => simp [run]
  | cons q qs ih =>
    by_cases hm : q.pair ∈ found
    · simp only [run, hm, not_true_eq_false, decide_false, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨r, hr, hpair, ha, hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨r, Or.inr hr, hpair, ha, hh⟩
      · rintro (h | ⟨r, rfl | hr, hpair, ha, hh⟩)
        · exact Or.inl h
        · exact Or.inl (hpair ▸ hm)
        · exact Or.inr ⟨r, hr, hpair, ha, hh⟩
    · cases ha : q.accepted <;> cases hh : q.hit <;>
        simp [run, hm, ha, hh, ih]
      all_goals aesop

theorem found_subset (qs : List Query) {found bound : Finset ℕ}
    (hinitial : found ⊆ bound) (hpairs : ∀ q ∈ qs, q.pair ∈ bound) :
    (run qs found).found ⊆ bound := by
  intro pair hp
  rcases (mem_found_iff qs found pair).1 hp with h | ⟨q, hq, rfl, _, _⟩
  · exact hinitial h
  · exact hpairs q hq

/-- For an initially empty table of `N` flags, at most `N` executed scans succeed. -/
theorem scans_le_failures_add (qs : List Query) (N : ℕ)
    (hpairs : ∀ q ∈ qs, q.pair < N) :
    (run qs ∅).scans ≤ failures qs + N := by
  have hpotential := scans_add_initial_le qs ∅
  have hbound : (run qs ∅).found.card ≤ N := by
    have hsub := found_subset qs (Finset.empty_subset (Finset.range N))
      (fun q hq => Finset.mem_range.2 (hpairs q hq))
    simpa using Finset.card_le_card hsub
  simp only [Finset.card_empty, Nat.add_zero] at hpotential
  omega

end APSPImprovement.AllEdges




end

section


/-!
The machine-level change in the all-edges algorithm: an accepted query scans its
piece only while its own persistent output flag is zero. A successful scan writes
one to that flag, and no other memory cell changes.
-/

namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

namespace PairLocal
abbrev AB : ℕ := 0
abbrev BC : ℕ := 1
abbrev AC : ℕ := 2
abbrev N : ℕ := 3
abbrev A : ℕ := 4
abbrev B : ℕ := 5
abbrev First : ℕ := 6
abbrev Len : ℕ := 7
abbrev Flag : ℕ := 8
abbrev Answer : ℕ := 9
abbrev Hit : ℕ := 10
end PairLocal

open PairLocal in
/-- `scanPair(ab,bc,ac,n,a,b,c0,len,flagAddress,answer)`.
The only writable cell is `flagAddress`. -/
def scanPairBody (pScan : ℕ) : Stmt :=
  .ite ((Light.Cond.eq (v Answer) (k 0))) .skip
    (.ite ((Light.Cond.eq (M (v Flag)) (k 0)))
      ((Light.Stmt.seq
         (.call pScan [v AB, v BC, v AC, v N, v A, v B, v First, v Len] Hit)
         (.store (v Flag) (v Hit)))) .skip)

def pairMemory (μ : ℕ → ℤ) (dst : ℕ) (accepted found hit : Bool) : ℕ → ℤ :=
  if accepted && !found then Function.update μ dst (bit hit) else μ

/-- Reading the result gives the Boolean OR of the old flag and this query's witness. -/
theorem pairMemory_read (μ : ℕ → ℤ) (dst : ℕ) (accepted found hit : Bool)
    (hread : μ dst = bit found) :
    pairMemory μ dst accepted found hit dst = bit (found || (accepted && hit)) := by
  cases accepted <;> cases found <;> cases hit <;> simp [pairMemory, bit, hread]

theorem pairMemory_away (μ : ℕ → ℤ) (dst : ℕ) (accepted found hit : Bool)
    {addr : ℕ} (haddr : addr ≠ dst) :
    pairMemory μ dst accepted found hit addr = μ addr := by
  unfold pairMemory
  split_ifs
  · exact Function.update_of_ne haddr _ _
  · rfl

/-- Exact memory behavior and scan-sensitive running time of the new primitive. -/
theorem scanPair_spec {lim : Limits} {P : Program} {d pScan : ℕ} {μ : ℕ → ℤ}
    {ab bc ac n a b c0 len U dst : ℕ} {AB BC AC : List ℤ} {accepted found : Bool}
    (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC)
    (ha : a < n) (hb : b < n) (hc : c0 + len ≤ n)
    (_hn : n ≤ lim.space) (haddr : dst < lim.space)
    (hread : μ dst = bit found) (hd : d < lim.depth) :
    Ends lim P d (scanPairBody pScan)
      ⟨frame [ab, bc, ac, n, a, b, c0, len, dst, bit accepted], μ⟩
      (12 + if accepted && !found then tScan len + 20 else 0)
      (fun σ' => σ'.mem = pairMemory μ dst accepted found
        (scanHit n AB BC AC a b c0 len)) := by
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.arrAB); (obtain ⟨⟩ := id C.arrBC);
    (obtain ⟨⟩ := id C.arrAC))
  unfold scanPairBody
  cases accepted
  · refine Ends.iteLast (fun _ => Ends.skip ?_) (fun h => absurd (by simp [bit]) h)
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, bit] <;> omega)))
    simp [pairMemory]
  · refine Ends.iteLast (fun h => absurd h (by simp [bit])) (fun _ => ?_)
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, bit] <;> omega)))
    cases found
    · refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp [hread, bit]) h)
        (by (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, hread, bit] <;> omega)))
      refine Ends.callToThen (scan_meets hp C ha hb hc) ?_ (by (((try have := Light.Std.space_le (by assumption)));
                                                                 ((try have := Light.Std.const_le (by assumption)));
                                                                 (simp [Light.Limits.Addr, abs_le, -abs_mul, bit] <;> omega)))
      rintro _ _ ⟨rfl, rfl⟩
      refine Ends.storeTo dst (bit (scanHit n AB BC AC a b c0 len)) ?_
        (by cases h : scanHit n AB BC AC a b c0 len <;> (((try have := Light.Std.space_le (by assumption)));
                                                          ((try have := Light.Std.const_le (by assumption)));
                                                          (simp [Light.Limits.Addr, abs_le, -abs_mul, h, flag, bit] <;> omega)))
        (by first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tScan]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [tScan] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))))
      simp [pairMemory]
    · exact Ends.iteLast (fun h => absurd h (by simp [hread, bit]))
        (fun _ => Ends.skip (by simp [pairMemory])) (by (((try have := Light.Std.space_le (by assumption)));
                                                          ((try have := Light.Std.const_le (by assumption)));
                                                          (simp [Light.Limits.Addr, abs_le, -abs_mul, hread, bit] <;> omega)))

/-- Caller-facing form, including the exact flag update and preservation of other cells. -/
theorem scanPair_meets {lim : Limits} {P : Program} {d pPair pScan : ℕ} {μ : ℕ → ℤ}
    {ab bc ac n a b c0 len U dst : ℕ} {AB BC AC : List ℤ} {accepted found : Bool}
    (hpair : P[pPair]? = some (scanPairBody pScan)) (hscan : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC)
    (ha : a < n) (hb : b < n) (hc : c0 + len ≤ n)
    (hn : n ≤ lim.space) (haddr : dst < lim.space)
    (hread : μ dst = bit found) (hd : d < lim.depth) :
    Meets lim P pPair d [ab, bc, ac, n, a, b, c0, len, dst, bit accepted] μ
      (12 + if accepted && !found then tScan len + 20 else 0)
      (fun _ μ' => μ' = pairMemory μ dst accepted found (scanHit n AB BC AC a b c0 len)) :=
  Meets.of_body hpair (scanPair_spec hscan C ha hb hc hn haddr hread hd)

end APSPImprovement.AllEdges



end

section


/-!
# From a pair to the next pair

A loop that runs through the pairs (a, b) with a, b < n in the order of their numbers t = a n + b
keeps a = t / n and b = t % n in two local variables, so that no division is needed.
`nextPair A B N` is the step from one pair to the next, and `Ends.nextPair` is its rule.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}





/-- **From the pair number t to the pair number t + 1.** -/
theorem Ends.nextPair {A B N n t T : ℕ} {l : List ℤ} {μ : ℕ → ℤ} {Q : State → Prop}
    (h : Q ⟨frame (setLocal (setLocal l B ((t + 1) % n : ℕ)) A ((t + 1) / n : ℕ)), μ⟩)
    (hn : 0 < n) (ht : ((t + 1 : ℕ) : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word)
    (hA : frame l A = (t / n : ℕ)) (hB : frame l B = (t % n : ℕ)) (hN : frame l N = n)
    (hAB : A ≠ B := by decide) (hBN : N ≠ B := by decide) (hT : 14 ≤ T := by first
                                                                                   |
                                                                                     ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                           List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                       (first
                                                                                         | omega
                                                                                         | ((ring_nf); (omega))))
                                                                                   | omega
                                                                                   |
                                                                                     (simp [] <;>
                                                                                         first
                                                                                         | omega
                                                                                         | ((ring_nf); (omega)))) :
    Ends lim P d (nextPair A B N) ⟨frame l, μ⟩ T Q := by
  have hmod := Nat.mod_lt t hn
  have hdiv := Nat.div_le_self t n
  have hlast := Nat.succ_div_mod_of_eq (n := n) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (i := t) hn
  generalize t / n = a at *
  generalize t % n = b at *
  -- b := b + 1
  refine Ends.setToThen (b + 1 : ℕ) ?_ (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                                               Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                                               reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                                               Nat.cast_zero, Nat.cast_one, Expr.Gives, hB, abs_le]; omega)
    (by simp; omega)
  -- if b = n then b := 0; a := a + 1
  refine Ends.iteLast (fun he => ?_) (fun he => ?_) ⟨trivial, trivial⟩ (by simp; omega)
  · have he : b + 1 = n := by
      have : ((b + 1 : ℕ) : ℤ) = n := by
        simpa only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN] using he
      exact_mod_cast this
    rw [(hlast he).1, (hlast he).2] at h
    refine Ends.setToThen (0 : ℕ) (Ends.setTo (a + 1 : ℕ) ?_
      (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
            Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
            reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
            Nat.cast_zero, Nat.cast_one, Expr.Gives, frame_setLocal, if_neg hAB, hA,
            abs_le]; omega)
      (by simp; omega)) (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                              Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                              reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                              Nat.cast_zero, Nat.cast_one, Expr.Gives]; omega) (by simp; omega)
    convert h using 2
    funext y
    simp only [frame_setLocal]
    split_ifs <;> rfl
  · have he : b + 1 ≠ n := fun e => he (by
      simp only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN]
      exact_mod_cast e)
    rw [(hinner he).1, (hinner he).2] at h
    refine Ends.skip ?_
    convert h using 2
    funext y
    simp only [frame_setLocal]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) hAB
    · rfl
    · rw [h2, hA]
    · rfl

end Light

end
end

section


/-!
# Matrices in Z-order (Morton order)

The count of the proof of Theorem 17 needs a product of matrices over `ℤ[x]/(x^p - 1)`, "O(n^{log₂
7}) with Strassen's algorithm".  For the recursion of that algorithm a `2^K × 2^K` matrix is stored
in Z-order: the entry `(a, c)` stands at the place whose digits in base 4 are `2 a_i + c_i`, where
`a_i` and `c_i` are the binary digits of `a` and `c`.

* Places: `zIdx` maps a pair to its place, `zRow` and `zCol` map back (`zRow_zIdx`, `zCol_zIdx`,
  `zIdx_zRow_zCol`).  All three are computed one digit in base 4 at a time (`zIdx_eq`, `zRow_eq`,
  `zCol_eq`), and every proof is an induction along these equations.
* Lists: the entry `(a, c)` of `zList K M` starts at `zIdx a c * p` (`getD_zList`).
* **The four quadrants of a matrix are the four quarters of its list** (`quarter_zList`,
  `zList_succ`), which is what the recursion needs.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Places -/

















/-- The last binary digit goes to the last digit in base 4. -/
theorem spread_eq (i : ℕ) : spread i = i % 2 + 4 * spread (i / 2) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [spread]
  · unfold spread
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hi.ne', Nat.ofDigits_cons]

/-- The number 0 has no digits to move. -/
theorem spread_zero : spread 0 = 0 := by simp [spread]

/-- The row, one digit in base 4 at a time. -/
theorem zRow_eq (z : ℕ) : zRow z = z % 4 / 2 + 2 * zRow (z / 4) := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [zRow]
  · unfold zRow
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hz.ne', List.map_cons, Nat.ofDigits_cons]

/-- The column, one digit in base 4 at a time. -/
theorem zCol_eq (z : ℕ) : zCol z = z % 4 % 2 + 2 * zCol (z / 4) := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [zCol]
  · unfold zCol
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hz.ne', List.map_cons, Nat.ofDigits_cons]

/-- The place 0 is in row 0. -/
theorem zRow_zero : zRow 0 = 0 := by simp [zRow]

/-- The place 0 is in column 0. -/
theorem zCol_zero : zCol 0 = 0 := by simp [zCol]

/-- The place, one digit in base 4 at a time. -/
theorem zIdx_eq (a c : ℕ) : zIdx a c = (2 * (a % 2) + c % 2) + 4 * zIdx (a / 2) (c / 2) := by
  unfold zIdx
  rw [spread_eq a, spread_eq c]
  ring

/-- The places of a `2^K × 2^K` matrix are below `4^K`. -/
theorem zIdx_lt {K a c : ℕ} (ha : a < 2 ^ K) (hc : c < 2 ^ K) : zIdx a c < 4 ^ K := by
  induction K generalizing a c with
  | zero =>
    obtain rfl : a = 0 := by simpa using ha
    obtain rfl : c = 0 := by simpa using hc
    simp [zIdx, spread_zero]
  | succ K ih =>
    rw [pow_succ] at ha hc
    have h := ih (a := a / 2) (c := c / 2) (by omega) (by omega)
    rw [zIdx_eq, pow_succ]
    omega

/-- The row and the column of the place of `(a, c)` are `a` and `c`. -/
private theorem zRow_zCol_zIdx (a c : ℕ) : zRow (zIdx a c) = a ∧ zCol (zIdx a c) = c := by
  induction hm : a + c using Nat.strong_induction_on generalizing a c with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos (a + c) with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by omega
      simp [zIdx, spread_zero, zRow_zero, zCol_zero]
    · obtain ⟨hrow, hcol⟩ := ih (a / 2 + c / 2) (by omega) (a / 2) (c / 2) rfl
      rw [zRow_eq, zCol_eq, zIdx_eq]
      generalize zIdx (a / 2) (c / 2) = z at hrow hcol
      rw [show (2 * (a % 2) + c % 2 + 4 * z) / 4 = z by omega, hrow, hcol]
      omega

/-- The row of the place of `(a, c)` is `a`. -/
theorem zRow_zIdx (a c : ℕ) : zRow (zIdx a c) = a := (zRow_zCol_zIdx a c).1

/-- The column of the place of `(a, c)` is `c`. -/
theorem zCol_zIdx (a c : ℕ) : zCol (zIdx a c) = c := (zRow_zCol_zIdx a c).2

































/-! ## Matrices as lists -/








/-- A matrix of vectors of length `p` has `4^K p` numbers. -/
theorem length_zList {p : ℕ} (K : ℕ) (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p) :
    (zList K M).length = 4 ^ K * p :=
  List.length_flatMap_range _ _ fun _ _ => hM _ _

/-- The entry `(a, c)` of the matrix stands at the place `zIdx a c`. -/
theorem getD_zList {p K a c r : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p)
    (ha : a < 2 ^ K) (hc : c < 2 ^ K) (hr : r < p) :
    (zList K M).getD (zIdx a c * p + r) 0 = (M a c).getD r 0 := by
  rw [zList, List.getD_flatMap_range _ (fun _ _ => hM _ _) (zIdx_lt ha hc) hr, zRow_zIdx, zCol_zIdx]

/-- **The quadrants of a matrix are the quarters of its list.** -/
theorem quarter_zList {p K t : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p)
    (ht : t < 4) :
    quarter (4 ^ K * p) t (zList (K + 1) M) =
      zList K fun a c => M (a + t / 2 * 2 ^ K) (c + t % 2 * 2 ^ K) := by
  have hsplit : 4 ^ (K + 1) = t * 4 ^ K + 4 ^ K + (3 - t) * 4 ^ K := by
    calc 4 ^ (K + 1) = (t + 1 + (3 - t)) * 4 ^ K := by
          rw [show t + 1 + (3 - t) = 4 by omega, pow_succ, Nat.mul_comm]
      _ = _ := by ring
  rw [quarter, zList, hsplit, ← Nat.mul_assoc,
    List.take_drop_flatMap_range _ _ _ _ fun _ _ => hM _ _,
    zList]
  refine List.flatMap_congr fun z hz => ?_
  obtain ⟨hrow, hcol⟩ := zRow_zCol_quadrant ht (List.mem_range.1 hz)
  rw [hrow, hcol]

/-- A list of length `4 q` is put together from its four quarters. -/
private theorem eq_append_quarters {q : ℕ} {l : List ℤ} (hl : l.length = 4 * q) :
    l = quarter q 0 l ++ quarter q 1 l ++ quarter q 2 l ++ quarter q 3 l := by
  unfold quarter
  refine List.ext_getElem (by simp; omega) fun i _ _ => ?_
  simp only [List.getElem_append, List.length_append, List.length_take, List.length_drop,
    List.getElem_take, List.getElem_drop]
  split_ifs <;> congr 1 <;> omega

/-- A matrix is put together from its four quadrants. -/
theorem zList_succ {p K : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p) :
    zList (K + 1) M = zList K (fun a c => M a c) ++ zList K (fun a c => M a (c + 2 ^ K)) ++
      zList K (fun a c => M (a + 2 ^ K) c) ++ zList K fun a c => M (a + 2 ^ K) (c + 2 ^ K) := by
  have hlen : (zList (K + 1) M).length = 4 * (4 ^ K * p) := by
    rw [length_zList _ _ hM, pow_succ]
    ring
  conv_lhs => rw [eq_append_quarters hlen]
  rw [quarter_zList M hM (by norm_num), quarter_zList M hM (by norm_num),
    quarter_zList M hM (by norm_num), quarter_zList M hM (by norm_num)]
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.zero_mul, Nat.one_mul, Nat.add_zero]

end ThreeSumApsp.Spec

end
end

section


/-!
# Strassen's algorithm on lists, and the count of the proof of Theorem 17

Proof of Theorem 17: "Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm".
`strassenList` multiplies two `2^K × 2^K` matrices over `ℤ[x]/(x^p - 1)`, given as lists in Z-order,
and `countOf` reads the number of triples `(a,b,c)` with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≡ 0
(mod p)` off the product.

1. `zRing hp K α` is the list of the matrix `α` over the ring.  The operations on lists are the
   operations of the ring, entry by entry (`zRing_add`, `zRing_sub`), and the quadrants of a matrix
   are the quarters of its list (`quarter_zRing`, `zRing_succ`).
2. `strassenList_zRing`: the algorithm computes the product.  By induction on `K`; Strassen's seven
   products give the four quadrants of the product by an identity that holds summand by summand.
   It makes `7^K` multiplications in the ring, which is `O(n^{log₂ 7})` (`seven_pow_clog_le`).
3. The lists that the routine fills are the matrices `P` and `Q` of the proof of Theorem 17, padded
   with zeros to `2^K` rows and columns (`matPList_eq_zRing`, `matQList_eq_zRing`), and the padding
   does not change the entries of the product (`sum_padP_mul_padQ`).
4. `countOf_eq`: the count is the count of the proof of Theorem 17.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

open Finset

/-! ## Matrices over the ring, as lists -/

section Ring

variable {p : ℕ} (hp : p ≠ 0) (K : ℕ)





/-- The list of a sum of matrices. -/
theorem zRing_add (α β : ℕ → ℕ → CyclicRing p) :
    vadd (zRing hp K α) (zRing hp K β) = zRing hp K fun a c => α a c + β a c := by
  unfold zRing zList vadd
  rw [List.zipWith_flatMap_range _ _ _ _ (fun _ => length_cycVec hp _) fun _ => length_cycVec hp _]
  exact List.flatMap_congr fun z _ => (cycVec_add hp _ _).symm

/-- The list of a difference of matrices. -/
theorem zRing_sub (α β : ℕ → ℕ → CyclicRing p) :
    vsub (zRing hp K α) (zRing hp K β) = zRing hp K fun a c => α a c - β a c := by
  unfold zRing zList vsub
  rw [List.zipWith_flatMap_range _ _ _ _ (fun _ => length_cycVec hp _) fun _ => length_cycVec hp _]
  exact List.flatMap_congr fun z _ => (cycVec_sub hp _ _).symm

/-- The quadrants of a matrix are the quarters of its list. -/
theorem quarter_zRing (α : ℕ → ℕ → CyclicRing p) {t : ℕ} (ht : t < 4) :
    quarter (4 ^ K * p) t (zRing hp (K + 1) α) =
      zRing hp K fun a c => α (a + t / 2 * 2 ^ K) (c + t % 2 * 2 ^ K) :=
  quarter_zList _ (fun _ _ => length_cycVec hp _) ht

/-- A matrix is put together from its four quadrants. -/
theorem zRing_succ (α : ℕ → ℕ → CyclicRing p) :
    zRing hp (K + 1) α =
      zRing hp K (fun a c => α a c) ++ zRing hp K (fun a c => α a (c + 2 ^ K)) ++
      zRing hp K (fun a c => α (a + 2 ^ K) c) ++ zRing hp K fun a c => α (a + 2 ^ K) (c + 2 ^ K) :=
  zList_succ _ fun _ _ => length_cycVec hp _

end Ring

/-! ## Strassen's algorithm -/



















/-- A sum over twice as many indices. -/
private theorem sum_range_two_pow_succ {R : Type} [AddCommMonoid R] (K : ℕ) (f : ℕ → R) :
    ∑ c ∈ range (2 ^ (K + 1)), f c =
      ∑ c ∈ range (2 ^ K), f c + ∑ c ∈ range (2 ^ K), f (c + 2 ^ K) := by
  rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
  simp only [Nat.add_comm]

/-- **Strassen's algorithm computes the product**, for matrices over the ring. -/
theorem strassenList_zRing {p : ℕ} (hp : p ≠ 0) (K : ℕ) (α β : ℕ → ℕ → CyclicRing p) :
    strassenList p K (zRing hp K α) (zRing hp K β) =
      zRing hp K fun a b => ∑ c ∈ range (2 ^ K), α a c * β c b := by
  induction K generalizing α β with
  | zero => simp [strassenList, zRing, zList, zRow_zero, zCol_zero, cycVec_mul]
  | succ K ih =>
    -- The quarters of the two lists are the quadrants, and the seven products are products.
    have hq0 := fun γ => quarter_zRing hp K γ (show 0 < 4 by norm_num)
    have hq1 := fun γ => quarter_zRing hp K γ (show 1 < 4 by norm_num)
    have hq2 := fun γ => quarter_zRing hp K γ (show 2 < 4 by norm_num)
    have hq3 := fun γ => quarter_zRing hp K γ (show 3 < 4 by norm_num)
    simp only [Nat.reduceDiv, Nat.reduceMod, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
      at hq0 hq1 hq2 hq3
    simp only [strassenList, hq0, hq1, hq2, hq3, zRing_add, zRing_sub, ih]
    -- Strassen's identities, one for each quadrant of the product, summand by summand.
    rw [zRing_succ]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_ <;>
      refine congrArg (zRing hp K) (funext₂ fun a b => ?_) <;>
      rw [sum_range_two_pow_succ] <;>
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib] <;>
      exact Finset.sum_congr rfl fun c _ => by ring







/-! ## The count of the proof of Theorem 17 -/


























section Count

variable {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ}









/-- The padding does not change the entries of the product. -/
theorem sum_padP_mul_padQ (p : ℕ) {N : ℕ} (hN : n ≤ N) (a b : Fin n) :
    ∑ c ∈ range N, padP T p a c * padQ T p c b = (T.matP p * T.matQ p) a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hpad : ∑ x ∈ range k, padP T p a (n + x) * padQ T p (n + x) b = 0 :=
    Finset.sum_eq_zero fun x _ => by simp [padP]
  rw [Finset.sum_range_add, hpad, add_zero, Matrix.mul_apply, Finset.sum_range]
  exact Finset.sum_congr rfl fun c _ => by simp [padP, padQ]

variable (n) (AB BC AC : List ℤ)

/-- The first list that the routine fills is the matrix `P`, padded. -/
theorem matPList_eq_zRing (hp : p ≠ 0) (K : ℕ) :
    matPList n p K (residList p AC) = zRing hp K (padP (triOf n AB BC AC) p) := by
  refine congrArg (zList K) (funext₂ fun a c => ?_)
  rw [padP]
  split_ifs with h
  · rw [cycVec_matP, getD_residList]
    rfl
  · exact (cycVec_zero hp).symm

/-- The second list that the routine fills is the matrix `Q`, padded. -/
theorem matQList_eq_zRing (hp : p ≠ 0) (K : ℕ) :
    matQList n p K (residList p BC) = zRing hp K (padQ (triOf n AB BC AC) p) := by
  refine congrArg (zList K) (funext₂ fun c b => ?_)
  rw [padQ]
  split_ifs with h
  · rw [cycVec_matQ, getD_residList]
    rfl
  · exact (cycVec_zero hp).symm

/-- **The count of the proof of Theorem 17**: `countOf`, computed with Strassen's algorithm from the
three lists of weights, is the number of triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`. -/
theorem countOf_eq (hp : p ≠ 0) :
    countOf n p AB BC AC = (triOf n AB BC AC).countZeroMod p := by
  have hnK : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  -- The two lists are `P` and `Q`, padded (step 3), and Strassen's algorithm gives their product
  -- (step 2); both sides become sums over the pairs `(a, b)`.
  rw [countZeroMod_eq _ hp, countOf, matPList_eq_zRing n AB BC AC hp,
    matQList_eq_zRing n AB BC AC hp, strassenList_zRing, countBy, List.sum_map_range, sum_range_mul,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- The place `a n + b` has row `a` and column `b`; `(p - r) % p` is the residue of `-w(a,b)`; the
  -- number read from the list is that coefficient of `(PQ)[a,b]`.
  rw [Nat.mul_add_div_of_lt b.isLt, Nat.mul_add_mod_of_lt b.isLt, getD_residList, ← resid_neg hp,
    zRing,
    getD_zList _ (fun _ _ => length_cycVec hp _) (a.isLt.trans_le hnK) (b.isLt.trans_le hnK)
      (resid_lt hp _),
    sum_padP_mul_padQ _ p hnK a b]
  rfl

end Count

end ThreeSumApsp.Spec

end
end

section


/-!
# The steps and the scratch space of Strassen's recursion

At level j the operands are 2^j × 2^j matrices whose entries are vectors of p numbers, so that an
operand has 4^j · p numbers.  strScr p j ≤ 4^j · p (`strScr_le`), and both strScr and strSteps are
monotone in p.
-/

public section

namespace Light.Sec3

/-- The scratch space, exactly. -/
theorem strScr_add (p j : ℕ) : strScr p j + p = 4 ^ j * p := by
  induction j with
  | zero => simp [strScr]
  | succ j ih =>
    rw [strScr, pow_succ]
    have : 4 ^ j * 4 * p = 4 * (4 ^ j * p) := by ring
    omega

/-- The scratch space is at most the size of an operand. -/
theorem strScr_le (p j : ℕ) : strScr p j ≤ 4 ^ j * p := by
  have := strScr_add p j
  omega
























end Light.Sec3

end
end

section


/-!
# Residues without division

"We reduce the weights modulo a prime p" (proof of Theorem 17).  The language has no division.  The
residue of a number w modulo p is found by greedy subtraction of 2^len p, …, 2p, p, which are kept
in a table.

* bitLen(U) returns the number of binary digits of U, by doubling (`bitLen_spec`).
* dblTable(dst, p, len) writes p, 2p, …, 2^len p to dst (`dblTable_spec`).
* resid(w, dbl, len) returns w mod p, for |w| < 2^len, given the table at dbl (`resid_meets`).  What
  the routine holds after i rounds is `greedyAt p len w i`: it is not negative, below 2^(len+1-i) p,
  and congruent to w (`greedyAt_inv`), so that it ends with the residue (`greedyAt_end`).
* residues(src, dst, m, dbl, len) writes the residues of the m numbers at src to dst, by one call of
  resid for each (`residues_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The number of binary digits -/

namespace BitLen






end BitLen












































/-! ## The table of the doubles -/

/-- One more entry of the table. -/
theorem dblList_succ (p len : ℕ) :
    dblList p (len + 1) = dblList p len ++ [((p * 2 ^ (len + 1) : ℕ) : ℤ)] := by
  simp [dblList, List.range_succ]

/-- The table has len + 1 entries. -/
@[simp] theorem length_dblList (p len : ℕ) : (dblList p len).length = len + 1 := by simp [dblList]

/-- Entry j of the table is 2^j p. -/
theorem read_dblList {μ : ℕ → ℤ} {dbl p len j : ℕ} (h : Seg μ dbl (dblList p len)) (hj : j ≤ len) :
    μ (dbl + j) = ((p * 2 ^ j : ℕ) : ℤ) := by
  rw [h j (by simp; omega)]
  simp [dblList]

namespace DblTable








end DblTable





















/-- **dblTable** writes p, 2p, …, 2^len p and changes nothing else.  It forms numbers up to
2^len p. -/
theorem dblTable_spec {μ : ℕ → ℤ} {dst p len : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst + (len + 1) ≤ lim.space) (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d dblTableBody ⟨frame [dst, p, len], μ⟩ (tDblTable len) fun σ' =>
      Seg σ'.mem dst (dblList p len) ∧ SameOutside μ σ'.mem dst (len + 1) := by
  have hfits : ∀ j ≤ len, ((p * 2 ^ j : ℕ) : ℤ) ≤ lim.word := fun j hj =>
    le_trans (by exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) hj)) hp
  unfold tDblTable
  -- exp := 0; entry := p; dst[0] := entry
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen p ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen dst p ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while exp < len
  refine Ends.whileBlock (DblInv μ dst p len) len ?start ?round ?done
  case start =>
    refine ⟨Function.update μ dst p, by simp, ?_, SameOutside.refl.update ⟨by omega, by omega⟩ _⟩
    simpa [dblList] using (Seg.nil (μ := μ) (a := dst)).snoc p
  case round =>
    rintro j _ hj ⟨μ', rfl, seg, rest⟩
    have hnext := hfits (j + 1) hj
    have hdouble : p * 2 ^ (j + 1) = p * 2 ^ j + p * 2 ^ j := by ring
    have haddr : ((dst : ℤ) + ((j : ℤ) + 1)).toNat = dst + (dblList p j).length := by
      rw [length_dblList]
      omega
    -- entry := entry + entry; exp := exp + 1; dst[exp] := entry
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_, Function.update μ' (dst + (dblList p j).length)
      ((p * 2 ^ (j + 1) : ℕ) : ℤ), ?_, dblList_succ p j ▸ seg.snoc _,
      rest.update ⟨by omega, by rw [length_dblList]; omega⟩ _⟩
    · rw [hdouble] at hnext
      generalize p * 2 ^ j = q at hnext
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
    · rw [hdouble]
      simp [update_frame_setLocal, haddr]
  case done =>
    rintro _ ⟨μ', rfl, seg, rest⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), seg, rest⟩

/-! ## One residue -/










/-- A multiple of p is congruent to 0. -/
private theorem mul_pow_modEq_zero (p j : ℕ) : ((p * 2 ^ j : ℕ) : ℤ) ≡ 0 [ZMOD (p : ℤ)] := by
  rw [Int.modEq_zero_iff_dvd, Nat.cast_mul]
  exact Dvd.intro _ rfl

/-- 2^(j+1) p is twice 2^j p. -/
private theorem cast_mul_pow_succ (p j : ℕ) :
    ((p * 2 ^ (j + 1) : ℕ) : ℤ) = 2 * ((p * 2 ^ j : ℕ) : ℤ) := by
  rw [pow_succ]
  push_cast
  ring

/-- After i rounds the number is not negative, below 2^(len+1-i) p, and congruent to w. -/
theorem greedyAt_inv {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) : ∀ i, i ≤ len + 1 →
    0 ≤ greedyAt p len w i ∧ greedyAt p len w i < ((p * 2 ^ (len + 1 - i) : ℕ) : ℤ) ∧
      greedyAt p len w i ≡ w [ZMOD (p : ℤ)] := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨hlow, hhigh⟩ := abs_lt.1 hw
    have hle : (2 : ℤ) ^ len ≤ ((p * 2 ^ len : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_mul_of_pos_left (2 ^ len) hp
    rw [greedyAt, Nat.sub_zero, cast_mul_pow_succ]
    exact ⟨by linarith, by linarith,
      by simpa only [add_zero] using (Int.ModEq.refl w).add (mul_pow_modEq_zero p len)⟩
  | succ i ih =>
    intro hi
    obtain ⟨hlow, hhigh, hmod⟩ := ih (by omega)
    rw [show len + 1 - i = (len - i) + 1 by omega, cast_mul_pow_succ] at hhigh
    rw [show len + 1 - (i + 1) = len - i by omega, greedyAt]
    split_ifs with h
    · exact ⟨by linarith, by linarith,
        by simpa only [sub_zero] using hmod.sub (mul_pow_modEq_zero p (len - i))⟩
    · exact ⟨hlow, by linarith, hmod⟩

/-- Greedy subtraction gives the remainder. -/
theorem greedyAt_end {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) :
    greedyAt p len w (len + 1) = (resid p w : ℕ) := by
  obtain ⟨hlow, hhigh, hmod⟩ := greedyAt_inv hp hw (len + 1) le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hhigh
  rw [resid_cast (by omega), ← Int.emod_eq_of_lt hlow hhigh]
  exact hmod

/-- Every number that resid holds is below 2^(len+1) p. -/
theorem greedyAt_lt {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) {i : ℕ}
    (hi : i ≤ len + 1) : greedyAt p len w i < ((p * 2 ^ (len + 1) : ℕ) : ℤ) := by
  obtain ⟨-, hhigh, -⟩ := greedyAt_inv hp hw i hi
  exact hhigh.trans_le (by
    exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) (by omega)))

namespace Resid









end Resid














/-- **resid** returns w mod p and changes no cell.  It forms numbers up to 2^(len+1) p. -/
theorem resid_meets {μ : ℕ → ℤ} {pResid dbl p len : ℕ} {w : ℤ} (hP : P[pResid]? = some residBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p) (hseg : Seg μ dbl (dblList p len))
    (hlt : |w| < 2 ^ len) (hdbl : dbl + (len + 1) ≤ lim.space)
    (hword : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pResid d [w, dbl, len] μ (tResid len) fun r μ' => r = (resid p w : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have hlow := fun i hi => (greedyAt_inv hp hlt i hi).1
  have hhigh := fun i (hi : i ≤ len + 1) => greedyAt_lt hp hlt hi
  unfold tResid
  -- num := w + dbl[len]; exp := len + 1
  have hlow0 := hlow 0 (by omega)
  have hhigh0 := hhigh 0 (by omega)
  have hfirst : w + μ (dbl + len) = greedyAt p len w 0 := by rw [read_dblList hseg le_rfl, greedyAt]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (greedyAt p len w 0) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hfirst]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hfirst] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hfirst] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (len + 1 : ℕ)
            -- while 0 < exp.  Before round i, exp = len + 1 - i and num = greedyAt p len w i.
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while 0 < exp.  Before round i, exp = len + 1 - i and num = greedyAt p len w i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [w, dbl, len, (len + 1 - i : ℕ), greedyAt p len w i], μ⟩) (len + 1)
    (by simp) ?round ?done le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hlowi := hlow i hi.le
    have hhighi := hhigh i hi.le
    have hread := read_dblList hseg (show len - i ≤ len by omega)
    have hexp : ((len + 1 - i : ℕ) : ℤ) - 1 = (len - i : ℕ) := by omega
    have hnext : len + 1 - (i + 1) = len - i := by omega
    have hpos : (0 : ℤ) ≤ ((p * 2 ^ (len - i) : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [hnext, greedyAt]
    generalize greedyAt p len w i = g at hlowi hhighi
    generalize ((p * 2 ^ (len - i) : ℕ) : ℤ) = q at hread hpos
    -- exp := exp - 1; if dbl[exp] ≤ num then num := num - dbl[exp]
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_, ?_⟩
    · simp [Limits.Addr, abs_le, hexp, hread]
      omega
    · by_cases hle : q ≤ g <;> simp [update_frame_setLocal, hexp, hread, hle]
  case done =>
    rintro _ rfl
    -- return num
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      Ends.setTo (greedyAt p len w (len + 1)) (by simp [greedyAt_end hp hlt])
      (hT := by simp; omega)⟩

/-! ## The residues of a list -/

namespace Residues











end Residues






































/-- One more residue. -/
theorem residList_take_succ (p : ℕ) {l : List ℤ} {i : ℕ} (hi : i < l.length) :
    residList p (l.take (i + 1)) = residList p (l.take i) ++ [resid p l[i]] := by
  rw [residList, residList, List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]
  rfl

open Residues in
/-- **residues** writes the residues of a list and changes nothing else. -/
theorem residues_spec {μ : ℕ → ℤ} {pResid src dst m dbl p len U : ℕ} {l : List ℤ}
    (hP : P[pResid]? = some residBody) (hd : d < lim.depth)
    (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Ends lim P d (residuesBody pResid) ⟨frame [src, dst, m, dbl, len], μ⟩ (tResidues m len)
      fun σ' => SegN σ'.mem dst (residList p l) ∧ SameOutside μ σ'.mem dst m := by
  obtain ⟨hw, hp, segDbl, segSrc, rfl, hle, hlt, spaceDbl, spaceSrc, spaceDst, hm, apartSrc,
    apartDbl, hword⟩ := pre
  have hltZ : (U : ℤ) < 2 ^ len := by exact_mod_cast hlt
  unfold tResidues
  -- for i < m
  refine Ends.for (ResiduesInv μ src dst l.length dbl p len l) l.length (tResid len + 13)
    ?start ?round ?done ?bound
  case start =>
    exact ⟨0, μ, congrArg (fun loc => (⟨loc, μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm), Seg.nil, .refl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, seg, rest⟩
    have hread : μ' (src + i) = l[i] := (rest _ (by omega)).trans (segSrc.get hi)
    have hlen : (residList p (l.take i)).length = i := by simp [residList]; omega
    -- res := resid(src[i], dbl, len)
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (first
        |
          refine
            Light.Ends.callToThen
              ((resid_meets (w := l[i]) hP hw hp
                  (segDbl.keep
                    (by
                      ((try have := length_dblList);
                        (((try refine Light.SameOn.cell ?_);
                            (intro apspMacro_408188_0 apspMacro_408188_1);
                            (first
                              |
                                ((((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_408188_2));
                                            ((try
                                                  have :=
                                                    apspMacro_408188_2
                                                      apspMacro_408188_0
                                                      (by omega)));
                                            (revert apspMacro_408188_2)));
                                      (intros);
                                      (try
                                          simp only [Function.update_apply,
                                            Light.wrote] at *)));
                                  (omega))
                              |
                                ((simp [length_dblList] at apspMacro_408188_1);
                                  (((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_408188_3));
                                            ((try
                                                  have :=
                                                    apspMacro_408188_3
                                                      apspMacro_408188_0
                                                      (by omega)));
                                            (revert apspMacro_408188_3)));
                                      (intros);
                                      (try
                                          simp only [Function.update_apply,
                                            Light.wrote] at *)));
                                  (omega))
                              |
                                ((((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_408188_4));
                                            ((try
                                                  have :=
                                                    apspMacro_408188_4
                                                      apspMacro_408188_0
                                                      (by omega)));
                                            (revert apspMacro_408188_4)));
                                      (intros);
                                      (try
                                          simp only [Function.update_apply,
                                            Light.wrote] at *)));
                                  (fail
                                      "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                its condition K x does not follow from the hypotheses."))))))))
                  ((hle.getElem hi).trans_lt hltZ) spaceDbl hword)
                _ (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            Light.Ends.callToThen
              (resid_meets (w := l[i]) hP hw hp
                (segDbl.keep
                  (by
                    ((try have := length_dblList);
                      (((try refine Light.SameOn.cell ?_);
                          (intro apspMacro_408188_5 apspMacro_408188_6);
                          (first
                            |
                              ((((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_408188_7));
                                          ((try
                                                have :=
                                                  apspMacro_408188_7
                                                    apspMacro_408188_5 (by omega)));
                                          (revert apspMacro_408188_7)));
                                    (intros);
                                    (try
                                        simp only [Function.update_apply,
                                          Light.wrote] at *)));
                                (omega))
                            |
                              ((simp [length_dblList] at apspMacro_408188_6);
                                (((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_408188_8));
                                          ((try
                                                have :=
                                                  apspMacro_408188_8
                                                    apspMacro_408188_5 (by omega)));
                                          (revert apspMacro_408188_8)));
                                    (intros);
                                    (try
                                        simp only [Function.update_apply,
                                          Light.wrote] at *)));
                                (omega))
                            |
                              ((((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_408188_9));
                                          ((try
                                                have :=
                                                  apspMacro_408188_9
                                                    apspMacro_408188_5 (by omega)));
                                          (revert apspMacro_408188_9)));
                                    (intros);
                                    (try
                                        simp only [Function.update_apply,
                                          Light.wrote] at *)));
                                (fail
                                    "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                              SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                              its condition K x does not follow from the hypotheses."))))))))
                ((hle.getElem hi).trans_lt hltZ) spaceDbl hword)
              ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hread]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hread] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hread] <;> omega)));
      (on_goal -1 =>
          ((rintro _ μ₁
                ⟨rfl, rfl⟩
                    -- dst[i] := res
                    );
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    -- dst[i] := res
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (dst + i) (resid p l[i] : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp, resid p l[i],
      Function.update μ₁ (dst + i) (resid p l[i] : ℕ), by simp [update_frame_setLocal], ?_,
      rest.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := seg.snoc (resid p l[i])
    rwa [hlen, ← residList_take_succ p hi] at hsnoc
  case done =>
    rintro _ - ⟨r, μ', rfl, seg, rest⟩
    exact ⟨by simpa using seg, rest⟩

end Light.Sec3

end
end

section


/-!
# The count for one prime (proof of Theorem 17, "Hashing modulo a prime")

"For every prime p in the range we count the triples with S(a,b,c) ≡ 0 (mod p)", where S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) is the weight of the triangle.  "Let P[a,c] := x^{w(a,c) mod p} and Q[c,b]
:= x^{w(b,c) mod p} be matrices over the ring ℤ[x]/(x^p - 1) […]; then F(p) + Z₀ is the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]."  Here F(p) is the number
of triples with S(a,b,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ the number of triples with S(a,b,c) = 0.

countPrime(n, ab, bc, ac, p, len, K, N2, w) computes this count for one prime, in a work area at w.
Two letters of the quotation mean something else in the code.  There w is the address of the work
area, and the weights are the three lists ab, bc and ac.  And `P` is the program, while the matrices
P and Q occur only as the lists `matPList` and `matQList`.

The routine has three parts.

* The addresses of the parts of the work area (`cpAddr_spec`); they lie one behind the other
  (`cp_places`).
* Six tables: the doubles of p, the residues of the three lists of weights, the places of the
  Z-order, and the sizes 4^i p of the matrices of Strassen's recursion, which szTable(dst, p, J)
  writes (`szTable_spec`, `cpTables_spec`, `CpTabs`).
* The matrices P and Q in Z-order, their product by Strassen's algorithm, and the sum of the
  coefficients (`cpProduct_spec`).

`countPrime_spec` puts the three parts together.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/























namespace CountPrime





























end CountPrime
















































/-! ## The layout of the work area -/





































































/-! ## What countPrime assumes -/

















/-- A list of residues is as long as the list of numbers. -/
@[simp] theorem length_residList (p : ℕ) (l : List ℤ) : (residList p l).length = l.length := by
  simp [residList]

/-- Residues modulo p are below p. -/
theorem lt_of_mem_residList {p : ℕ} (hp : 1 ≤ p) {l : List ℤ} {x : ℕ} (hx : x ∈ residList p l) :
    x < p := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact resid_lt (by omega) w

section Premise

variable {μ : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}


























end Premise

/-! ## The procedures that countPrime calls -/

section meets

variable {μ : ℕ → ℤ}

/-- **dblTable** as a procedure. -/
theorem dblTable_meets {q dst p len : ℕ} (hP : P[q]? = some dblTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + (len + 1) ≤ lim.space)
    (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, len] μ (tDblTable len) fun _ μ' =>
      Seg μ' dst (dblList p len) ∧ SameOutside μ μ' dst (len + 1) :=
  Meets.of_body hP (dblTable_spec hw hdst hp)

/-- **residues** as a procedure. -/
theorem residues_meets {q pResid src dst m dbl p len U : ℕ} {l : List ℤ}
    (hP : P[q]? = some (residuesBody pResid)) (hR : P[pResid]? = some residBody)
    (hd : d < lim.depth) (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Meets lim P q d [src, dst, m, dbl, len] μ (tResidues m len) fun _ μ' =>
      SegN μ' dst (residList p l) ∧ SameOutside μ μ' dst m :=
  Meets.of_body hP (residues_spec hR hd pre)

end meets

/-! ## The tables -/










section parts

variable {ν : CpNums} {μ₀ μ μ' : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}





























































/-! ## The product and the count -/
































































































end parts

/-! ## Larger primes need more cells and more time -/

















end Light.Sec3

end
end

section


/-!
# The prime that is chosen (proof of Theorem 17)

`chosenPrime n D AB BC AC` is the first prime of the window `√D/2 ≤ p < √D` at which the count,
computed with Strassen's algorithm from the three lists of weights, is smallest.  Here
`triOf n AB BC AC` is the instance of Exact Triangle whose weights are read from the three lists:
`w(a,b)` at `a n + b` of `AB`, `w(b,c)` at `b n + c` of `BC`, `w(a,c)` at `a n + c` of `AC`.

* The computed count is the count of the proof of Theorem 17 at every prime of the window
  (`countOf_eq`), so the chosen prime is a selected prime in the sense of the proof of Theorem 17,
  "We select the prime with the smallest count" (`chosenPrime_isSelected`).  It lies between 2 and
  `⌊√D⌋` (`two_le_chosenPrime`, `chosenPrime_le_sqrt`).
* A program finds it in one pass over the primes: `bestOf f L i` is the best of the first `i`
  elements of a list (`bestOf_one`, `bestOf_succ`, `bestOf_length`).
* The paper bounds the weights by `n^ν`; a program has a bound `U`.  `kappaOf n U` is the least
  exponent `κ ≥ 1` with `U ≤ n^κ`, and with it the bound of the proof of Theorem 17 on the number
  `F(p)` of false positives, that is, of triples with `S(a,b,c) ≠ 0` and `p ∣ S(a,b,c)`, holds for
  the chosen prime (`F_chosenPrime_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The chosen prime -/






section Chosen

variable {n D : ℕ} (AB BC AC : List ℤ)

/-- **The chosen prime is a selected prime** (proof of Theorem 17: "We select the prime with the
smallest count"). -/
theorem chosenPrime_isSelected (hD : 16 ≤ D) :
    (triOf n AB BC AC).IsSelectedPrime D (chosenPrime n D AB BC AC) := by
  -- The window has a prime `p₀`, so `List.argmin` returns `some m`, and the default 0 of
  -- `chosenPrime` is never used.
  obtain ⟨p₀, hp₀, -⟩ := TriangleInstance.exists_isSelectedPrime (triOf n AB BC AC) D hD
  rw [primesInRange_eq, List.mem_toFinset] at hp₀
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1
    (mt (List.argmin_eq_none (f := fun p => (countOf n p AB BC AC).toNat)).1
      (List.ne_nil_of_mem hp₀))
  -- The computed count is the count of the proof of Theorem 17 at every prime of the window.
  have hcount : ∀ q ∈ primesList D,
      (triOf n AB BC AC).countZeroMod q = (countOf n q AB BC AC).toNat := fun q hq => by
    rw [countOf_eq n AB BC AC (mem_primesList.1 hq).1.ne_zero, Int.toNat_natCast]
  rw [chosenPrime, hm, Option.getD_some, TriangleInstance.IsSelectedPrime, primesInRange_eq]
  refine ⟨List.mem_toFinset.2 (List.argmin_mem hm), fun q hq => ?_⟩
  rw [hcount m (List.argmin_mem hm), hcount q (List.mem_toFinset.1 hq)]
  exact List.le_of_mem_argmin (f := fun p => (countOf n p AB BC AC).toNat)
    (List.mem_toFinset.1 hq) hm

/-- The chosen prime is a prime of the window. -/
theorem chosenPrime_mem (hD : 16 ≤ D) : chosenPrime n D AB BC AC ∈ primesInRange D :=
  (chosenPrime_isSelected AB BC AC hD).1

/-- The chosen number is in the list of the primes of the window. -/
private theorem chosenPrime_mem_primesList (hD : 16 ≤ D) :
    chosenPrime n D AB BC AC ∈ primesList D := by
  have hmem := chosenPrime_mem (n := n) AB BC AC hD
  rwa [primesInRange_eq, List.mem_toFinset] at hmem

/-- The chosen prime is at least 2. -/
theorem two_le_chosenPrime (hD : 16 ≤ D) : 2 ≤ chosenPrime n D AB BC AC :=
  (mem_primesList.1 (chosenPrime_mem_primesList AB BC AC hD)).1.two_le

/-- The chosen prime is at most `⌊√D⌋`. -/
theorem chosenPrime_le_sqrt (hD : 16 ≤ D) : chosenPrime n D AB BC AC ≤ Nat.sqrt D :=
  le_sqrt_of_mem_primesList (chosenPrime_mem_primesList AB BC AC hD)

end Chosen

/-! ## The smallest count, by one pass -/




















/-! ## False positives, in terms of a bound on the weights -/




/-- The exponent is at least 1. -/
theorem one_le_kappaOf (n U : ℕ) : 1 ≤ kappaOf n U := le_max_left _ _

/-- `U ≤ n^κ` for this exponent. -/
theorem le_rpow_kappaOf {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) :
    (U : ℝ) ≤ (n : ℝ) ^ kappaOf n U := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  calc (U : ℝ) = (n : ℝ) ^ Real.logb n U := (Real.rpow_logb (by linarith) hn1.ne' hU0).symm
    _ ≤ (n : ℝ) ^ kappaOf n U := Real.rpow_le_rpow_of_exponent_le hn1.le (le_max_right _ _)

/-- It is the least such exponent. -/
theorem kappaOf_le {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) {κ' : ℝ} (h1 : 1 ≤ κ')
    (h : (U : ℝ) ≤ (n : ℝ) ^ κ') : kappaOf n U ≤ κ' := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  refine max_le h1 ?_
  rw [div_le_iff₀ (Real.log_pos hn1), ← Real.log_rpow (by linarith)]
  exact Real.log_le_log hU0 h

/-- Weights of absolute value at most `U` are at most `n^κ`. -/
theorem weightsPolyBounded_kappaOf {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) {AB BC AC : List ℤ}
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    (triOf n AB BC AC).WeightsPolyBounded (kappaOf n U) := by
  have key : ∀ l : List ℤ, AbsLe l U → ∀ i,
      ((|l.getD i 0| : ℤ) : ℝ) ≤ (n : ℝ) ^ kappaOf n U := fun l hl i =>
    le_trans (by exact_mod_cast AbsLe.abs_getD_le (Int.natCast_nonneg U) hl i)
      (le_rpow_kappaOf hn hU)
  exact ⟨fun a b => key AB hAB _, fun b c => key BC hBC _, fun a c => key AC hAC _⟩

/-- **The number of false positives of the chosen prime** (proof of Theorem 17:
"F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)"), with the constant `Hashing.falsePositiveConst`. -/
theorem F_chosenPrime_le {n D U : ℕ} (hD : 16 ≤ D) (hDn : D ≤ n) (hU : 1 ≤ U) {AB BC AC : List ℤ}
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    ((triOf n AB BC AC).F (chosenPrime n D AB BC AC) : ℝ) ≤
      Hashing.falsePositiveConst * (kappaOf n U * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) :=
  Hashing.F_le_falsePositiveConst_mul hD hDn (one_le_kappaOf n U) _
    (weightsPolyBounded_kappaOf (by omega) hU hAB hBC hAC) (chosenPrime_isSelected AB BC AC hD)

end ThreeSumApsp.Spec

end
end

section


/-!
# The classes W_ϱ of the pairs (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p)".  (The cutting of
the classes into chunks, with which the sentence goes on, is a routine of its own.)

classes(rab, n, p, cls, cur, qi, qj) sorts the n² pairs (a, b) by the residue of w(a,b), which is in
the cell rab + a n + b, keeping the row-major order within a class: a stable counting sort.  It
writes the rows of the sorted pairs to qi, their columns to qj, and the places where the classes
start to cls.  The row and the column of the current pair are kept in two counters, so that no
division is needed.  `classes_meets` proves this, within `tClasses n p` steps, a number linear in
n² + p.

The routine has five phases.  Between them the state is described by `ClsState`:

* `clsZero_ends`: the counters are cleared;
* `clsCount_ends`: the sizes of the classes are counted;
* `clsPrefix_ends`: prefix sums turn the sizes into the starts;
* `clsCopy_ends`: the starts are copied to cur, the next free places;
* `clsPlace_ends`: each pair goes to the next free place of its class (`ClsPlaced.step` for the
  memory, `clsPlaceOne_ends` for the program), and row and column step to the next pair.

The place of a pair is its place `sortPos` in a stable sort; `getD_sortedIdx` and
`segN_map_sortedIdx` identify what stands there with the lists of the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side: the lists of the specification and the places of a stable sort -/

section pure




/-- The size of a class, as a count of keys. -/
theorem length_classIdx (n : ℕ) (RAB : List ℕ) (r : ℕ) :
    (classIdx n RAB r).length = cntEq (clsKey RAB) r (n * n) :=
  List.length_filter_range (fun i => RAB.getD i 0 = r) (n * n)

/-- The sizes of the classes before `r` add up to the number of smaller keys. -/
theorem sum_length_classIdx (n : ℕ) (RAB : List ℕ) (r : ℕ) :
    ((List.range r).map fun r' => (classIdx n RAB r').length).sum =
      cntLt (clsKey RAB) r (n * n) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, cntLt_succ_left]
    simp [length_classIdx]

/-- An entry of the list of the starts. -/
theorem getD_classStarts (n p : ℕ) (RAB : List ℕ) {r : ℕ} (hr : r ≤ p) :
    (classStarts n p RAB).getD r 0 = cntLt (clsKey RAB) r (n * n) := by
  have h : r < p + 1 := by omega
  simp [classStarts, classStart, List.getD_eq_getElem?_getD, h, sum_length_classIdx]

/-- The pair number i stands at its place in the list of all the pairs, class after class. -/
theorem getD_sortedIdx (n p : ℕ) (RAB : List ℕ) {i : ℕ} (hi : i < n * n) (hk : clsKey RAB i < p) :
    (sortedIdx n p RAB).getD (sortPos (clsKey RAB) (n * n) i) 0 = i := by
  have ho : cntEq (clsKey RAB) (clsKey RAB i) i < (classIdx n RAB (clsKey RAB i)).length := by
    rw [length_classIdx]
    exact cntEq_lt_of_lt hi
  rw [sortedIdx, sortPos, ← sum_length_classIdx, List.getD_flatMap_range_sum _ hk ho]
  exact List.getD_filter_range_count (fun j => RAB.getD j 0 = clsKey RAB i) (n * n) hi rfl

/-- All the pairs are listed if all the keys are below `p`. -/
theorem length_sortedIdx (n p : ℕ) (RAB : List ℕ) (h : ∀ i < n * n, clsKey RAB i < p) :
    (sortedIdx n p RAB).length = n * n := by
  rw [sortedIdx, List.length_flatMap, sum_length_classIdx, cntLt_of_forall_lt h]

/-- What stands at the places of a stable sort is the list of the pairs, class after class. -/
theorem segN_map_sortedIdx {μ' : ℕ → ℤ} {n p : ℕ} {RAB : List ℕ}
    (hkeys : ∀ j < n * n, clsKey RAB j < p) {base : ℕ} (f : ℕ → ℕ)
    (h : ∀ j < n * n, μ' (base + sortPos (clsKey RAB) (n * n) j) = (f j : ℕ)) :
    SegN μ' base ((sortedIdx n p RAB).map f) := by
  have hlen := length_sortedIdx n p RAB hkeys
  intro q hq
  have hq' : q < n * n := by simpa [hlen] using hq
  obtain ⟨j, hj, rfl⟩ := exists_sortPos_eq (clsKey RAB) hq'
  have hg := getD_sortedIdx n p RAB hj (hkeys j hj)
  rw [List.getD_eq_getElem _ 0 (by rw [hlen]; exact hq')] at hg
  simp only [List.getElem_map, hg]
  exact h j hj

end pure

/-! ## The routine -/

namespace Classes




























end Classes










































































section phases

variable {μ μ' : ℕ → ℤ} {x : ClassesArgs}

/-- The keys are below p. -/
theorem ClassesPre.key_lt (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n) :
    clsKey x.RAB i < x.p := by
  have hl : i < x.RAB.length := pre.len ▸ hi
  rw [clsKey, List.getD_eq_getElem _ 0 hl]
  exact pre.lt _ (List.getElem_mem hl)

/-- The residues lie before the areas that are written, so they can be read at any time. -/
theorem ClassesPre.read (pre : ClassesPre lim μ x) (h : x.Same μ μ') {i : ℕ}
    (hi : i < x.n * x.n) : μ' (x.rab + i) = (clsKey x.RAB i : ℕ) := by
  have hl : i < x.RAB.length := pre.len ▸ hi
  have := pre.rab_le
  rw [h _ (by omega), pre.seg _ (by simpa using hl), List.getElem_map, clsKey,
    List.getD_eq_getElem _ 0 hl]


















variable {σ : State} (hw : (lim.space : ℤ) ≤ lim.word)

include hw

/-- cls[t] := 0 for t ≤ p. -/
theorem clsZero_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (fun _ => True) σ) :
    Ends lim P d clsZero σ (15 * x.p + 23) (ClsState μ x (ClsZeroed x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, -⟩ := h
  (obtain ⟨⟩ := id pre)
  refine Ends.forFrame
    (fun j μ'' => x.Same μ μ'' ∧ ∀ t < j, μ'' (x.cls + t) = 0) (x.p + 1)
    ⟨hrest, fun t ht => absurd ht (by omega)⟩ ?round ?done
  case round =>
    rintro j μ'' hj ⟨hr, hz⟩
    refine Ends.storeTo (x.cls + j) 0 ⟨rfl, hr.update ⟨by omega, by omega⟩ _, fun t ht => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (hz t ht)
    · exact Function.update_self ..
  case done =>
    exact fun μ'' ⟨hr, hz⟩ => ⟨_, ad, row, col, pl, μ'', rfl, hr, fun t ht => hz t (by omega)⟩

/-- cls[rab[i] + 1] += 1 for i < n². -/
theorem clsCount_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsZeroed x) σ) :
    Ends lim P d clsCount σ (23 * (x.n * x.n) + 6) (ClsState μ x (ClsCounted x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hz⟩ := h
  (obtain ⟨⟩ := id pre)
  refine Ends.for (fun j σ => ∃ (ad : ℤ) (μ'' : ℕ → ℤ),
      σ = ⟨frame (x.locals j ad row col pl), μ''⟩ ∧ x.Same μ μ'' ∧ μ'' x.cls = 0 ∧
      ∀ t < x.p, μ'' (x.cls + (t + 1)) = (cntEq (clsKey x.RAB) t j : ℕ)) (x.n * x.n) 15
    ?start ?round ?done ?bound
  case start =>
    exact ⟨ad, μ', by rw [update_frame_setLocal]; rfl, hrest, hz 0 (by omega),
      fun t ht => by simpa [cntEq] using hz (t + 1) (by omega)⟩
  case bound =>
    rintro j _ - - ⟨ad, μ'', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨ad, μ'', rfl, hr, hfirst, hc⟩
    exact ⟨_, ad, row, col, pl, μ'', rfl, hr, hfirst, hc⟩
  case round =>
    rintro j _ hj - ⟨ad, μ'', rfl, hr, hfirst, hc⟩
    have hread := pre.read hr hj
    have hk := pre.key_lt hj
    have hcell := hc _ hk
    have hle : cntEq (clsKey x.RAB) (clsKey x.RAB j) j ≤ j := Nat.count_le _
    have haddr :
        ((x.cls : ℤ) + ((clsKey x.RAB j : ℤ) + 1)).toNat = x.cls + (clsKey x.RAB j + 1) := by
      omega
    -- ad := cls + rab[i] + 1
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (x.cls + (clsKey x.RAB j + 1) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hread]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hread] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hread] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    -- mem[ad] := mem[ad] + 1
    refine Ends.storeTo (x.cls + (clsKey x.RAB j + 1))
      (cntEq (clsKey x.RAB) (clsKey x.RAB j) j + 1 : ℕ)
      ⟨by simp, _, _, by rw [update_frame_setLocal]; rfl, hr.update ⟨by omega, by omega⟩ _,
        (Function.update_of_ne (by omega) _ _).trans hfirst, fun t ht => ?_⟩
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hcell] <;> omega)))
    rw [cntEq_succ]
    by_cases e : clsKey x.RAB j = t
    · subst e
      rw [if_pos rfl, Function.update_self]
    · rw [if_neg e, Function.update_of_ne (by omega)]
      exact hc t ht

/-- cls[t] += cls[t - 1] for t = 1, …, p. -/
theorem clsPrefix_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsCounted x) σ) :
    Ends lim P d clsPrefix σ (25 * x.p + 8) (ClsState μ x (ClsStarts x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hfirst, hc⟩ := h
  (obtain ⟨⟩ := id pre)
  -- i := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (1 : ℕ)
            -- while i ≤ p; before round j the counter is j + 1, and the cells up to j hold the starts
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while i ≤ p; before round j the counter is j + 1, and the cells up to j hold the starts
  refine Ends.whileConst (fun j σ => ∃ μ'' : ℕ → ℤ,
      σ = ⟨frame (x.locals (j + 1 : ℕ) ad row col pl), μ''⟩ ∧ x.Same μ μ'' ∧
      (∀ t ≤ j, μ'' (x.cls + t) = (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) ∧
      ∀ t < x.p, j ≤ t → μ'' (x.cls + (t + 1)) = (cntEq (clsKey x.RAB) t (x.n * x.n) : ℕ)) x.p 19
    ?start ?round ?done (by first
                            |
                              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                (first
                                  | omega
                                  | ((ring_nf); (omega))))
                            | omega
                            |
                              (simp [] <;>
                                  first
                                  | omega
                                  | ((ring_nf); (omega))))
  case start =>
    refine ⟨μ', rfl, hrest, fun t ht => ?_, fun t ht _ => hc t ht⟩
    obtain rfl : t = 0 := by omega
    simpa [cntLt] using hfirst
  case done =>
    rintro _ ⟨μ'', rfl, hr, hs, -⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), _, ad, row, col, pl, μ'', rfl, hr, hs⟩
  case round =>
    rintro j _ hj ⟨μ'', rfl, hr, hs, hc⟩
    have hprev := hs j le_rfl
    have hcell := hc j hj le_rfl
    have hle : cntLt (clsKey x.RAB) (j + 1) (x.n * x.n) ≤ x.n * x.n := cntLt_le _ _ _
    have hsum := cntLt_succ_left (clsKey x.RAB) j (x.n * x.n)
    have haddr : ((x.cls : ℤ) + ((j : ℤ) + 1)).toNat = x.cls + (j + 1) := by omega
    have haddr' : ((x.cls : ℤ) + ((j : ℤ) + 1) - 1).toNat = x.cls + j := by omega
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- cls[i] := cls[i] + cls[i - 1]
    refine Ends.storeToThen (x.cls + (j + 1)) (cntLt (clsKey x.RAB) (j + 1) (x.n * x.n) : ℕ) ?_
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, haddr', hprev, hcell] <;>
                omega)))
    -- i := i + 1
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (j + 1 + 1 : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨_, rfl, hr.update ⟨by omega, by omega⟩ _, fun t ht => ?_,
      fun t ht hjt => (Function.update_of_ne (by omega) _ _).trans (hc t ht (by omega))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with ht | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (hs t (by omega))
    · exact Function.update_self ..





open Classes in
/-- cur[t] := cls[t] for t < p. -/
theorem clsCopy_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsStarts x) σ) :
    Ends lim P d clsCopy σ (16 * x.p + 6) (ClsState μ x (ClsCopied x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hs⟩ := h
  (obtain ⟨⟩ := id pre)
  refine Ends.pass (x := Prime) (y := Cur) (dst := x.cur) (n := x.p)
    (fun t => (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) (fun j hj => ?_) ?_ hw (by omega) rfl rfl
  · have hcell := (wrote_rest (μ := μ') (dst := x.cur) (j := j)
      (f := fun t => (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) (a := x.cls + j) (by omega)).trans
      (hs j (by omega))
    simp [Limits.Addr, abs_le, hcell]
    omega
  · rw [update_frame_setLocal]
    exact ⟨_, ad, row, col, pl, _, rfl,
      hrest.trans ((sameOutside_wrote le_rfl).mono (by omega) (by omega)),
      fun t ht => (wrote_rest (by omega)).trans (hs t ht), fun t ht => wrote_done ht⟩










omit hw in
/-- **The pair number i is placed**: its row and its column are written to its place, and the next
free place of its class moves on. -/
theorem ClsPlaced.step (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n)
    (h : ClsPlaced x i μ') :
    ClsPlaced x (i + 1)
      (Function.update (Function.update (Function.update μ'
        (x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i) (i / x.n : ℕ))
        (x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i) (i % x.n : ℕ))
        (x.cur + clsKey x.RAB i) (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ)) := by
  (obtain ⟨⟩ := id pre)
  have hk := pre.key_lt hi
  have hpos := sortPos_lt (clsKey x.RAB) hi
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun j hj => ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact h.keep t ht
  · rw [cntEq_succ]
    by_cases e : clsKey x.RAB i = t
    · subst e
      rw [Function.update_self, if_pos rfl, sortPos, Nat.add_assoc]
    · rw [if_neg e, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact h.next t ht
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have hne : sortPos (clsKey x.RAB) (x.n * x.n) j ≠ sortPos (clsKey x.RAB) (x.n * x.n) i :=
        fun e => absurd (eq_of_sortPos_eq (by omega) hi e) (by omega)
      have hlt := sortPos_lt (clsKey x.RAB) (show j < x.n * x.n by omega)
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.done j hj
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self, Function.update_of_ne (by omega), Function.update_self]
      exact ⟨rfl, rfl⟩

/-- **The pair number i is written to its place.** -/
theorem clsPlaceOne_ends (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n) (ad pl : ℤ)
    (hrest : x.Same μ μ') (h : ClsPlaced x i μ') :
    Ends lim P d clsPlaceOne ⟨frame (x.locals i ad (i / x.n : ℕ) (i % x.n : ℕ) pl), μ'⟩ 25
      fun σ' => ∃ (ad' pl' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (x.locals i ad' (i / x.n : ℕ) (i % x.n : ℕ) pl'), μ''⟩ ∧
          x.Same μ μ'' ∧ ClsPlaced x (i + 1) μ'' := by
  (obtain ⟨⟩ := id pre)
  have hread := pre.read hrest hi
  have hk := pre.key_lt hi
  have hpos : sortPos (clsKey x.RAB) (x.n * x.n) i < x.n * x.n := sortPos_lt (clsKey x.RAB) hi
  have hcell : μ' (x.cur + clsKey x.RAB i) = (sortPos (clsKey x.RAB) (x.n * x.n) i : ℕ) :=
    h.next _ hk
  have hrow := Nat.div_le_self i x.n
  have hcol := Nat.mod_le i x.n
  have hstep := h.step pre hi
  have hrest' := ((hrest.update (b := x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i)
    ⟨by omega, by omega⟩ (i / x.n : ℕ)).update (b := x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i)
    ⟨by omega, by omega⟩ (i % x.n : ℕ)).update (b := x.cur + clsKey x.RAB i) ⟨by omega, by omega⟩
    (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ)
  generalize i / x.n = row at *
  generalize i % x.n = col at *
  -- ad := cur + rab[i]; pl := mem[ad]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.cur + clsKey x.RAB i : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hread]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hread] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hread] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen (sortPos (clsKey x.RAB) (x.n * x.n) i : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcell]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcell] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcell] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- qi[pl] := row; qj[pl] := col; mem[ad] := pl + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.storeToThen (x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i)
          (row : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.storeToThen (x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i)
          (col : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.storeToThen (x.cur + clsKey x.RAB i)
          (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  exact ⟨_, _, _, rfl, hrest', hstep⟩

/-- All pairs go to their places. -/
theorem clsPlace_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsCopied x) σ) :
    Ends lim P d clsPlace σ (47 * (x.n * x.n) + 10) (ClsState μ x (ClsPlaced x (x.n * x.n))) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hs, hcur⟩ := h
  (obtain ⟨⟩ := id pre)
  -- row := 0; col := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (0 : ℕ)
            -- for i < nn
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- for i < nn
  refine Ends.for (fun j σ => ∃ (ad pl : ℤ) (μ'' : ℕ → ℤ),
      σ = ⟨frame (x.locals j ad (j / x.n : ℕ) (j % x.n : ℕ) pl), μ''⟩ ∧
        x.Same μ μ'' ∧ ClsPlaced x j μ'') (x.n * x.n) 39
    ?start ?round ?done ?bound
  case start =>
    exact ⟨ad, pl, μ', by rw [update_frame_setLocal, Nat.zero_div, Nat.zero_mod]; rfl, hrest, hs,
      fun t ht => by simpa [cntEq] using hcur t ht, fun j hj => absurd hj (by omega)⟩
  case bound =>
    rintro j _ - - ⟨ad, pl, μ'', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨ad, pl, μ'', rfl, hr, hp⟩
    exact ⟨_, ad, _, _, pl, μ'', rfl, hr, hp⟩
  case round =>
    rintro j _ hj - ⟨ad, pl, μ'', rfl, hr, hp⟩
    have hn : 0 < x.n := Nat.pos_of_ne_zero fun e => by simp [e] at hj
    have hnn : x.n ≤ x.n * x.n := Nat.le_mul_of_pos_left x.n hn
    refine Ends.next 25 ((clsPlaceOne_ends hw pre hj ad pl hr hp).mono le_rfl ?_)
    rintro _ ⟨ad', pl', μ₃, rfl, hr', hp'⟩
    refine Ends.nextPair ?_ hn (by omega) (by omega) rfl rfl rfl
    exact ⟨by simp, ad', pl', μ₃, by rw [update_frame_setLocal]; rfl, hr', hp'⟩

end phases

open Classes in
/-- **classes** writes the starts of the classes and the rows and columns of the pairs, class after
class. -/
theorem classes_meets {pClasses : ℕ} (hP : P[pClasses]? = some classesBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (x : ClassesArgs) (μ : ℕ → ℤ) (pre : ClassesPre lim μ x) :
    Meets lim P pClasses d x.vals μ (tClasses x.n x.p) fun _ μ' =>
      SegN μ' x.cls (classStarts x.n x.p x.RAB) ∧ SegN μ' x.qi (queryRows x.n x.p x.RAB) ∧
        SegN μ' x.qj (queryCols x.n x.p x.RAB) ∧ x.Same μ μ' := by
  refine .of_body hP ?_
  (obtain ⟨⟩ := id pre)
  unfold tClasses
  -- pairs := n * n
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.n * x.n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have h0 : ClsState μ x (fun _ => True) ⟨frame (setLocal x.vals Pairs (x.n * x.n : ℕ)), μ⟩ :=
    ⟨0, 0, 0, 0, 0, μ, by rw [← frame_append_zeros _ 5]; rfl, .refl, trivial⟩
  -- the five phases
  refine Ends.next _ ((clsZero_ends hw pre h0).mono le_rfl fun _ h1 => ?_)
  refine Ends.next _ ((clsCount_ends hw pre h1).mono le_rfl fun _ h2 => ?_)
  refine Ends.next _ ((clsPrefix_ends hw pre h2).mono le_rfl fun _ h3 => ?_)
  refine Ends.next _ ((clsCopy_ends hw pre h3).mono le_rfl fun _ h4 => ?_)
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (clsPlace_ends hw pre h4) ?_ ?_
      | refine Light.Ends.pieceLast (clsPlace_ends hw pre h4) ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => rintro _ ⟨_, _, _, _, _, μ', rfl, hrest, hp⟩)
  have hkeys : ∀ j < x.n * x.n, clsKey x.RAB j < x.p := fun j hj => pre.key_lt hj
  refine ⟨fun t ht => ?_, segN_map_sortedIdx hkeys _ fun j hj => (hp.done j hj).1,
    segN_map_sortedIdx hkeys _ fun j hj => (hp.done j hj).2, hrest⟩
  have hl : t < (classStarts x.n x.p x.RAB).length := by simpa using ht
  have ht' : t < x.p + 1 := by simpa [classStarts] using hl
  rw [List.getElem_map, ← List.getD_eq_getElem _ 0 hl, getD_classStarts x.n x.p x.RAB (by omega)]
  exact hp.keep t (by omega)

end Light.Sec3

end
end

section


/-!
# The table of the chunks

Proof of Theorem 17: "cut it into chunks of at most n²/√D query pairs".  chunks(cls, p, cap, cr, cl,
cw) goes through the `p` classes, whose starts are in the `p + 1` cells from `cls`, cuts each of
them into chunks of at most `cap` places, and writes the residues, the starts and the lengths of the
chunks to `cr`, `cl` and `cw`; the residue of a chunk is the number `rho < p` of its class.  It
returns the number of chunks (`chunks_meets`).  The proof follows the program: one chunk
(`chunksRound_runs`), the chunks of one class (`chunksClass_ends`), all classes.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Chunks

















end Chunks








































































/-! ## The pure side -/

section pure

/-- A class of `hi - lo` places has `⌈(hi - lo)/cap⌉` chunks. -/
theorem length_chunksOf (cap lo hi rho : ℕ) :
    (chunksOf cap lo hi rho).length = (hi - lo) ⌈/⌉ cap := by
  simp [chunksOf]





theorem length_chunkRow (cap : ℕ) (C : List ℕ) (rho : ℕ) :
    (chunkRow cap C rho).length = (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap :=
  length_chunksOf _ _ _ _





/-- At the start the table is empty. -/
theorem tabAt_zero_zero (cap : ℕ) (C : List ℕ) : tabAt cap C 0 0 = [] := by simp [tabAt]

/-- After all classes the table is complete. -/
theorem tabAt_end (p cap : ℕ) (C : List ℕ) : tabAt cap C p 0 = chunkTabOf p cap C := by
  rw [tabAt, List.take_zero, List.append_nil]
  rfl

/-- After the last chunk of a class the next class begins. -/
theorem tabAt_row (cap : ℕ) (C : List ℕ) (rho : ℕ) :
    tabAt cap C rho ((C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap)
      = tabAt cap C (rho + 1) 0 := by
  rw [tabAt, ← length_chunkRow, List.take_length, tabAt, List.range_succ, List.flatMap_append]
  simp

/-- One more chunk of the class `rho`. -/
theorem tabAt_succ (cap : ℕ) (C : List ℕ) (rho : ℕ) {i : ℕ}
    (hi : i < (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) :
    tabAt cap C rho (i + 1) = tabAt cap C rho i ++
      [⟨rho, C.getD rho 0 + i * cap, min cap (C.getD (rho + 1) 0 - C.getD rho 0 - i * cap)⟩] := by
  have hrow : i < (chunkRow cap C rho).length := by rw [length_chunkRow]; exact hi
  rw [tabAt, tabAt, ← List.take_append_getElem hrow, List.append_assoc]
  simp [chunkRow, chunksOf]

/-- As long as a chunk is missing, the table is shorter than the complete one. -/
theorem length_tabAt_lt {p cap : ℕ} (C : List ℕ) {rho i : ℕ} (hrho : rho < p)
    (hi : i < (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) :
    (tabAt cap C rho i).length < (chunkTabOf p cap C).length := by
  have hrow := length_chunkRow cap C rho
  have hrows :=
    List.sum_map_range_mono (fun r => (chunkRow cap C r).length) (show rho + 1 ≤ p by omega)
  rw [List.range_succ, List.map_append, List.sum_append] at hrows
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hrows
  have hall : (chunkTabOf p cap C).length
      = ((List.range p).map fun r => (chunkRow cap C r).length).sum := by
    rw [chunkTabOf, List.length_flatMap]
    rfl
  rw [hall, tabAt, List.length_append, List.length_flatMap, List.length_take]
  omega

/-- The time of the rounds, added up: 37 steps for each chunk and 24 for each class. -/
theorem sum_chunks_rounds (cap : ℕ) (C : List ℕ) (q : ℕ) :
    ∑ rho ∈ Finset.range q, (4 + (37 * ((C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) + 20))
      = 37 * (tabAt cap C q 0).length + 24 * q := by
  induction q with
  | zero => simp [tabAt]
  | succ q ih =>
    have hrow : (tabAt cap C (q + 1) 0).length
        = (tabAt cap C q 0).length + (C.getD (q + 1) 0 - C.getD q 0) ⌈/⌉ cap := by
      rw [← tabAt_row cap C q]
      simp [tabAt, length_chunkRow]
    rw [Finset.sum_range_succ, ih, hrow]
    omega

end pure

/-! ## The tables in the memory -/

variable {μ μ' : ℕ → ℤ} {x : ChunksArgs}








/-- One more chunk: each table gets one more entry, and the writes to the other two tables do not
touch it. -/
theorem TabInv.push {T : List Chunk} (h : TabInv μ μ' x T) (pre : ChunksPre lim μ x)
    (hlen : T.length < x.R) (c : Chunk) :
    TabInv μ (Function.update (Function.update (Function.update μ' (x.cr + T.length) c.residue)
      (x.cl + T.length) c.start) (x.cw + T.length) c.len) x (T ++ [c]) := by
  (obtain ⟨⟩ := id pre)
  have hr := h.sr.snoc c.residue
  have hl :=
    SegN.snoc (h.sl.update_out (b := x.cr + T.length) (by simp; omega) (c.residue : ℤ)) c.start
  have hw := SegN.snoc
    ((h.sw.update_out (b := x.cr + T.length) (by simp; omega) (c.residue : ℤ)).update_out
      (b := x.cl + T.length) (by simp; omega) (c.start : ℤ)) c.len
  simp only [List.length_map] at hr hl hw
  refine ⟨?_, ?_, ?_, fun b hb => ?_⟩
  · rw [List.map_append]
    exact (hr.update_out (by simp; omega) _).update_out (by simp; omega) _
  · rw [List.map_append]
    exact hl.update_out (by simp; omega) _
  · rw [List.map_append]
    exact hw
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact h.same b hb

/-- A start of a class, read from a memory in which only the tables have changed. -/
theorem ChunksPre.start (pre : ChunksPre lim μ x) (hsame : x.Same μ μ') {t : ℕ} (ht : t ≤ x.p) :
    μ' (x.cls + t) = ((x.C.getD t 0 : ℕ) : ℤ) ∧ x.C.getD t 0 ≤ x.B := by
  (obtain ⟨⟩ := id pre)
  have hlen : t < x.C.length := by omega
  rw [hsame _ ⟨by omega, by omega, by omega⟩, pre.seg.read hlen]
  exact ⟨rfl, by rw [List.getD_eq_getElem _ 0 hlen]; exact pre.le _ (List.getElem_mem hlen)⟩

/-! ## The program -/

variable (hw : (lim.space : ℤ) ≤ lim.word)

include hw

/-- One chunk. -/
theorem chunksRound_runs {rho pos hi cnt : ℕ} {len : ℤ} (hpos : pos < hi) (hhi : hi < lim.space)
    (hr : x.cr + cnt < lim.space) (hl : x.cl + cnt < lim.space) (hc : x.cw + cnt < lim.space) :
    chunksRound.Runs lim ⟨frame (x.locals rho pos hi cnt len), μ'⟩
      (· = ⟨frame (x.locals rho (pos + min x.cap (hi - pos) : ℕ) hi (cnt + 1 : ℕ)
          (min x.cap (hi - pos) : ℕ)),
        Function.update (Function.update (Function.update μ' (x.cr + cnt) rho) (x.cl + cnt) pos)
          (x.cw + cnt) (min x.cap (hi - pos) : ℕ)⟩) := by
  by_cases hcap : x.cap < hi - pos
  · have htest : (x.cap : ℤ) < (hi : ℤ) - pos := by omega
    rw [show min x.cap (hi - pos) = x.cap by omega]
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, chunksRound,
                        update_frame_setLocal, htest] <;>
                      omega)),
      by simp [chunksRound, update_frame_setLocal, htest]⟩
  · have htest : ¬ (x.cap : ℤ) < (hi : ℤ) - pos := by omega
    rw [show min x.cap (hi - pos) = hi - pos by omega]
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, chunksRound,
                        update_frame_setLocal, htest] <;>
                      omega)),
      by simp [chunksRound, update_frame_setLocal, htest, Nat.cast_sub hpos.le]⟩






/-- The chunks of one class. -/
theorem chunksClass_ends {rho : ℕ} {σ : State} (pre : ChunksPre lim μ x) (hrho : rho < x.p)
    (hσ : ChunksInv μ x rho (tabAt x.cap x.C rho 0) σ) :
    Ends lim P d chunksClass σ (37 * ((x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap) + 16)
      (ChunksInv μ x rho (tabAt x.cap x.C (rho + 1) 0)) := by
  obtain ⟨pos₀, end₀, len₀, μ', rfl, hT⟩ := hσ
  (obtain ⟨⟩ := id pre)
  have hroom : x.table.length ≤ x.R := pre.room
  obtain ⟨hreadLo, hloB⟩ := pre.start hT.same (show rho ≤ x.p by omega)
  obtain ⟨hreadHi, hhiB⟩ := pre.start hT.same (show rho + 1 ≤ x.p by omega)
  have hsucc := fun i hlt => tabAt_succ x.cap x.C rho (i := i) hlt
  have hlenlt : ∀ i, i < (x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap →
      (tabAt x.cap x.C rho i).length < x.table.length := fun i hlt => length_tabAt_lt x.C hrho hlt
  have hiff : ∀ i, i < (x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap ↔
      i * x.cap < x.C.getD (rho + 1) 0 - x.C.getD rho 0 := fun i => Nat.lt_ceilDiv_iff pre.hcap
  rw [← tabAt_row x.cap x.C rho]
  generalize x.C.getD rho 0 = lo at *
  generalize x.C.getD (rho + 1) 0 = hi at *
  generalize (hi - lo) ⌈/⌉ x.cap = rounds at *
  have haddr : ((x.cls : ℤ) + rho + 1).toNat = x.cls + (rho + 1) := by omega
  -- pos := cls[rho]; end := cls[rho + 1]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen lo ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hreadLo]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hreadLo] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadLo] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen hi ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr,
                hreadHi]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddr, hreadHi] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hreadHi] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while pos < end.  Before round i, the first i chunks of the class are in the tables.
  refine Ends.whileBlock (fun i σ => ∃ (len : ℤ) (μ₁ : ℕ → ℤ),
    σ = ⟨frame (x.locals rho (lo + min (i * x.cap) (hi - lo) : ℕ) hi
      (tabAt x.cap x.C rho i).length len), μ₁⟩ ∧
    TabInv μ μ₁ x (tabAt x.cap x.C rho i)) rounds ?start ?round ?done
    (by simp [chunksRound]; omega)
  case start => exact ⟨len₀, μ', by simp, hT⟩
  case round =>
    rintro i _ hround ⟨len, μ₁, rfl, hT₁⟩
    have hlt : i * x.cap < hi - lo := (hiff i).1 hround
    have hlen := hlenlt i hround
    have hpush := hT₁.push pre (by omega) ⟨rho, lo + i * x.cap, min x.cap (hi - lo - i * x.cap)⟩
    rw [← hsucc i hround] at hpush
    rw [show lo + min (i * x.cap) (hi - lo) = lo + i * x.cap by omega]
    refine ⟨by simp, by simp; omega, (chunksRound_runs hw (by omega) (by omega) (by omega)
      (by omega) (by omega)).mono ?_⟩
    rintro _ rfl
    have hleft : hi - (lo + i * x.cap) = hi - lo - i * x.cap := by omega
    have hnext : lo + i * x.cap + min x.cap (hi - lo - i * x.cap) =
        lo + min ((i + 1) * x.cap) (hi - lo) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hlength : (tabAt x.cap x.C rho (i + 1)).length = (tabAt x.cap x.C rho i).length + 1 := by
      rw [hsucc i hround, List.length_append, List.length_singleton]
    exact ⟨(min x.cap (hi - lo - i * x.cap) : ℕ), _, by rw [hleft, hnext, hlength], hpush⟩
  case done =>
    rintro _ ⟨len, μ₁, rfl, hT₁⟩
    have hge : ¬ rounds * x.cap < hi - lo := fun h => absurd ((hiff rounds).2 h) (lt_irrefl _)
    exact ⟨by simp, by simp; omega, _, _, _, _, rfl, hT₁⟩

omit hw in
/-- **chunks** writes the table of the chunks and returns their number. -/
theorem chunks_meets {pChunks : ℕ} (hP : P[pChunks]? = some chunksBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (x : ChunksArgs) (μ : ℕ → ℤ) (pre : ChunksPre lim μ x) :
    Meets lim P pChunks d x.vals μ (tChunks x.p x.table.length) fun r μ' =>
      r = (x.table.length : ℕ) ∧ SegN μ' x.cr (x.table.map (·.residue)) ∧
        SegN μ' x.cl (x.table.map (·.start)) ∧ SegN μ' x.cw (x.table.map (·.len)) ∧
        x.Same μ μ' := by
  refine .of_body hP ?_
  (obtain ⟨⟩ := id pre)
  have hsum := sum_chunks_rounds x.cap x.C x.p
  rw [tabAt_end, ← ChunksArgs.table] at hsum
  unfold tChunks
  -- rho := 0; cnt := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (0 : ℕ)
            -- while rho < p
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while rho < p
  refine Ends.next _ (Ends.while (fun rho σ => ChunksInv μ x rho (tabAt x.cap x.C rho 0) σ) x.p
    (fun rho => 37 * ((x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap) + 20) ?start ?round ?done)
    (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)
  case start =>
    refine ⟨0, 0, 0, μ, ?_, by simp [tabAt_zero_zero, SegN], by simp [tabAt_zero_zero, SegN],
      by simp [tabAt_zero_zero, SegN], .refl⟩
    simpa [tabAt_zero_zero] using
      (frame_append_zeros [(x.cls : ℤ), x.p, x.cap, x.cr, x.cl, x.cw, 0, 0, 0, 0] 1).symm
  case round =>
    rintro rho σ hrho hσ
    have hclass := chunksClass_ends (P := P) (d := d) hw pre hrho hσ
    obtain ⟨pos, hi, len, μ', rfl, -⟩ := hσ
    -- the chunks of the class rho; then rho := rho + 1
    refine ⟨by simp, by simp; omega, Ends.next _ (hclass.mono le_rfl ?_) (by omega)⟩
    rintro _ ⟨pos₁, hi₁, len₁, μ₁, rfl, hT⟩
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (rho + 1 : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    exact ⟨pos₁, hi₁, len₁, μ₁, by simp, hT⟩
  case done =>
    rintro _ ⟨pos, hi, len, μ', rfl, hT⟩
    rw [tabAt_end] at hT
    -- return cnt
    exact ⟨by simp, by simp, Ends.setTo ((tabAt x.cap x.C x.p 0).length : ℕ)
      ⟨by simp [tabAt_end], hT.sr, hT.sl, hT.sw, hT.same⟩ (by simp)
      (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩

end Light.Sec3

end
end

section


/-!
# The two matrices of an instance (proof of Theorem 17)

"a ∼ (c, σ) ⟺ σ ≡ w(a,c) + ϱ, (c, σ) ∼ b ⟺ σ ≡ -w(b,c) (mod p)."

writeY(y, rbc, n, D, p, c0, len) writes the D × n matrix Y of the instances for the piece
{c0, …, c0 + len - 1} of C: the middle vertex (c, σ) is the row (c - c0) p + σ.  The n² cells from
rbc hold the residues of the weights w(b,c) mod p, that of (b, c) at place b n + c.
writeX(x, rac, n, D, p, c0, len, rho) writes the n × D matrix X for the residue rho; the cells from
rac hold the residues of the weights w(a,c), that of (a, c) at place a n + c.  In the statements and
docstrings below, c counts from 0 within the piece: the c-th member of the piece is the vertex
c0 + c.

Both clear the matrix and then run through the pairs of a vertex and a member of the piece; each
pair marks one cell with a 1.  So both are instances of one pair of loops:

* `markVal` says what a cell holds when the pairs before (u, w) have been handled, and `Marked` says
  it of the memory;
* `markPairs` runs the two loops, given what the body does for one pair (`MarkCtx`);
* `writeYCell_spec` and `writeXCell_spec` treat the bodies: read a residue, form the label, mark the
  cell;
* `getElem_yList` and `getElem_xList` identify the marks of all pairs with the matrices.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Marking cells: the pure side -/

section marks












variable {pos : ℕ → ℕ → ℕ} {W u w i : ℕ}

theorem markVal_zero : markVal pos W 0 0 i = 0 := by
  unfold markVal
  rw [if_neg]
  rintro ⟨u', w', h, -, -⟩
  omega

theorem markVal_step (hlt : w < W) :
    markVal pos W u (w + 1) i = if i = pos u w then 1 else markVal pos W u w i := by
  unfold markVal
  by_cases h : i = pos u w
  · rw [if_pos h, if_pos ⟨u, w, Or.inr ⟨rfl, by omega⟩, hlt, h.symm⟩]
  · rw [if_neg h]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨u', w', h1, h2, h3⟩
      refine ⟨u', w', ?_, h2, h3⟩
      rcases h1 with h1 | ⟨rfl, h1⟩
      · exact Or.inl h1
      · refine Or.inr ⟨rfl, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h4 | rfl
        · exact h4
        · exact absurd h3.symm h
    · rintro ⟨u', w', h1, h2, h3⟩
      exact ⟨u', w', by omega, h2, h3⟩

theorem markVal_row : markVal pos W u W i = markVal pos W (u + 1) 0 i := by
  unfold markVal
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u', w', h1, h2, h3⟩
    exact ⟨u', w', by omega, h2, h3⟩
  · rintro ⟨u', w', h1, h2, h3⟩
    exact ⟨u', w', by omega, h2, h3⟩

/-- At the end, a cell is marked iff it is the cell of one of the pairs. -/
theorem markVal_end {U : ℕ} (q : Prop) [Decidable q] (h : q ↔ ∃ u' < U, ∃ w' < W, pos u' w' = i) :
    markVal pos W U 0 i = if q then 1 else 0 := by
  unfold markVal
  have : CellMarked pos W U 0 i ↔ q := by
    rw [h]
    constructor
    · rintro ⟨u', w', h1, h2, h3⟩
      exact ⟨u', by omega, w', h2, h3⟩
    · rintro ⟨u', h1, w', h2, h3⟩
      exact ⟨u', w', Or.inl h1, h2, h3⟩
  by_cases hq : q
  · rw [if_pos hq, if_pos (this.2 hq)]
  · rw [if_neg hq, if_neg fun h' => hq (this.1 h')]

end marks

/-! ## Marking cells: the memory -/







namespace Marked

variable {μ μ' : ℕ → ℤ} {base m : ℕ} {pos : ℕ → ℕ → ℕ} {U W u w : ℕ}

/-- After the clearing no pair has been handled. -/
theorem start (hzero : ∀ i < m, μ' (base + i) = 0) (hrest : SameOutside μ μ' base m) :
    Marked μ μ' base m pos W 0 0 :=
  ⟨fun i hi => by rw [markVal_zero]; exact hzero i hi, hrest⟩

/-- The pair (u, w) marks its cell. -/
theorem step (h : Marked μ μ' base m pos W u w) (hlt : w < W) (hpos : pos u w < m) :
    Marked μ (Function.update μ' (base + pos u w) 1) base m pos W u (w + 1) := by
  refine ⟨fun i hi => ?_, h.rest.update ⟨by omega, by omega⟩ _⟩
  rw [markVal_step hlt]
  split_ifs with e
  · rw [e, Function.update_self]
  · rw [Function.update_of_ne (by omega)]
    exact h.cells i hi

/-- The end of a row of pairs is the beginning of the next row. -/
theorem row (h : Marked μ μ' base m pos W u W) : Marked μ μ' base m pos W (u + 1) 0 :=
  ⟨fun i hi => by rw [← markVal_row]; exact h.cells i hi, h.rest⟩

/-- When all pairs have been handled, the cells hold the list of all marks. -/
theorem seg {l : List ℤ} (h : Marked μ μ' base m pos W U 0) (hlen : l.length = m)
    (hget : ∀ i (hi : i < l.length), l[i] = markVal pos W U 0 i) : Seg μ' base l :=
  fun i hi => by rw [hget i hi]; exact h.cells i (hlen ▸ hi)

end Marked

/-! ## Marking cells: the two loops -/




















section loops

variable {μ μ' : ℕ → ℤ} {base m U W b : ℕ} {pos : ℕ → ℕ → ℕ} {cu cw : ℕ} {hiU hiW : Expr}
  {cell : Stmt} {L : ℤ → ℤ → ℤ → List ℤ}

/-- The inner loop: the pairs (u, 0), …, (u, W - 1) mark their cells. -/
theorem markRow (C : MarkCtx lim P d μ base m U W b pos cu cw hiU hiW cell L) {u : ℕ} (hu : u < U)
    (w₀ t₀ : ℤ) (h : Marked μ μ' base m pos W u 0) :
    Ends lim P d (.for cw hiW cell) ⟨frame (L u w₀ t₀), μ'⟩ (W * (hiW.cost + b + 7) + hiW.cost + 5)
      fun σ' => ∃ w t μ'', σ' = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W (u + 1) 0 := by
  refine Ends.for
    (fun w σ => ∃ t μ'', σ = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W u w) W b
    ?start ?round ?done ?bound C.wordW le_rfl
  case start => exact ⟨t₀, μ', by simp only [update_frame_setLocal, C.setW, Nat.cast_zero], h⟩
  case bound =>
    rintro w _ - - ⟨t, μ'', rfl, -⟩
    exact C.boundW _ _ _ _
  case round =>
    rintro w _ hlt - ⟨t, μ'', rfl, hm⟩
    refine (C.cell_spec u w t μ'' hu hlt hm.rest).mono le_rfl ?_
    rintro _ ⟨t', rfl⟩
    exact ⟨C.atW _ _ _, t', _,
      by simp only [update_frame_setLocal, C.setW, Nat.cast_add, Nat.cast_one],
      hm.step hlt (C.pos_lt u w hu hlt)⟩
  case done =>
    rintro _ - ⟨t, μ'', rfl, hm⟩
    exact ⟨W, t, μ'', rfl, hm.row⟩

/-- **The two loops**: all pairs mark their cells. -/
theorem markPairs (C : MarkCtx lim P d μ base m U W b pos cu cw hiU hiW cell L) (u₀ w₀ t₀ : ℤ)
    (h : Marked μ μ' base m pos W 0 0) :
    Ends lim P d (.for cu hiU (.for cw hiW cell)) ⟨frame (L u₀ w₀ t₀), μ'⟩
      (U * (hiU.cost + (W * (hiW.cost + b + 7) + hiW.cost + 5) + 7) + hiU.cost + 5)
      fun σ' => Marked μ σ'.mem base m pos W U 0 := by
  refine Ends.for
    (fun u σ => ∃ w t μ'', σ = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W u 0) U _
    ?start ?round ?done ?bound C.wordU le_rfl
  case start => exact ⟨w₀, t₀, μ', by simp only [update_frame_setLocal, C.setU, Nat.cast_zero], h⟩
  case bound =>
    rintro u _ - - ⟨w, t, μ'', rfl, -⟩
    exact C.boundU _ _ _ _
  case round =>
    rintro u _ hu - ⟨w, t, μ'', rfl, hm⟩
    refine (markRow C hu w t hm).mono le_rfl ?_
    rintro _ ⟨w', t', μ₃, rfl, hm'⟩
    exact ⟨C.atU _ _ _, w', t', μ₃,
      by simp only [update_frame_setLocal, C.setU, Nat.cast_add, Nat.cast_one], hm'⟩
  case done =>
    rintro _ - ⟨w, t, μ'', rfl, hm⟩
    exact hm

end loops

/-! ## Clearing the matrix -/

/-- The loop that clears a matrix: local 0 holds its address base, local t the number m of its
cells, and local c is the counter.  Afterwards the m cells hold 0, and no other cell has changed. -/
theorem clear_spec {μ : ℕ → ℤ} {l : List ℤ} {c t base m : ℕ} {Q : State → Prop}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base + m < lim.space) (hc : 0 ≠ c) (ht : t ≠ c)
    (hbase : frame l 0 = base) (hm : frame l t = m)
    (h : ∀ μ', (∀ i < m, μ' (base + i) = 0) → SameOutside μ μ' base m →
      Q ⟨frame (setLocal l c m), μ'⟩) :
    Ends lim P d (.for c (v t) (.store (((Light.Expr.op Light.Op.add) (v 0) (v c))) (k 0))) ⟨frame l, μ⟩ (13 * m + 6) Q := by
  refine Ends.pass (x := t) (y := 0) (dst := base) (n := m) (fun _ => 0)
    (fun j _ => ⟨?_, by simp⟩) ?_ hw (by omega) hm hbase ht hc
  · change ((0 : ℕ) : ℤ) ≤ lim.word
    omega
  · rw [update_frame_setLocal]
    exact h _ (fun i hi => wrote_done hi) (sameOutside_wrote le_rfl)

/-! ## What both routines assume -/


















namespace WritePre

variable {μ μ' : ℕ → ℤ} {base m res n D p c0 len : ℕ} {R : List ℕ}

/-- The number n of vertices fits in a word. -/
theorem n_le_word (pre : WritePre lim μ base m res n D p c0 len R) : (n : ℤ) ≤ lim.word := by
  have := pre.hw
  have := pre.spaceR
  have := Nat.le_mul_self n
  omega

/-- The length of the piece fits in a word. -/
theorem len_le_word (pre : WritePre lim μ base m res n D p c0 len R) : (len : ℤ) ≤ lim.word := by
  have := pre.n_le_word
  have := pre.piece
  omega

/-- The place of the weight between the vertex u and the c-th member c0 + c of the piece. -/
theorem index_lt (pre : WritePre lim μ base m res n D p c0 len R) {u c : ℕ} (hu : u < n)
    (hc : c < len) : u * n + c0 + c < n * n := by
  have := pre.piece
  have := Nat.mul_add_lt_mul hu (show c0 + c < n by omega)
  omega

/-- The residues can be read at any time. -/
theorem read (pre : WritePre lim μ base m res n D p c0 len R) (h : SameOutside μ μ' base m) {i : ℕ}
    (hi : i < n * n) : μ' (res + i) = (R.getD i 0 : ℕ) := by
  have hap := pre.apart
  have hil : i < R.length := pre.length ▸ hi
  rw [h _ (by omega), pre.seg _ (by simpa using hil), List.getElem_map,
    List.getD_eq_getElem _ 0 hil]

/-- The residues are below p. -/
theorem getD_lt (pre : WritePre lim μ base m res n D p c0 len R) {i : ℕ} (hi : i < n * n) :
    R.getD i 0 < p := by
  have hil : i < R.length := pre.length ▸ hi
  rw [List.getD_eq_getElem _ 0 hil]
  exact pre.lt _ (List.getElem_mem hil)

/-- The label s of the c-th member of the piece is one of the D middle vertices. -/
theorem middle_lt (pre : WritePre lim μ base m res n D p c0 len R) {c s : ℕ} (hc : c < len)
    (hs : s < p) : c * p + s < D :=
  (Nat.mul_add_lt_mul hc hs).trans_le pre.fits

end WritePre

/-! ## The matrix Y -/

namespace WriteY
















end WriteY

























/-- Entry i of yList, the matrix Y row by row, is 1 if one of the pairs (c, b) marks the cell i, and
0 if not. -/
theorem getElem_yList {n D p c0 len : ℕ} {RBC : List ℕ} (hp : 0 < p) {i : ℕ}
    (hi : i < (yList n D p c0 len RBC).length) :
    (yList n D p c0 len RBC)[i] = markVal (posY n p c0 RBC) n len 0 i := by
  have hi' : i < D * n := by simpa [yList] using hi
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi'
  rw [markVal_end
    (i / n / p < len ∧ i / n % p = (p - RBC.getD (i % n * n + c0 + i / n / p) 0) % p)]
  · simp [yList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / n / p, h1, i % n, Nat.mod_lt _ hn, ?_⟩
      rw [posY, labY, ← h2, Nat.mul_comm (i / n / p) p, Nat.div_add_mod, Nat.mul_comm (i / n) n,
        Nat.div_add_mod]
    · rintro ⟨c, hc, b, hb, rfl⟩
      have hl : labY n p c0 RBC c b < p := Nat.mod_lt _ hp
      rw [posY, Nat.mul_add_div_of_lt hb, Nat.mul_add_mod_of_lt hb, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section writeY

variable {μ μ' : ℕ → ℤ} {y rbc n D p c0 len : ℕ} {RBC : List ℕ}

/-- The cell of a pair lies in the matrix. -/
theorem posY_lt (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) {c b : ℕ} (hc : c < len)
    (hb : b < n) : posY n p c0 RBC c b < D * n := by
  have hp := pre.getD_lt (pre.index_lt hb hc)
  exact Nat.mul_add_lt_mul (pre.middle_lt hc (Nat.mod_lt _ (by omega))) hb

/-- The label, as the program computes it. -/
theorem labY_eq {c b : ℕ} (hr : RBC.getD (b * n + c0 + c) 0 < p) : labY n p c0 RBC c b =
    if RBC.getD (b * n + c0 + c) 0 = 0 then 0 else p - RBC.getD (b * n + c0 + c) 0 := by
  unfold labY
  split_ifs with h
  · rw [h, Nat.sub_zero, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

open WriteY in
/-- **One pair of writeY.** -/
theorem writeYCell_spec (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) {c b : ℕ} (t : ℤ)
    (hc : c < len) (hb : b < n) (hrest : SameOutside μ μ' y (D * n)) :
    Ends lim P d writeYCell ⟨frame [y, rbc, n, D, p, c0, len, c, b, t, (D * n : ℕ)], μ'⟩ 32
      fun σ' => ∃ t', σ' = ⟨frame [y, rbc, n, D, p, c0, len, c, b, t', (D * n : ℕ)],
        Function.update μ' (y + posY n p c0 RBC c b) 1⟩ := by
  (obtain ⟨⟩ := id pre)
  have hidx := pre.index_lt hb hc
  have hread := pre.read hrest hidx
  have hr := pre.getD_lt hidx
  have hlab := labY_eq hr
  have hpos : (c * p + labY n p c0 RBC c b) * n + b < D * n := posY_lt pre hc hb
  have hrow : c * p + labY n p c0 RBC c b < D := pre.middle_lt hc (Nat.mod_lt _ (by omega))
  have hDn : D ≤ D * n := Nat.le_mul_of_pos_right D (by omega)
  have hposZ : ((c : ℤ) * p + labY n p c0 RBC c b) * n + b < D * n := by exact_mod_cast hpos
  have hpos0 : 0 ≤ ((c : ℤ) * p + labY n p c0 RBC c b) * n := by positivity
  have haddr : ((rbc : ℤ) + b * n + c0 + c).toNat = rbc + (b * n + c0 + c) := by omega
  generalize RBC.getD (b * n + c0 + c) 0 = r at hread hr hlab
  -- y[(c p + r) n + b] := 1, once r is the label
  have mark : ∀ s : ℕ, labY n p c0 RBC c b = s →
      Ends lim P d (.store (((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.add) (v Y)
                                ((Light.Expr.op Light.Op.mul)
                                  ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v C) (v PR))
                                    (v R))
                                  (v N)))
                              (v B))) (k 1))
        ⟨frame [y, rbc, n, D, p, c0, len, c, b, s, (D * n : ℕ)], μ'⟩ 13 fun σ' =>
          ∃ t', σ' = ⟨frame [y, rbc, n, D, p, c0, len, c, b, t', (D * n : ℕ)],
            Function.update μ' (y + posY n p c0 RBC c b) 1⟩ := by
    rintro _ rfl
    exact Ends.storeTo (y + posY n p c0 RBC c b) 1 ⟨_, rfl⟩
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, posY] <;> omega)))
  -- r := rbc[b n + c0 + c]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (r : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr,
                hread]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddr, hread] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hread] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- if r ≠ 0 then r := p - r
  refine Ends.next 8 (Ends.iteLast (fun h0 => Ends.skip (mark _ ?_)) fun h0 =>
    Ends.setTo (p - r : ℕ) (mark _ ?_))
  · have h0 : r = 0 := by simpa using h0
    rw [hlab, if_pos h0, h0]
  · have h0 : r ≠ 0 := by simpa using h0
    rw [hlab, if_neg h0]

open WriteY in
/-- The two loops of writeY are loops that mark cells. -/
theorem writeY_markCtx (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) :
    MarkCtx lim P d μ y (D * n) len n 32 (posY n p c0 RBC) C B (v LEN) (v N) writeYCell
      fun c b t => [y, rbc, n, D, p, c0, len, c, b, t, (D * n : ℕ)] where
  wordU := pre.len_le_word
  wordW := pre.n_le_word
  atU _ _ _ := rfl
  atW _ _ _ := rfl
  setU _ _ _ _ := rfl
  setW _ _ _ _ := rfl
  boundU _ _ _ _ := by simp
  boundW _ _ _ _ := by simp
  pos_lt _ _ hc hb := posY_lt pre hc hb
  cell_spec _ _ t _ hc hb hrest := writeYCell_spec pre t hc hb hrest

open WriteY in
/-- **writeY** writes the matrix Y and changes nothing else. -/
theorem writeY_spec (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) :
    Ends lim P d writeYBody ⟨frame [y, rbc, n, D, p, c0, len], μ⟩ (tWriteY n D len) fun σ' =>
      Seg σ'.mem y (yList n D p c0 len RBC) ∧ SameOutside μ σ'.mem y (D * n) := by
  (obtain ⟨⟩ := id pre)
  unfold tWriteY
  -- sz := D n
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (D * n : ℕ)
            -- for c < sz: y[c] := 0
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- for c < sz: y[c] := 0
  refine Ends.next _
    (clear_spec pre.hw pre.spaceM (by decide) (by decide) rfl rfl fun μ' hzero hrest => ?_)
  -- for c < len: for b < n: the pair (c, b) marks its cell
  refine ((markPairs (writeY_markCtx pre) _ _ _ (.start hzero hrest)).mono ?_ fun σ' hm =>
    ⟨hm.seg (by simp [yList]) fun i hi => getElem_yList ?_ hi, hm.rest⟩)
  · first
     |
       ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
             List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
         (first
           | omega
           | ((ring_nf); (omega))))
     | omega
     |
       (simp [] <;>
           first
           | omega
           | ((ring_nf); (omega)))
  · have hi' : i < D * n := by simpa [yList] using hi
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi'
    have hl : 0 < RBC.length := by rw [pre.length]; exact Nat.mul_pos hn hn
    have := pre.lt _ (List.getElem_mem hl)
    omega

end writeY

/-! ## The matrix X -/

namespace WriteX

















end WriteX


























/-- Entry i of xList, the matrix X row by row, is 1 if one of the pairs (a, c) marks the cell i, and
0 if not. -/
theorem getElem_xList {n D p c0 len rho : ℕ} {RAC : List ℕ} (hp : 0 < p) (hD : len * p ≤ D) {i : ℕ}
    (hi : i < (xList n D p c0 len rho RAC).length) :
    (xList n D p c0 len rho RAC)[i] = markVal (posX n D p c0 rho RAC) len n 0 i := by
  have hi' : i < n * D := by simpa [xList] using hi
  rw [markVal_end
    (i % D / p < len ∧ i % D % p = (RAC.getD (i / D * n + c0 + i % D / p) 0 + rho) % p)]
  · simp [xList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / D, Nat.div_lt_of_lt_mul' hi', i % D / p, h1, ?_⟩
      rw [posX, labX, ← h2, Nat.mul_comm (i % D / p) p, Nat.div_add_mod, Nat.mul_comm (i / D) D,
        Nat.div_add_mod]
    · rintro ⟨a, ha, c, hc, rfl⟩
      have hl : labX n p c0 rho RAC a c < p := Nat.mod_lt _ hp
      have hcol : c * p + labX n p c0 rho RAC a c < D := (Nat.mul_add_lt_mul hc hl).trans_le hD
      rw [posX, Nat.mul_add_div_of_lt hcol, Nat.mul_add_mod_of_lt hcol, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section writeX

variable {μ μ' : ℕ → ℤ} {x rac n D p c0 len rho : ℕ} {RAC : List ℕ}

/-- The cell of a pair lies in the matrix. -/
theorem posX_lt (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) {a c : ℕ} (ha : a < n)
    (hc : c < len) : posX n D p c0 rho RAC a c < n * D := by
  have hp := pre.getD_lt (pre.index_lt ha hc)
  exact Nat.mul_add_lt_mul ha (pre.middle_lt hc (Nat.mod_lt _ (by omega)))

/-- The label, as the program computes it. -/
theorem labX_eq {a c : ℕ} (hr : RAC.getD (a * n + c0 + c) 0 < p) (hrho : rho < p) :
    labX n p c0 rho RAC a c = if RAC.getD (a * n + c0 + c) 0 + rho < p
      then RAC.getD (a * n + c0 + c) 0 + rho else RAC.getD (a * n + c0 + c) 0 + rho - p := by
  unfold labX
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

open WriteX in
/-- **One pair of writeX.** -/
theorem writeXCell_spec (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p)
    {a c : ℕ} (t : ℤ) (ha : a < n) (hc : c < len) (hrest : SameOutside μ μ' x (n * D)) :
    Ends lim P d writeXCell ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t, (n * D : ℕ)], μ'⟩ 34
      fun σ' => ∃ t', σ' = ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t', (n * D : ℕ)],
        Function.update μ' (x + posX n D p c0 rho RAC a c) 1⟩ := by
  (obtain ⟨⟩ := id pre)
  have hidx := pre.index_lt ha hc
  have hread := pre.read hrest hidx
  have hr := pre.getD_lt hidx
  have hlab := labX_eq hr hrho
  have hpos : a * D + (c * p + labX n p c0 rho RAC a c) < n * D := posX_lt pre ha hc
  have haddr : ((rac : ℤ) + a * n + c0 + c).toNat = rac + (a * n + c0 + c) := by omega
  generalize RAC.getD (a * n + c0 + c) 0 = r at hread hr hlab
  -- x[a D + c p + t] := 1, once t is the label
  have mark : ∀ s : ℕ, labX n p c0 rho RAC a c = s →
      Ends lim P d (.store (((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.add)
                                ((Light.Expr.op Light.Op.add) (v X)
                                  ((Light.Expr.op Light.Op.mul) (v A) (v DD)))
                                ((Light.Expr.op Light.Op.mul) (v C) (v PR)))
                              (v T))) (k 1))
        ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, s, (n * D : ℕ)], μ'⟩ 13 fun σ' =>
          ∃ t', σ' = ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t', (n * D : ℕ)],
            Function.update μ' (x + posX n D p c0 rho RAC a c) 1⟩ := by
    rintro _ rfl
    exact Ends.storeTo (x + posX n D p c0 rho RAC a c) 1 ⟨_, rfl⟩ (by (((try have := Light.Std.space_le (by assumption)));
                                                                            ((try have := Light.Std.const_le (by assumption)));
                                                                            (simp [Light.Limits.Addr, abs_le, -abs_mul, posX] <;> omega)))
  -- t := rac[a n + c0 + c] + rho
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (r + rho : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr,
                hread]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddr, hread] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hread] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- if p ≤ t then t := t - p
  refine Ends.next 8 (Ends.iteLast (fun h0 => Ends.skip (mark _ ?_)) fun h0 => ?_)
  · have h0 : r + rho < p := by simp at h0; omega
    rw [hlab, if_pos h0]
  · have h0 : ¬ r + rho < p := by simp at h0; omega
    exact Ends.setTo (r + rho - p : ℕ) (mark _ (by rw [hlab, if_neg h0]))

open WriteX in
/-- The two loops of writeX are loops that mark cells. -/
theorem writeX_markCtx (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p) :
    MarkCtx lim P d μ x (n * D) n len 34 (posX n D p c0 rho RAC) A C (v N) (v LEN) writeXCell
      fun a c t => [x, rac, n, D, p, c0, len, rho, a, c, t, (n * D : ℕ)] where
  wordU := pre.n_le_word
  wordW := pre.len_le_word
  atU _ _ _ := rfl
  atW _ _ _ := rfl
  setU _ _ _ _ := rfl
  setW _ _ _ _ := rfl
  boundU _ _ _ _ := by simp
  boundW _ _ _ _ := by simp
  pos_lt _ _ ha hc := posX_lt pre ha hc
  cell_spec _ _ t _ ha hc hrest := writeXCell_spec pre hrho t ha hc hrest

open WriteX in
/-- **writeX** writes the matrix X and changes nothing else. -/
theorem writeX_spec (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p) :
    Ends lim P d writeXBody ⟨frame [x, rac, n, D, p, c0, len, rho], μ⟩ (tWriteX n D len) fun σ' =>
      Seg σ'.mem x (xList n D p c0 len rho RAC) ∧ SameOutside μ σ'.mem x (n * D) := by
  (obtain ⟨⟩ := id pre)
  unfold tWriteX
  -- sz := n D
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (n * D : ℕ)
            -- for a < sz: x[a] := 0
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- for a < sz: x[a] := 0
  refine Ends.next _
    (clear_spec pre.hw pre.spaceM (by decide) (by decide) rfl rfl fun μ' hzero hrest => ?_)
  -- for a < n: for c < len: the pair (a, c) marks its cell
  refine ((markPairs (writeX_markCtx pre hrho) _ _ _ (.start hzero hrest)).mono ?_ fun σ' hm =>
    ⟨hm.seg (by simp [xList]) fun i hi => getElem_xList (by omega) pre.fits hi, hm.rest⟩)
  first
  |
    ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
      (first
        | omega
        | ((ring_nf); (omega))))
  | omega
  |
    (simp [] <;>
        first
        | omega
        | ((ring_nf); (omega)))

end writeX

end Light.Sec3

end
end

section


/-!
# The parameters of Theorems 17 and 19, without division and without roots

The proof of Theorem 19 chooses D as "the largest power of four with D ≤ n^{1/18}"
and g := ⌈D^{1/36}⌉, or D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉; the reduction of Theorem 17 uses
⌊n²/√D⌋ and quotients rounded up.  The language has neither division nor roots, so all of these are
found by counting up.  A power is compared with a bound without forming a number above the bound
times the base.

* powLt(g, e, t), for g ≥ 1, returns 1 if g^e < t, and 0 if not (`powLt_meets`); what it holds after
  i factors is `capPow g t i`.
* rootCeil(e, t) returns the least g with g^e ≥ t (`rootCeil_meets`).
* The four parameters; 5 and 26 stand for the two routes of Theorem 19, through Theorem 5 and
  through Corollary 26.  d5(n) returns the largest power of four that is at most n^{1/18}, g5(D)
  returns ⌈D^{1/36}⌉, d26(n) returns ⌊n^{1/18}⌋, and g26(D) returns ⌈D^{0.0315}⌉; g5 and g26
  are for D ≥ 1 (`d5_spec`, `g5_spec`, `d26_spec`, `g26_spec`).
* queryCapNat(n, D) returns ⌊n²/√D⌋, and ceilDiv(a, b) returns ⌈a/b⌉ (`queryCapNat_meets`,
  `ceilDiv_meets`).

No routine touches the memory.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/







/-- One more factor. -/
theorem capPow_succ (g t i : ℕ) :
    capPow g t (i + 1) = if capPow g t i < t then capPow g t i * g else capPow g t i := rfl

/-- Below t the value is the power, and a value that has reached t shows that the power has. -/
theorem capPow_spec {g : ℕ} (hg : 1 ≤ g) (t i : ℕ) :
    (capPow g t i < t → capPow g t i = g ^ i) ∧ (t ≤ capPow g t i → t ≤ g ^ i) := by
  induction i with
  | zero => simp [capPow]
  | succ i ih =>
    rw [capPow_succ]
    split_ifs with h
    · rw [ih.1 h, pow_succ]
      exact ⟨fun _ => rfl, fun h' => h'⟩
    · exact ⟨fun h' => absurd h' h,
        fun _ => (ih.2 (not_lt.1 h)).trans (Nat.pow_le_pow_right hg (Nat.le_succ i))⟩

/-- The value is below t exactly if the power is. -/
theorem capPow_lt_iff {g : ℕ} (hg : 1 ≤ g) (t i : ℕ) : capPow g t i < t ↔ g ^ i < t := by
  obtain ⟨hlow, hhigh⟩ := capPow_spec hg t i
  exact ⟨fun h => hlow h ▸ h, fun h => not_le.1 fun hc => absurd (hhigh hc) (not_le.2 h)⟩

namespace PowLt









end PowLt











/-- **powLt**, for g ≥ 1, returns 1 if g^e < t and 0 if not, in at most 16 e + 14 steps.  It forms
no number above t g + e + 1. -/
theorem powLt_meets {μ : ℕ → ℤ} {pPow g e t : ℕ} (hP : P[pPow]? = some powLtBody) (hg : 1 ≤ g)
    (hword : ((t * g + e + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pPow d [g, e, t] μ (16 * e + 14) fun r μ' =>
      r = (if g ^ e < t then 1 else 0) ∧ μ' = μ := by
  refine .of_body hP ?_
  push_cast at hword
  have htg : (0 : ℤ) ≤ (t : ℤ) * g := by positivity
  -- cnt := 0; prod := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (1 : ℕ)
            -- while cnt < e.  Before round i, cnt = i and prod = capPow g t i.
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while cnt < e.  Before round i, cnt = i and prod = capPow g t i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [g, e, t, i, (capPow g t i : ℕ)], μ⟩) e (by simp [capPow]) ?round ?done
    le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    rw [capPow_succ]
    generalize capPow g t i = c
    -- if prod < t then prod := prod * g; cnt := cnt + 1
    by_cases hlt : c < t
    · have hmul : (c : ℤ) * g ≤ t * g := by exact_mod_cast Nat.mul_le_mul_right g hlt.le
      have hmul0 : (0 : ℤ) ≤ (c : ℤ) * g := by positivity
      exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                    ((try have := Light.Std.const_le (by assumption)));
                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                    ((try have := Light.Std.const_le (by assumption)));
                                                                                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                    ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                    (simp [Light.Limits.Addr, abs_le, -abs_mul, hlt] <;> omega)),
        by simp [update_frame_setLocal, hlt]⟩
    · exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                     ((try have := Light.Std.const_le (by assumption)));
                     (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                     ((try have := Light.Std.const_le (by assumption)));
                                                                                     (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [abs_le, hlt]; omega,
        by simp [update_frame_setLocal, hlt]⟩
  case done =>
    rintro _ rfl
    have hiff := capPow_lt_iff hg t e
    -- return 1 if prod < t, and 0 if not
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      Ends.iteLast (fun h => ?_) (fun h => ?_) (hT := by simp; omega)⟩
    · have hlt : g ^ e < t := hiff.1 (by simpa using h)
      exact Ends.setTo 1 (by simp [hlt]) (hT := by simp; omega)
    · have hlt : ¬ g ^ e < t := fun h' => h (by simpa using hiff.2 h')
      exact Ends.setTo 0 (by simp [hlt]) (hT := by simp; omega)

/-! ## Roots, rounded up -/

namespace RootCeil







end RootCeil














/-- **rootCeil** returns the least g with g^e ≥ t, for e ≥ 1 and t ≥ 1.  It forms no number above t
times the result plus e + 1. -/
theorem rootCeil_meets {μ : ℕ → ℤ} {pRoot pPow e t : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (he : e ≠ 0) (ht : 1 ≤ t)
    (hword : ((t * rootCeil e t + e + 1 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pRoot d [e, t] μ (tRootCeil e t) fun r μ' => r = (rootCeil e t : ℕ) ∧ μ' = μ := by
  refine .of_body hR ?_
  have key : ∀ g, g ^ e < t ↔ g < rootCeil e t := fun g => by
    rw [← not_le, ← not_le, rootCeil_le_iff he ht]
  have hpos : 1 ≤ rootCeil e t := Nat.succ_le_succ (Nat.zero_le _)
  unfold tRootCeil
  generalize rootCeil e t = G at key hpos hword
  obtain ⟨y, rfl⟩ : ∃ y, G = y + 1 := ⟨G - 1, by omega⟩
  have hyt : y + 1 ≤ t * (y + 1) := Nat.le_mul_of_pos_left _ ht
  -- The test of a candidate g ≤ y + 1.
  have test : ∀ g, 1 ≤ g → g ≤ y + 1 → Meets lim P pPow (d + 1) [g, e, t] μ (16 * e + 14)
      fun r μ' => r = (if g < y + 1 then 1 else 0) ∧ μ' = μ := fun g hg hgy => by
    have hle : t * g + e + 1 ≤ t * (y + 1) + e + 1 := by
      have := Nat.mul_le_mul_left t hgy
      omega
    simpa only [key] using powLt_meets hP hg ((Int.ofNat_le.2 hle).trans hword)
  -- cand := 1; more := powLt(cand, e, t)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen ((test 1 le_rfl hpos) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (test 1 le_rfl hpos) ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ' ⟨rfl, hμ⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hμ]
  -- while more = 1.  Before round i, cand = i + 1.
  refine Ends.next _ (Ends.whileConst
    (fun i σ => σ = ⟨frame [e, t, (i + 1 : ℕ), if i + 1 < y + 1 then 1 else 0], μ⟩) y (16 * e + 23)
    (by simp) ?round ?done le_rfl) (by simp; ring_nf; omega)
  case round =>
    rintro i _ hi rfl
    -- cand := cand + 1; more := powLt(cand, e, t)
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [hi], Ends.setToThen (i + 1 + 1 : ℕ)
      (Ends.callTo (test (i + 1 + 1) (by omega) (by omega)) ?_)⟩
    rintro _ μ' ⟨rfl, hμ⟩
    simp [hμ]
  case done =>
    rintro _ rfl
    -- return cand
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp, Ends.setTo (y + 1 : ℕ) (by simp) (hT := by simp; ring_nf; omega)⟩

/-- Rounding a root down is rounding the root of the next number up, minus one. -/
theorem rootCeil_succ {e : ℕ} (he : e ≠ 0) (t : ℕ) : rootCeil e (t + 1) = rootFloor e t + 1 := by
  have h : ∀ g, rootCeil e (t + 1) ≤ g ↔ rootFloor e t + 1 ≤ g := fun g => by
    rw [rootCeil_le_iff he (by omega), Nat.succ_le_iff, Nat.succ_le_iff, ← not_le, ← not_le,
      le_rootFloor_iff he]
  exact le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)

/-! ## The four parameters of the proof of Theorem 19 -/










/-- **d26** returns ⌊n^{1/18}⌋. -/
theorem d26_spec {μ : ℕ → ℤ} {pRoot pPow n : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody)
    (hword : (((n + 1) * (paramD₂₆Nat n + 1) + 19 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (d26Body pRoot) ⟨frame [n], μ⟩ (tD26 n) fun σ' =>
      σ'.loc 0 = (paramD₂₆Nat n : ℕ) ∧ σ'.mem = μ := by
  have hroot : rootCeil 18 (n + 1) = paramD₂₆Nat n + 1 := rootCeil_succ (by norm_num) n
  have hn : n + 1 ≤ (n + 1) * (paramD₂₆Nat n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hD : paramD₂₆Nat n + 1 ≤ (n + 1) * (paramD₂₆Nat n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  -- root := rootCeil(18, n + 1)
  refine Ends.callToThen (rootCeil_meets (e := 18) (t := n + 1) hR hP (by norm_num) (by omega)
    (by rw [hroot]; exact hword) (by omega)) ?_ (hT := by simp [tD26, tRootCeil, hroot]; omega)
  rintro _ μ' ⟨rfl, hμ⟩
  -- return root - 1
  rw [hroot, hμ]
  exact Ends.setTo (paramD₂₆Nat n) (by simp) (hT := by simp [tD26, tRootCeil, hroot]; omega)



































































































/-- **g26** returns ⌈D^{0.0315}⌉, for D ≥ 1. -/
theorem g26_spec {μ : ℕ → ℤ} {pRoot pPow D : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (hD : 1 ≤ D)
    (hword : ((D ^ 63 * paramG₂₆Nat D + 2001 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (g26Body pRoot) ⟨frame [D], μ⟩ (tG26 D) fun σ' =>
      σ'.loc 0 = (paramG₂₆Nat D : ℕ) ∧ σ'.mem = μ := by
  have hpos : 1 ≤ paramG₂₆Nat D := Nat.succ_le_succ (Nat.zero_le _)
  have hfits : ((D ^ 63 + 2001 : ℕ) : ℤ) ≤ lim.word := le_trans
    (by exact_mod_cast Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hpos) 2001) hword
  rw [Nat.cast_add] at hfits
  have hpow0 : (0 : ℤ) ≤ ((D ^ 63 : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold tG26
  -- cnt := 0; prod := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (1 : ℕ)
            -- while cnt < 63: prod := prod * D; cnt := cnt + 1.  Before round i, prod = D^i.
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while cnt < 63: prod := prod * D; cnt := cnt + 1.  Before round i, prod = D^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [D, i, (D ^ i : ℕ)], μ⟩) 63 (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hle : ((D ^ (i + 1) : ℕ) : ℤ) ≤ ((D ^ 63 : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hD hi
    have hmul : ((D ^ i : ℕ) : ℤ) * D = ((D ^ (i + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmul0 : (0 : ℤ) ≤ ((D ^ (i + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((D ^ (i + 1) : ℕ) : ℤ) = q' at hle hmul hmul0
    generalize ((D ^ i : ℕ) : ℤ) = q at hmul
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, hmul] <;> omega)),
      by simp [update_frame_setLocal, hmul]⟩
  case done =>
    rintro _ rfl
    -- return rootCeil(2000, prod)
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      Ends.callTo (rootCeil_meets (e := 2000) (t := D ^ 63) hR hP (by norm_num)
        (Nat.one_le_pow _ _ hD) hword (by omega)) (fun r μ' h => by simpa [paramG₂₆Nat] using h)
        (hT := by simp [tRootCeil, paramG₂₆Nat]; omega)⟩

/-! ## ⌊n²/√D⌋ and quotients rounded up -/












































































































end Light.Sec3

end
end

section


/-!
# Theorem 17: the time of each routine, up to a constant

The running time of the reduction of Theorem 17 is a sum of the time functions of its routines.  The
theorem bounds the additional time by "O(ν n³ log n/g + n^{ω+o(1)} D^{3/2} + n² D g)", where ν is
the exponent in `|w(e)| ≤ n^ν`; it is `κ` below.  The form for programs, `Claim.Theorem_17`, has,
here, Strassen's exponent `log₂ 7` in the second term.  This file bounds each
routine by a monomial in `n`, `√D` and `κ log n`, uniformly in `n`, `D`, `g`, `U` and `κ` under the
hypotheses of the theorem, and says which monomials are within which of the three terms.  No
constant is computed.

* `Steps t B` says that the number `t` of steps is `O(B)`, uniformly in the parameters.  Such bounds
  can be added and multiplied, and they absorb constant factors.
* Every time function is a polynomial in a few quantities, and each of these is at most a monomial
  `mon a b c = n^a (√D)^b (κ log n)^c`: `⌊√D⌋`, `g` and the size `⌈s/g⌉` of a piece are at most
  `√D`; `2^⌈log₂ n⌉ ≤ 2n`; the number of binary digits of `U ≤ n^κ` is `O(κ log n)` (section "The
  basic quantities").  So a routine takes `O(mon a b c)` steps (`StepsMon t a b c`), and the
  exponents are read off its time function, in the calculus `Scale.SoftO` on the scale `costScale`.
* All three bases are at least 1.  So a monomial is within the first term if its exponents are at
  most `(2, 1, 1)`, within the second if they are at most `(2, 3, 0)`, within the third if they are
  at most `(2, 2, 0)` (`Scale.SoftO.withinScans`, `Scale.SoftO.withinPrime`,
  `Scale.SoftO.withinBuild`).
* The choice of the prime runs through at most `√D` primes (`steps_chooseTime`).  The product of the
  two matrices is within the second term, as in the paper: Strassen's recursion makes
  `7^⌈log₂ n⌉ = O(n^{log₂ 7})` products of polynomials of degree below `p ≤ √D`
  (`steps_sqrt_mul_strSteps`).  The residues of the weights, computed bit by bit for each prime,
  take `O(√D n² κ log n)` steps, which is within the first term.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The hypotheses -/































namespace CostParams.Hyp

variable {θ : CostParams} (h : θ.Hyp)
include h

/-- `D ≥ 1`, as a natural number. -/
theorem one_le_D_nat : 1 ≤ θ.D := (by norm_num : 1 ≤ 16).trans h.hD16













/-- `g > 0`. -/
theorem g_pos : (0 : ℝ) < θ.g := zero_lt_one.trans_le h.one_le_g




/-- `√D > 0`. -/
theorem sqrt_pos : 0 < Real.sqrt θ.D := zero_lt_one.trans_le h.one_le_sqrt









/-- `√D g ≤ D ≤ n`. -/
theorem sqrt_mul_g_le : Real.sqrt θ.D * θ.g ≤ θ.n :=
  calc Real.sqrt θ.D * θ.g ≤ Real.sqrt θ.D * Real.sqrt θ.D := by
        gcongr
        exact h.hgD
    _ = θ.D := Real.mul_self_sqrt θ.D.cast_nonneg
    _ ≤ θ.n := Nat.cast_le.2 h.hDn





end CostParams.Hyp

/-! ## Numbers of steps up to a constant -/






namespace Steps

variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}





/-- A larger bound. -/
theorem mono_right (h : Steps t B₁) (hle : ∀ θ, θ.Hyp → B₁ θ ≤ B₂ θ) : Steps t B₂ :=
  Dominated.mono_right h hle

/-- `O(B) + O(B) = O(B)`. -/
protected theorem add (h₁ : Steps t₁ B) (h₂ : Steps t₂ B) : Steps (fun θ => t₁ θ + t₂ θ) B := by
  simpa only [Steps, Nat.cast_add] using Dominated.add h₁ h₂

/-- `O(B₁) · O(B₂) = O(B₁ B₂)`. -/
protected theorem mul (h₁ : Steps t₁ B₁) (h₂ : Steps t₂ B₂) :
    Steps (fun θ => t₁ θ * t₂ θ) fun θ => B₁ θ * B₂ θ := by
  simpa only [Steps, Nat.cast_mul] using
    Dominated.mul h₁ h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _

/-- A constant factor is absorbed. -/
theorem const_mul {c : ℕ} (h : Steps t B) : Steps (fun θ => c * t θ) B := by
  simpa only [Steps, Nat.cast_mul] using Dominated.const_mul h c.cast_nonneg

/-- A constant number of steps is `O(B)` if `B ≥ 1`. -/
protected theorem const {c : ℕ} (hB : ∀ θ, θ.Hyp → 1 ≤ B θ) : Steps (fun _ => c) B :=
  Dominated.const _ hB

end Steps

/-! ## Monomials -/












theorem mon_eq (a b c : ℕ) (θ : CostParams) :
    mon a b c θ = (θ.n : ℝ) ^ a * Real.sqrt θ.D ^ b * (θ.κ * Real.log θ.n) ^ c := by
  simp [Scale.mon, costScale, Scale.ofBases, Fin.prod_univ_three]




/-- A bound by a monomial, as a bound up to a constant. -/
theorem steps_of_softO {t : CostParams → ℕ} {e : Fin 3 → ℕ} (h : costScale.SoftO t e) :
    Steps t (costScale.mon e) :=
  h.dominated fun _ _ => rfl

/-! ## The basic quantities -/

/-- The number of vertices per part. -/
theorem steps_n : StepsMon (fun θ => θ.n) 1 0 0 :=
  (Scale.SoftO.of_le_base 0 fun _ _ => le_rfl).mono (by decide)

/-- `s = ⌊√D⌋ ≤ √D`. -/
theorem steps_sqrt : StepsMon (fun θ => Nat.sqrt θ.D) 0 1 0 :=
  (Scale.SoftO.of_le_base 1 fun _ _ => Real.nat_sqrt_le_real_sqrt).mono (by decide)

/-- `D = (√D)²`. -/
theorem steps_D : StepsMon (fun θ => θ.D) 0 2 0 :=
  .of_dominated <| .of_le fun θ _ => by
    simp only [mon_eq, pow_zero, mul_one, one_mul, Real.sq_sqrt θ.D.cast_nonneg, le_refl]


































/-- A piece has `⌈s/g⌉ ≤ s` vertices. -/
private theorem steps_pieceSizeNat : StepsMon (fun θ => pieceSizeNat θ.D θ.g) 0 1 0 :=
  steps_sqrt.of_le fun _ hθ => (Nat.ceilDiv_le_iff hθ.hg).2 (Nat.le_mul_of_pos_right _ hθ.hg)

/-- `⌊n²/√D⌋ ≤ n²/√D`. -/
theorem cast_queryCapNat_le {θ : CostParams} (hθ : θ.Hyp) :
    (queryCapNat θ.n θ.D : ℝ) ≤ (θ.n : ℝ) ^ 2 / Real.sqrt θ.D := by
  rw [queryCapNat_eq θ.n hθ.one_le_D_nat]
  exact Nat.floor_le (by positivity)






/-! ## The routines -/































/-- Writing the matrix `X` of an instance takes `O(nD)` steps. -/
theorem steps_tWriteX : StepsMon (fun θ => tWriteX θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWriteX
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_D
              | apply steps_pieceSizeNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply steps_D
                            | apply steps_pieceSizeNat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply steps_D
                      | apply steps_pieceSizeNat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_D
              | apply steps_pieceSizeNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- Writing the matrix `Y` of an instance takes `O(nD)` steps. -/
theorem steps_tWriteY : StepsMon (fun θ => tWriteY θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWriteY
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_D
              | apply steps_pieceSizeNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply steps_D
                            | apply steps_pieceSizeNat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply steps_D
                      | apply steps_pieceSizeNat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply steps_D
              | apply steps_pieceSizeNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))






































/-! ## The three terms of the bound dominate the monomials -/

/-- `D^{3/2} = (√D)³`. -/
private theorem rpow_three_half (D : ℕ) : (D : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt D ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul D.cast_nonneg]
  norm_num

/-- `n² √D κ log n ≤ κ n³ log n/g`, because `√D g ≤ n`. -/
private theorem mon_le_termScans {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 1 1 θ ≤ termScans θ.n θ.g θ.κ := by
  have hκ : 0 ≤ θ.κ := zero_le_one.trans hθ.hκ
  rw [termScans, le_div_iff₀ hθ.g_pos]
  calc mon 2 1 1 θ * θ.g
      = (θ.n : ℝ) ^ 2 * θ.κ * Real.log θ.n * (Real.sqrt θ.D * θ.g) := by
        rw [mon_eq]
        ring
    _ ≤ (θ.n : ℝ) ^ 2 * θ.κ * Real.log θ.n * θ.n := by
        gcongr _ * ?_
        exact hθ.sqrt_mul_g_le
    _ = θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n := by ring

/-- `n² (√D)³ ≤ n^{log₂ 7} D^{3/2}`. -/
private theorem mon_le_termPrime {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 3 0 θ ≤ termPrime strassen θ.n θ.D := by
  have htwo : (2 : ℝ) ≤ Real.logb 2 7 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    norm_num
  rw [termPrime, strassen, rpow_three_half, mon_eq, pow_zero, mul_one, ← Real.rpow_ofNat]
  gcongr
  exact hθ.one_le_n

/-- `n² (√D)² ≤ n² D g`. -/
private theorem mon_le_termBuild {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 2 0 θ ≤ termBuild θ.n θ.D θ.g := by
  rw [termBuild, mon_eq, pow_zero, mul_one, Real.sq_sqrt θ.D.cast_nonneg]
  exact le_mul_of_one_le_right (by positivity) hθ.one_le_g





/-- The first term is not negative. -/
private theorem termScans_nonneg {θ : CostParams} (hθ : θ.Hyp) : 0 ≤ termScans θ.n θ.g θ.κ := by
  have hκ : 0 ≤ θ.κ := zero_le_one.trans hθ.hκ
  unfold termScans
  positivity

/-- The second term is not negative. -/
private theorem termPrime_nonneg (θ : CostParams) : 0 ≤ termPrime strassen θ.n θ.D := by
  unfold termPrime strassen
  positivity

/-- The third term is not negative. -/
private theorem termBuild_nonneg (θ : CostParams) : 0 ≤ termBuild θ.n θ.D θ.g := by
  unfold termBuild
  positivity

/-- The sum is not negative. -/
theorem budget_nonneg {θ : CostParams} (hθ : θ.Hyp) : 0 ≤ budget θ :=
  add_nonneg (add_nonneg (termScans_nonneg hθ) (termPrime_nonneg θ)) (termBuild_nonneg θ)

/-- The first term is at most the sum. -/
theorem termScans_le_budget (θ : CostParams) : termScans θ.n θ.g θ.κ ≤ budget θ := by
  unfold budget
  linarith [termPrime_nonneg θ, termBuild_nonneg θ]

/-- The second term is at most the sum. -/
private theorem termPrime_le_budget {θ : CostParams} (hθ : θ.Hyp) :
    termPrime strassen θ.n θ.D ≤ budget θ := by
  unfold budget
  linarith [termScans_nonneg hθ, termBuild_nonneg θ]

/-- The third term is at most the sum. -/
theorem termBuild_le_budget {θ : CostParams} (hθ : θ.Hyp) :
    termBuild θ.n θ.D θ.g ≤ budget θ := by
  unfold budget
  linarith [termScans_nonneg hθ, termPrime_nonneg θ]

section within

variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}

/-- Within the first term, `κ n³ log n/g`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinScans (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 1, 1] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun θ hθ =>
    (mon_le_termScans hθ).trans (termScans_le_budget θ)

/-- Within the second term, `n^{log₂ 7} D^{3/2}`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinPrime (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 3, 0] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun _ hθ =>
    (mon_le_termPrime hθ).trans (termPrime_le_budget hθ)

/-- Within the third term, `n² D g`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinBuild (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 2, 0] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun _ hθ =>
    (mon_le_termBuild hθ).trans (termBuild_le_budget hθ)

end within

namespace Steps

variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}






end Steps

/-! ## The choice of the prime -/







































































end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the loop over the instances

Proof of Theorem 17.  After the prime has been chosen and the query pairs have been sorted into
classes and cut into chunks, the host runs through all instances: instance number t belongs to the
piece number t / chunkCount of the third part of the vertices and to the chunk number t % chunkCount
of the table of chunks.  For each instance it writes the two biadjacency matrices, calls the solver
of Lop-AE-SparseTri on the chunk (a segment of the sorted arrays of query pairs, so nothing is
copied), and scans the piece for every accepted query pair, as long as no zero triangle has been
found.

The solver is arbitrary.  The facts about the data that the loop relies on are collected in the
structure `HostOk`.

* What the four calls assume is proved without any program: `HostSetting.writeX`,
  `HostSetting.writeY`, `HostSetting.solver`, `HostSetting.weights`, `HostSetting.answers`.
* The program has one lemma for each part of a round: `hostParams_spec` (the parameters of the
  instance), `hostCalls_spec` (the four calls) and `hostNext_spec` (the counters).
  `hostRound_spec` puts them together, and `hostLoop_spec` is the loop: hostLoop returns 1 if a scan
  has found a zero triangle (`X.found X.m`) and 0 if not, changes no cell below x, and takes at most
  `tHostLoop` steps, the sum over the instances of the times of the four calls.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace HostLocal




























































end HostLocal

open HostLocal
















































/-! ## What the loop relies on -/



















































































/-! ## What the calls assume -/











/-- Entries 0 and 1 have absolute value at most 1. -/
private theorem absLe_one_of_zero_or_one {L : List ℤ} (h : ∀ e ∈ L, e = 0 ∨ e = 1) :
    AbsLe L ((1 : ℕ) : ℤ) := by
  intro e he
  rcases h e he with rfl | rfl <;> simp

namespace HostSetting

variable {X : HostData} {U : ℕ} {A : HostAddr} {need : List ℕ → Need} {μ μ' μ'' : ℕ → ℤ} {t : ℕ}

/-- The order of the regions of the memory, the limits, and the sizes of instance t. -/
theorem places (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    A.ab + X.n * X.n ≤ A.x ∧ A.bc + X.n * X.n ≤ A.x ∧ A.ac + X.n * X.n ≤ A.x ∧
      A.rac + X.n * X.n ≤ A.x ∧ A.rbc + X.n * X.n ≤ A.x ∧ A.qi + X.n * X.n ≤ A.x ∧
      A.qj + X.n * X.n ≤ A.x ∧ A.cr + X.chunkCount ≤ A.x ∧ A.cl + X.chunkCount ≤ A.x ∧
      A.cw + X.chunkCount ≤ A.x ∧ A.x + X.n * X.D ≤ A.y ∧ A.y + X.D * X.n ≤ A.out ∧
      A.out + X.w t ≤ A.fr ∧
      (lim.space : ℤ) ≤ lim.word ∧ A.fr < lim.space ∧ 2 * X.p < lim.space ∧
      (X.m : ℤ) ≤ lim.word ∧ ((X.n + X.q : ℕ) : ℤ) ≤ lim.word ∧ d + 2 ≤ lim.depth ∧
      X.c0 t + X.len t ≤ X.n ∧ X.lo t + X.w t ≤ X.n * X.n ∧ t % X.chunkCount < X.chunkCount :=
  ⟨S.lay.bAB, S.lay.bBC, S.lay.bAC, S.lay.bRAC, S.lay.bRBC, S.lay.bQI, S.lay.bQJ, S.lay.bCR,
    S.lay.bCL, S.lay.bCW, S.lay.xy, S.lay.yo, S.lay.ofr t ht, S.fits.space, S.fits.fr, S.fits.prime,
    S.fits.count, S.fits.step, S.fits.depth, S.ok.valid.piece_le ht, S.ok.valid.lo_add_le ht,
    HostData.mod_chunkCount_lt ht⟩

/-- A later memory that agrees with μ' below x. -/
theorem next (S : HostSetting lim d X U A need μ μ') (h : ∀ a < A.x, μ'' a = μ' a) :
    HostSetting lim d X U A need μ μ'' :=
  { S with kept := fun a ha => (h a ha).trans (S.kept a ha) }

/-- There are `n²` residues of the weights `w(a,c)`. -/
theorem length_RAC (S : HostSetting lim d X U A need μ μ') : X.RAC.length = X.n * X.n := by
  simp [HostData.RAC, residList, S.ok.valid.lenAC]

/-- There are `n²` residues of the weights `w(b,c)`. -/
theorem length_RBC (S : HostSetting lim d X U A need μ μ') : X.RBC.length = X.n * X.n := by
  simp [HostData.RBC, residList, S.ok.valid.lenBC]

/-- What the loop reads stands in μ' as it stood in μ. -/
theorem mem_prime (S : HostSetting lim d X U A need μ μ') : HostMem X A μ' := by
  ((obtain ⟨⟩ := id S); (obtain ⟨⟩ := id S.lay); (obtain ⟨⟩ := id S.ok.valid))
  have lenRAC := S.length_RAC
  have lenRBC := S.length_RBC
  have lenQI := S.ok.valid.length_QI
  have lenQJ := S.ok.valid.length_QJ
  have lenCT : X.CT.length = X.chunkCount := rfl
  have h := S.mem
  exact
    { segAB := h.segAB.keep
      segBC := h.segBC.keep
      segAC := h.segAC.keep
      segRAC := h.segRAC.keep
      segRBC := h.segRBC.keep
      segQI := h.segQI.keep
      segQJ := h.segQJ.keep
      segCR := h.segCR.keep
      segCL := h.segCL.keep
      segCW := h.segCW.keep }

/-- Reading an entry of a component of the table of chunks. -/
theorem read_tab {a : ℕ} (f : Chunk → ℕ) (h : SegN μ a (X.CT.map f)) {i : ℕ}
    (hi : i < X.chunkCount) : μ (a + i) = (f (X.CT.getD i ⟨0, 0, 0⟩) : ℤ) := by
  have hi' : i < X.CT.length := hi
  rw [h i (by simpa using hi'), List.getD_eq_getElem _ _ hi']
  simp

/-- The three parameters of the chunk of instance t, in the memory. -/
theorem read_chunk (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    μ' (A.cr + t % X.chunkCount) = X.rho t ∧ μ' (A.cl + t % X.chunkCount) = X.lo t ∧
      μ' (A.cw + t % X.chunkCount) = X.w t :=
  ⟨read_tab (fun c => c.residue) S.mem_prime.segCR (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.start) S.mem_prime.segCL (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.len) S.mem_prime.segCW (HostData.mod_chunkCount_lt ht)⟩

/-- What writeX and writeY assume, for a matrix of size cells at dst and the residues of a list of
weights at r. -/
private theorem write (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) {dst size r : ℕ}
    {weights : List ℤ} (seg : SegN μ' r (residList X.p weights))
    (length : (residList X.p weights).length = X.n * X.n) (hsize : size = X.D * X.n)
    (hdst : dst + size < lim.space) (hr : r + X.n * X.n ≤ dst) :
    WritePre lim μ' dst size r X.n X.D X.p (X.c0 t) (X.len t) (residList X.p weights) where
  hw := S.fits.space
  seg := seg
  length := length
  lt := fun x hx => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
    exact resid_lt S.ok.valid.p_ne z
  fits := S.ok.valid.len_mul_le t
  piece := S.ok.valid.piece_le ht
  size := hsize
  spaceM := hdst
  spaceR := by omega
  spaceP := S.fits.prime
  apart := Or.inr hr

/-- The precondition of writeX holds. -/
theorem writeX (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.x (X.n * X.D) A.rac X.n X.D X.p (X.c0 t) (X.len t) X.RAC := by
  have hplaces := S.places ht
  exact S.write ht S.mem_prime.segRAC S.length_RAC (Nat.mul_comm _ _) (by omega) (by omega)

/-- The precondition of writeY holds. -/
theorem writeY (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.y (X.D * X.n) A.rbc X.n X.D X.p (X.c0 t) (X.len t) X.RBC := by
  have hplaces := S.places ht
  exact S.write ht S.mem_prime.segRBC S.length_RBC rfl (by omega) (by omega)






/-- The precondition of the solver holds, once the two matrices are written. -/
theorem solver (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) : lopDetectTask.Pre (inst X A t) μ' A.fr := by
  have hplaces := S.places ht
  have hv := S.ok.valid
  refine ⟨?_, ⟨X.matX_zero_or_one t, X.matY_zero_or_one t⟩, rfl⟩
  exact
    { N_pos := hv.n_pos
      D_pos := le_trans (Nat.mul_pos hv.q_pos hv.p_pos) hv.qp_le
      U_pos := le_rfl
      lenX := X.length_matX t
      lenY := X.length_matY t
      lenWI := hv.length_WI ht
      lenWJ := hv.length_WJ ht
      segX := hX
      segY := hY
      segWI := SegN.drop_take S.mem_prime.segQI _ _
      segWJ := SegN.drop_take S.mem_prime.segQJ _ _
      leX := absLe_one_of_zero_or_one (X.matX_zero_or_one t)
      leY := absLe_one_of_zero_or_one (X.matY_zero_or_one t)
      ltWI := fun _ => HostData.lt_of_mem_WI
      ltWJ := fun _ => HostData.lt_of_mem_WJ
      nodup := X.nodup_zip t
      belowX := by simp only [inst]; omega
      belowY := by simp only [inst]; omega
      belowWI := by simp only [inst]; omega
      belowWJ := by simp only [inst]; omega
      belowOut := by simp only [inst]; omega
      apartX := by simp only [inst]; omega
      apartY := by simp only [inst]; omega
      apartWI := by simp only [inst]; omega
      apartWJ := by simp only [inst]; omega }

/-- The weights are where the scans read them. -/
theorem weights (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Weights lim μ' A.ab A.bc A.ac X.n U X.AB X.BC X.AC := by
  have hplaces := S.places ht
  have hm := S.mem_prime
  have hv := S.ok.valid
  exact
    { hw := S.fits.space
      hU := by exact_mod_cast S.fits.weights
      arrAB := { len := hv.lenAB, seg := hm.segAB, bound := S.ok.leAB }
      arrBC := { len := hv.lenBC, seg := hm.segBC, bound := S.ok.leBC }
      arrAC := { len := hv.lenAC, seg := hm.segAC, bound := S.ok.leAC } }

/-- The answers of the solver and the query pairs of the chunk are where the scans read them. -/
theorem answers (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (hans : Seg μ' A.out (X.ans t)) :
    Answers lim μ' A.out (A.qi + X.lo t) (A.qj + X.lo t) (X.w t) X.n (X.ans t) (X.WI t)
      (X.WJ t) := by
  have hplaces := S.places ht
  have hv := S.ok.valid
  exact
    { arrOUT :=
        { len := by simp [HostData.ans, thinOut, hv.length_WI ht, hv.length_WJ ht], seg := hans }
      arrQA :=
        { len := hv.length_WI ht, seg := SegN.drop_take S.mem_prime.segQI _ _
          lt := fun _ => HostData.lt_of_mem_WI }
      arrQB :=
        { len := hv.length_WJ ht, seg := SegN.drop_take S.mem_prime.segQJ _ _
          lt := fun _ => HostData.lt_of_mem_WJ }
      w_lt := by omega }

end HostSetting

/-! ## The parts of a round -/

variable {P₀ R : Program} {pS pWriteX pWriteY pScanPairs pScan : ℕ} {Tn : List ℕ → ℕ}
  {need : List ℕ → Need} {X : HostData} {U : ℕ} {A : HostAddr} {μ μ' : ℕ → ℤ} {t : ℕ}








/-- **The parameters of instance t.** -/
theorem hostParams_spec {P : Program} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostParams (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 27
      (· = hostState X A t (t % X.chunkCount) (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res
        μ') := by
  have hplaces := S.places ht
  obtain ⟨hrho, hlo, hw⟩ := S.read_chunk ht
  have hlen : X.len t = min X.q (X.n - X.c0 t) := rfl
  generalize t % X.chunkCount = ch at *
  -- rho := mem[cr + ch]; lo := mem[cl + ch]; w := mem[cw + ch]
  have htail : ∀ len' : ℤ, len' = X.len t → Ends lim P d
      ((Light.Stmt.seq
         (.set Residue (M ((Light.Expr.op Light.Op.add) (v TabR) (v ChunkNo))))
         (Light.Stmt.seq
           (.set Start (M ((Light.Expr.op Light.Op.add) (v TabL) (v ChunkNo))))
           (.set NumPairs (M ((Light.Expr.op Light.Op.add) (v TabW) (v ChunkNo)))))))
      (hostState X A t ch (X.c0 t) fnd len' rho lo w res μ') 15
      (· = hostState X A t ch (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res μ') := by
    rintro _ rfl
    refine Ends.setToThen (X.rho t : ℤ) ?_ (by (((try have := Light.Std.space_le (by assumption)));
                                                   ((try have := Light.Std.const_le (by assumption)));
                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, hrho] <;> omega)))
    refine Ends.setToThen (X.lo t : ℤ) ?_ (by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, hlo] <;> omega)))
    exact Ends.setTo (X.w t : ℤ) rfl (by (((try have := Light.Std.space_le (by assumption)));
                                             ((try have := Light.Std.const_le (by assumption)));
                                             (simp [Light.Limits.Addr, abs_le, -abs_mul, hw] <;> omega)))
  unfold hostParams
  -- len := q
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen X.q ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- if n - c0 < q then len := n - c0
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : (X.n : ℤ) - X.c0 t < X.q := by simpa using hc
    exact Ends.setToThen (X.len t : ℤ) ((htail _ rfl).mono (by first
                                                                 |
                                                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                     (first
                                                                       | omega
                                                                       | ((ring_nf); (omega))))
                                                                 | omega
                                                                 |
                                                                   (simp [] <;>
                                                                       first
                                                                       | omega
                                                                       | ((ring_nf); (omega)))) fun _ h => h)
  · replace hc : ¬ (X.n : ℤ) - X.c0 t < X.q := by simpa using hc
    refine Ends.next 0 (Ends.skip ?_)
    exact (htail _ (by omega)).mono (by first
                                        |
                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                            (first
                                              | omega
                                              | ((ring_nf); (omega))))
                                        | omega
                                        |
                                          (simp [] <;>
                                              first
                                              | omega
                                              | ((ring_nf); (omega)))) fun _ h => h






/-- The call of writeX for instance t. -/
theorem HostCtx.writeX_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteX (d + 1)
      [(A.x : ℤ), A.rac, X.n, X.D, X.p, X.c0 t, X.len t, X.rho t] μ' (tWriteX X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.x (X.matX t) ∧ SameOutside μ' μ₁ A.x (X.n * X.D) :=
  Meets.of_body C.writeX (writeX_spec (S.writeX ht) (S.ok.valid.rho_lt ht))

/-- The call of writeY for instance t. -/
theorem HostCtx.writeY_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteY (d + 1) [(A.y : ℤ), A.rbc, X.n, X.D, X.p, X.c0 t, X.len t] μ'
      (tWriteY X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.y (X.matY t) ∧ SameOutside μ' μ₁ A.y (X.D * X.n) :=
  Meets.of_body C.writeY (writeY_spec (S.writeY ht))

/-- The call of the solver for instance t, once the two matrices are written. -/
theorem HostCtx.solver_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) :
    Meets lim (P₀ ++ R) pS (d + 1)
      [(X.n : ℤ), X.D, X.w t, (1 : ℕ), A.x, A.y, (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), A.out,
        A.fr] μ' (Tn [X.n, X.D, X.w t])
      fun _ μ₁ => Seg μ₁ A.out (X.ans t) ∧ KeptBut μ' μ₁ A.fr A.out (X.w t) :=
  C.sol.meets R (HostSetting.inst X A t) (S.solver ht hX hY) (S.fits.solver t ht)





































/-- **The counters**: from instance t to instance t + 1. -/
theorem hostNext_spec {P : Program} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostNext (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 18
      (· = hostState X A (t + 1) ((t + 1) % X.chunkCount) (X.c0 (t + 1)) fnd len rho lo w res
        μ') := by
  have hplaces := S.places ht
  have hlast := Nat.succ_div_mod_of_eq (n := X.chunkCount) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (n := X.chunkCount) (i := t) (by omega)
  have hc0 : X.c0 t = t / X.chunkCount * X.q := rfl
  have hc0' : X.c0 (t + 1) = (t + 1) / X.chunkCount * X.q := rfl
  generalize t % X.chunkCount = ch at *
  generalize (t + 1) % X.chunkCount = ch' at *
  -- t := t + 1
  have htail : Ends lim P d (.set Inst (((Light.Expr.op Light.Op.add) (v Inst) (k 1))))
      (hostState X A t ch' (X.c0 (t + 1)) fnd len rho lo w res μ') 4
      (· = hostState X A (t + 1) ch' (X.c0 (t + 1)) fnd len rho lo w res μ') :=
    Ends.setTo (t + 1 : ℕ) rfl
  unfold hostNext
  -- ch := ch + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (ch + 1 : ℕ)
            -- if ch = chunkCount
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- if ch = chunkCount
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : ch + 1 = X.chunkCount := by
      have : ((ch + 1 : ℕ) : ℤ) = X.chunkCount := by simpa using hc
      exact_mod_cast this
    obtain ⟨hdiv, rfl⟩ := hlast hc
    have hstep : X.c0 (t + 1) = X.c0 t + X.q := by rw [hc0', hc0, hdiv, Nat.succ_mul]
    -- ch := 0; c0 := c0 + q
    have hwrap : Ends lim P d ((Light.Stmt.seq (.set ChunkNo (k 0))
                                 (.set PieceStart ((Light.Expr.op Light.Op.add) (v PieceStart) (v PieceLen)))))
        (hostState X A t (ch + 1) (X.c0 t) fnd len rho lo w res μ') 6
        (· = hostState X A t 0 (X.c0 (t + 1)) fnd len rho lo w res μ') :=
      Ends.setToThen ((0 : ℕ) : ℤ)
        (Ends.setTo (X.c0 (t + 1) : ℕ) rfl (by (((try have := Light.Std.space_le (by assumption)));
                                                   ((try have := Light.Std.const_le (by assumption)));
                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, hstep] <;> omega))))
    refine Ends.next _ (hwrap.mono le_rfl ?_)
    rintro _ rfl
    exact htail.mono (by first
                         |
                           ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                 List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                             (first
                               | omega
                               | ((ring_nf); (omega))))
                         | omega
                         |
                           (simp [] <;>
                               first
                               | omega
                               | ((ring_nf); (omega)))) fun _ h => h
  · replace hc : ch + 1 ≠ X.chunkCount := fun h => hc (by simp; exact_mod_cast h)
    obtain ⟨hdiv, rfl⟩ := hinner hc
    have hstep : X.c0 (t + 1) = X.c0 t := by rw [hc0', hc0, hdiv]
    -- skip
    refine Ends.next 0 (Ends.skip ?_)
    rw [← hstep]
    exact htail.mono (by first
                         |
                           ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                 List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                             (first
                               | omega
                               | ((ring_nf); (omega))))
                         | omega
                         |
                           (simp [] <;>
                               first
                               | omega
                               | ((ring_nf); (omega)))) fun _ h => h

/-! ## The loop -/



























































end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the top procedure

The host procedure et17(n, U, ab, bc, ac, fr) decides Exact Triangle with the help of an arbitrary
solver of Lop-AE-SparseTri (proof of Theorem 17).  It computes the parameters `D` and `g` by two
procedures that are parameters of the construction, and `s = ⌊√D⌋`.  For small `n`
(`D < 16`, `n < D`, `g < 1` or `s < g`) it runs the brute force.  Otherwise it chooses the prime,
computes the largest number of query pairs, the number of vertices of a piece and the number of
pieces, lays out its arrays from the free pointer on, computes the residues of the weights, sorts
the pairs `(a, b)` into classes, cuts the classes into chunks, and runs the loop over the instances.

This file holds the program (`et17Body`), its time and its need (`hostTime`, `hostNeed`), what it
assumes about the program around it (`Et17Ctx`), and the data, the addresses and the local variables
of a run.

**The way through the files on the host**, each named by its main result.

1. The instances as data, with no program in sight: what the host writes, what the solver answers
   and which scans succeed (`HostData`); a zero triangle is found if and only if there is one
   (`HostData.found_m`); a failed scan belongs to a false positive of its own
   (`HostData.sum_fails_le`); there are at most 4ng instances (`HostData.m_le`).
2. The loop over the instances (`hostLoop_spec`).
3. The text of the top procedure (this file), in three parts and the small case.
4. The parts: the parameters and the small case (`et17Params_spec`, `et17Small_spec`); the prime,
   the sizes and the addresses (`et17Sizes_spec`, `et17Addr_spec`); the arrays and the call of the
   loop (`et17Tables_spec`).
5. What the parts need: the limits cover what the called procedures ask for (`choosePre_of_ok`,
   `hostLim_of_ok`), and the time of a run is within the worst case (`hostRunTime_le`).
6. The parts together: et17 decides Exact Triangle (`et17_spec`).
7. The list of the procedures with their numbers; with a solver it is a solver (`et17Procs`,
   `et17_solves`).
8. For the claim: the need is polynomially bounded (`hostNeed_poly`), the time obeys the bound of
   Theorem 17 (`obeysBound17_hostTime`), and so the claim holds for programs of the light language
   (`claim17_of_host`, `claim_theorem_17₅`, `claim_theorem_17₂₆`).

The layout, from the free pointer `fr` on: the table of doubles (`len + 1` cells, where
`len = bitLen U` is the number of binary digits of `U`; cell `j` holds `2^j p`, for residues without
division); the residues of `w(a,b)`, `w(b,c)`, `w(a,c)` (`n²` each); the starts of the classes
(`p + 1`); running places (`p`; while the pairs are sorted, cell `ϱ` holds the next free place of
the class `ϱ`); rows and columns of the sorted pairs (`n²` each); the three components of the table
of chunks (`n² + p` each); `X` (`n D`); `Y` (`D n`); the answers (`cap`); the solver's free pointer.

Notation: `κ` is the exponent in `|w(e)| ≤ n^κ`, the paper's ν; as in the paper, `F(p)` is the
number of false positives of `p`, that is, of triples with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≠ 0`
and `p ∣ S(a,b,c)`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The procedure -/



























namespace Et17












































end Et17



































































/-! ## Time and need

The additive constants in the time functions are upper bounds for the cost of evaluating arguments,
of calls and of tests.  They are not meant to be tight. -/















































































/-! ## The context -/






























/-! ## The data, the addresses and the local variables of a run -/


































/-- The arrays of the host stand one after the other. -/
theorem host_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCur X U fr = aCls X U fr + (X.p + 1) ∧ aQi X U fr = aCur X U fr + X.p ∧
      aQj X U fr = aQi X U fr + X.n * X.n ∧ aCr X U fr = aQj X U fr + X.n * X.n ∧
      aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧ aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧
      aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧ aY X U fr = aX X U fr + X.n * X.D ∧
      aOut X U fr = aY X U fr + X.n * X.D ∧ aFr X U fr = aOut X U fr + X.cap :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩







































end Light.Sec3

end
end

section


/-!
The additional successful scans in the all-edges variant do not worsen Theorem 17's
asymptotic bound. At most `n²` successes each cost `O(√D)`; the source's parameter
inequality `√D g ≤ n` puts this within `O(κ n³ log n / g)`.
-/

namespace APSPImprovement.AllEdges

open Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

theorem pieceSize_steps : StepsMon (fun θ => pieceSizeNat θ.D θ.g) 0 1 0 :=
  steps_sqrt.of_le fun _ hθ =>
    (Nat.ceilDiv_le_iff hθ.hg).2 (Nat.le_mul_of_pos_right _ hθ.hg)

/-- The `n²` possible successes fit the original host's three-term budget. -/
theorem successful_scans_within_budget :
    Steps (fun θ => (tScan (pieceSizeNat θ.D θ.g) + 20) * (θ.n * θ.n)) budget := by
  have h : StepsMon (fun θ => (tScan (pieceSizeNat θ.D θ.g) + 20) * (θ.n * θ.n)) 2 1 0 := by
    unfold tScan
    first
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply pieceSize_steps
                | apply steps_n
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div);
        (·
            first
            | decide
            | exact isEmptyElim))
    |
      ((fail_if_success
            (fail_if_success
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (on_goal 1 =>
                      ((repeat'
                            with_reducible
                              first
                              | exact ThreeSumApsp.Scale.SoftO.const _
                              | apply pieceSize_steps
                              | apply steps_n
                              | apply ThreeSumApsp.Scale.SoftO.add
                              | apply ThreeSumApsp.Scale.SoftO.mul
                              | apply ThreeSumApsp.Scale.SoftO.pow
                              | apply ThreeSumApsp.Scale.SoftO.max
                              | apply ThreeSumApsp.Scale.SoftO.sub
                              | apply ThreeSumApsp.Scale.SoftO.div);
                        (done))))));
        (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
        (all_goals
            try
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (·
                    repeat'
                      with_reducible
                        first
                        | exact ThreeSumApsp.Scale.SoftO.const _
                        | apply pieceSize_steps
                        | apply steps_n
                        | apply ThreeSumApsp.Scale.SoftO.add
                        | apply ThreeSumApsp.Scale.SoftO.mul
                        | apply ThreeSumApsp.Scale.SoftO.pow
                        | apply ThreeSumApsp.Scale.SoftO.max
                        | apply ThreeSumApsp.Scale.SoftO.sub
                        | apply ThreeSumApsp.Scale.SoftO.div);
                (· decide))))
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply pieceSize_steps
                | apply steps_n
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div))
  exact h.withinScans








/-- Refined piece cost, retaining the saving by `g`. This follows the existing
source proof of `steps_tScanCall`, with the new scan-and-store overhead. -/
theorem scan_piece_ratio :
    Steps (fun θ => tScan (pieceSizeNat θ.D θ.g) + 20)
      (fun θ => Real.sqrt θ.D / θ.g) := by
  have hone : ∀ θ : CostParams, θ.Hyp → 1 ≤ Real.sqrt θ.D / θ.g :=
    fun θ hθ => (one_le_div hθ.g_pos).2 hθ.hgD
  have hpiece : Steps (fun θ => pieceSizeNat θ.D θ.g) (fun θ => Real.sqrt θ.D / θ.g) := by
    refine Dominated.of_le_const_mul (C := 2) (by norm_num) fun θ hθ => ?_
    have hlt : (pieceSizeNat θ.D θ.g : ℝ) * θ.g < (Nat.sqrt θ.D : ℝ) + θ.g := by
      exact_mod_cast Nat.ceilDiv_mul_lt (a := Nat.sqrt θ.D) hθ.hg
    rw [← mul_div_assoc, le_div_iff₀ hθ.g_pos]
    linarith [hlt, Real.nat_sqrt_le_real_sqrt (a := θ.D), hθ.hgD]
  exact (hpiece.const_mul.add (.const hone)).add (.const hone)

theorem false_positive_steps :
    Steps (fun θ => falsePositiveBound θ.n θ.U θ.D)
      (fun θ => θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n / Real.sqrt θ.D) := by
  have hc : 0 ≤ Hashing.falsePositiveConst := zero_le_one.trans Hashing.one_le_falsePositiveConst
  refine Dominated.of_le_const_mul hc fun θ hθ => (Nat.floor_le ?_).trans ?_
  · have hk : 0 ≤ kappaOf θ.n θ.U := zero_le_one.trans (one_le_kappaOf θ.n θ.U)
    positivity
  · have hk : kappaOf θ.n θ.U ≤ θ.κ := by
      rcases Nat.eq_zero_or_pos θ.U with hU | hU
      · simp [kappaOf, hU, hθ.hκ]
      · exact kappaOf_le ((by norm_num : 2 ≤ 16).trans hθ.sixteen_le_n) hU hθ.hκ hθ.hUn
    gcongr

theorem failed_scans_within_budget :
    Steps (fun θ => (tScan (pieceSizeNat θ.D θ.g) + 20) * falsePositiveBound θ.n θ.U θ.D)
      budget := by
  refine (scan_piece_ratio.mul false_positive_steps).mono_right fun θ hθ =>
    le_trans (le_of_eq ?_) (termScans_le_budget θ)
  have hr := hθ.sqrt_pos
  have hg := hθ.g_pos
  unfold termScans
  field_simp

theorem all_scans_within_budget :
    Steps (fun θ => (tScan (pieceSizeNat θ.D θ.g) + 20) *
      (falsePositiveBound θ.n θ.U θ.D + θ.n * θ.n)) budget := by
  simpa only [Nat.mul_add] using failed_scans_within_budget.add successful_scans_within_budget

theorem instances_steps : StepsMon (fun θ => 4 * θ.n * θ.g) 1 1 0 := by
  have hg : StepsMon (fun θ => θ.g) 0 1 0 :=
    (Scale.SoftO.of_le_base (s := costScale) 1 fun _ hθ => hθ.hgD).mono (by decide)
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply hg
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_n
                            | apply hg
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_n
                      | apply hg
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_n
              | apply hg
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

theorem instance_setup_within_budget :
    Steps (fun θ => 4 * θ.n * θ.g *
      (tWriteX θ.n θ.D (pieceSizeNat θ.D θ.g) +
        tWriteY θ.n θ.D (pieceSizeNat θ.D θ.g) + 113)) budget := by
  have h : StepsMon (fun θ => 4 * θ.n * θ.g *
      (tWriteX θ.n θ.D (pieceSizeNat θ.D θ.g) +
        tWriteY θ.n θ.D (pieceSizeNat θ.D θ.g) + 113)) 2 3 0 := by
    first
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply instances_steps
                | apply steps_tWriteX
                | apply steps_tWriteY
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div);
        (·
            first
            | decide
            | exact isEmptyElim))
    |
      ((fail_if_success
            (fail_if_success
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (on_goal 1 =>
                      ((repeat'
                            with_reducible
                              first
                              | exact ThreeSumApsp.Scale.SoftO.const _
                              | apply instances_steps
                              | apply steps_tWriteX
                              | apply steps_tWriteY
                              | apply ThreeSumApsp.Scale.SoftO.add
                              | apply ThreeSumApsp.Scale.SoftO.mul
                              | apply ThreeSumApsp.Scale.SoftO.pow
                              | apply ThreeSumApsp.Scale.SoftO.max
                              | apply ThreeSumApsp.Scale.SoftO.sub
                              | apply ThreeSumApsp.Scale.SoftO.div);
                        (done))))));
        (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
        (all_goals
            try
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (·
                    repeat'
                      with_reducible
                        first
                        | exact ThreeSumApsp.Scale.SoftO.const _
                        | apply instances_steps
                        | apply steps_tWriteX
                        | apply steps_tWriteY
                        | apply ThreeSumApsp.Scale.SoftO.add
                        | apply ThreeSumApsp.Scale.SoftO.mul
                        | apply ThreeSumApsp.Scale.SoftO.pow
                        | apply ThreeSumApsp.Scale.SoftO.max
                        | apply ThreeSumApsp.Scale.SoftO.sub
                        | apply ThreeSumApsp.Scale.SoftO.div);
                (· decide))))
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply instances_steps
                | apply steps_tWriteX
                | apply steps_tWriteY
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div))
  exact h.withinPrime

noncomputable def allRestBound (θ : CostParams) : ℝ :=
  (θ.n : ℝ) * θ.g * ((θ.n : ℝ) ^ 2 / Real.sqrt θ.D) + budget θ

theorem Steps.toAllRest {t : CostParams → ℕ} (h : Steps t budget) : Steps t allRestBound :=
  h.mono_right fun _ _ => le_add_of_nonneg_left (by positivity)

theorem reading_answers_steps :
    Steps (fun θ => 4 * θ.n * θ.g * (64 * queryCapNat θ.n θ.D)) allRestBound := by
  have hi : Steps (fun θ => 4 * θ.n * θ.g) (fun θ => (θ.n : ℝ) * θ.g) :=
    (Steps.const_mul (Dominated.refl _ _)).mul (Dominated.refl _ _)
  have hc : Steps (fun θ => 64 * queryCapNat θ.n θ.D)
      (fun θ => (θ.n : ℝ) ^ 2 / Real.sqrt θ.D) :=
    Steps.const_mul (Dominated.of_le fun _ hθ => cast_queryCapNat_le hθ)
  exact (hi.mul hc).mono_right fun _ hθ => le_add_of_nonneg_right (budget_nonneg hθ)

end APSPImprovement.AllEdges





end

section


/-!
The existing Theorem 17 oracle calls and their order suffice for the all-edges
variant. Only the scan scheduler changes: its persistent table records each pair
separately. The original coverage and false-positive lemmas prove correctness and
the new total scan bound for this table.
-/

namespace APSPImprovement.AllEdges

open Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

def hostQuery (X : HostData) (t i : ℕ) : Query :=
  ⟨X.place t i, X.acc t i, X.hit t i⟩

/-- All queries of an instance, in the original host's order. -/
def instanceQueries (X : HostData) (t : ℕ) : List Query :=
  (List.range (X.w t)).map (hostQuery X t)

/-- The oracle queries of the first `T` instances, in program order. -/
def hostQueries (X : HostData) : ℕ → List Query
  | 0 => []
  | T + 1 => hostQueries X T ++ instanceQueries X T

theorem mem_instanceQueries (X : HostData) (t : ℕ) (q : Query) :
    q ∈ instanceQueries X t ↔ ∃ i < X.w t, hostQuery X t i = q := by
  simp [instanceQueries]

theorem mem_hostQueries (X : HostData) (T : ℕ) (q : Query) :
    q ∈ hostQueries X T ↔ ∃ t < T, ∃ i < X.w t, hostQuery X t i = q := by
  induction T with
  | zero => simp [hostQueries]
  | succ T ih =>
    rw [hostQueries, List.mem_append, ih, mem_instanceQueries]
    constructor
    · rintro (⟨t, ht, h⟩ | h)
      · exact ⟨t, by omega, h⟩
      · exact ⟨T, by omega, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact Or.inl ⟨t, ht, h⟩
      · exact Or.inr h

theorem failures_append (qs rs : List Query) :
    failures (qs ++ rs) = failures qs + failures rs := by
  simp [failures]

theorem failures_instanceQueries (X : HostData) (t : ℕ) :
    failures (instanceQueries X t) = X.fails t := by
  simp only [failures, instanceQueries, List.filter_map, List.length_map,
    HostData.fails, Light.Sec3.failsUpto, Function.comp_def, hostQuery]

theorem failures_hostQueries (X : HostData) (T : ℕ) :
    failures (hostQueries X T) = ∑ t ∈ Finset.range T, X.fails t := by
  induction T with
  | zero => simp [hostQueries, failures]
  | succ T ih =>
    rw [hostQueries, failures_append, ih, failures_instanceQueries, Finset.sum_range_succ]

/-- Every output flag address is within the `n²`-entry table. -/
theorem hostQueries_pair_lt {X : HostData} (hv : X.Valid) {q : Query}
    (hq : q ∈ hostQueries X X.m) : q.pair < X.n * X.n := by
  obtain ⟨t, ht, i, hi, rfl⟩ := (mem_hostQueries X X.m q).1 hq
  exact hv.place_lt ht hi

/-- The all-edges replacement for the source's `HostData.sum_execs_le`.
There is at most one successful executed scan per pair, hence the additive `n²`. -/
theorem scans_le_falsePositives {X : HostData} (hv : X.Valid) :
    (run (hostQueries X X.m) ∅).scans ≤
      (triOf X.n X.AB X.BC X.AC).F X.p + X.n * X.n := by
  have h := scans_le_failures_add (hostQueries X X.m) (X.n * X.n)
    (fun _ hq => hostQueries_pair_lt hv hq)
  rw [failures_hostQueries] at h
  exact h.trans (Nat.add_le_add_right (HostData.sum_fails_le hv) _)

/-- After every instance, a pair is marked exactly when a zero triangle contains it. -/
theorem pair_mem_found_iff {X : HostData} (hv : X.Valid) {a b : ℕ}
    (ha : a < X.n) (hb : b < X.n) :
    a * X.n + b ∈ (run (hostQueries X X.m) ∅).found ↔
      ∃ c < X.n, X.sumAt a b c = 0 := by
  rw [mem_found_iff]
  simp only [Finset.notMem_empty, false_or]
  constructor
  · rintro ⟨q, hq, hpair, _, hhit⟩
    obtain ⟨t, ht, i, hi, rfl⟩ := (mem_hostQueries X X.m q).1 hq
    change X.place t i = a * X.n + b at hpair
    have hrow : X.rowOf t i = a := by
      rw [HostData.rowOf, hpair, Nat.mul_add_div_of_lt hb]
    have hcol : X.colOf t i = b := by
      rw [HostData.colOf, hpair, Nat.mul_add_mod_of_lt hb]
    obtain ⟨c, hc, hz⟩ := (HostData.hit_iff hi).1 hhit
    rw [hrow, hcol] at hz
    have hpiece := hv.piece_le ht
    exact ⟨X.c0 t + c, by omega, hz⟩
  · rintro ⟨c, hc, hz⟩
    obtain ⟨t, ht, i, hi, hrow, hcol, c', hc', hvertex⟩ := hv.exists_query ha hb hc
    have hzero : X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c') = 0 := by
      simpa [hrow, hcol, hvertex] using hz
    refine ⟨hostQuery X t i, (mem_hostQueries X X.m _).2 ⟨t, ht, i, hi, rfl⟩, ?_, ?_, ?_⟩
    · change X.place t i = a * X.n + b
      rw [← HostData.rowOf_mul_add_colOf, hrow, hcol]
    · exact (HostData.acc_iff hv ht hi).2 ⟨c', hc', hzero ▸ dvd_zero _⟩
    · exact (HostData.hit_iff hi).2 ⟨c', hc', hzero⟩

/-- The table produced by the executable pure scheduler. -/
def outputFlags (X : HostData) : List ℤ :=
  (List.range (X.n * X.n)).map fun q =>
    if q ∈ (run (hostQueries X X.m) ∅).found then 1 else 0

/-- The table has exactly the public all-edges AB output specification. -/
theorem outputFlags_eq {X : HostData} (hv : X.Valid) :
    outputFlags X = abZeroFlags X.n X.AB X.BC X.AC := by
  apply List.map_congr_left
  intro q hq
  have hq' := List.mem_range.1 hq
  have ha : q / X.n < X.n := Nat.div_lt_of_lt_mul' hq'
  have hb : q % X.n < X.n := Nat.mod_lt_of_lt_mul hq'
  have h := pair_mem_found_iff hv ha hb
  rw [Nat.div_add_mod'] at h
  simp only [HostData.sumAt, Nat.div_add_mod'] at h
  simp only [flag, h]
  split_ifs <;> rfl

end APSPImprovement.AllEdges





end

section


/-! The persistent flag-table invariant connecting pure scheduling to machine memory. -/

namespace APSPImprovement.AllEdges

open Light Light.Sec3

/-- A memory region stores the zero/one membership flags of the solved-pair set. -/
def FlagTable (μ : ℕ → ℤ) (dst N : ℕ) (found : Finset ℕ) : Prop :=
  ∀ q < N, μ (dst + q) = bit (decide (q ∈ found))

def queryMemory (μ : ℕ → ℤ) (dst : ℕ) (found : Finset ℕ) (q : Query) : ℕ → ℤ :=
  pairMemory μ (dst + q.pair) q.accepted (decide (q.pair ∈ found)) q.hit

theorem run_cons_found (q : Query) (qs : List Query) (found : Finset ℕ) :
    (run (q :: qs) found).found = (run qs (run [q] found).found).found := by
  by_cases hm : q.pair ∈ found <;> cases ha : q.accepted <;> cases hh : q.hit <;>
    simp [run, hm, ha, hh]

theorem run_cons_scans (q : Query) (qs : List Query) (found : Finset ℕ) :
    (run (q :: qs) found).scans =
      (run [q] found).scans + (run qs (run [q] found).found).scans := by
  by_cases hm : q.pair ∈ found <;> cases ha : q.accepted <;> cases hh : q.hit <;>
    simp [run, hm, ha, hh, Nat.add_comm]

theorem run_append_found (qs rs : List Query) (found : Finset ℕ) :
    (run (qs ++ rs) found).found = (run rs (run qs found).found).found := by
  induction qs generalizing found with
  | nil => rfl
  | cons q qs ih =>
    rw [List.cons_append, run_cons_found q (qs ++ rs) found,
      ih, run_cons_found q qs found]

theorem run_append_scans (qs rs : List Query) (found : Finset ℕ) :
    (run (qs ++ rs) found).scans =
      (run qs found).scans + (run rs (run qs found).found).scans := by
  induction qs generalizing found with
  | nil => simp [run]
  | cons q qs ih =>
    rw [List.cons_append, run_cons_scans q (qs ++ rs) found,
      ih, run_cons_scans q qs found, run_cons_found q qs found, Nat.add_assoc]

theorem queryMemory_table {μ : ℕ → ℤ} {dst N : ℕ} {found : Finset ℕ} {q : Query}
    (htable : FlagTable μ dst N found) (hq : q.pair < N) :
    FlagTable (queryMemory μ dst found q) dst N (run [q] found).found := by
  intro p hp
  by_cases heq : p = q.pair
  · subst p
    rw [queryMemory, pairMemory_read _ _ _ _ _ (htable _ hq)]
    apply congrArg bit
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [mem_found_iff]
    simp
  · rw [queryMemory, pairMemory_away _ _ _ _ _ (by omega), htable p hp]
    apply congrArg bit
    apply Bool.eq_iff_iff.2
    simp [mem_found_iff, Ne.symm heq]

theorem queryMemory_outside (μ : ℕ → ℤ) (dst N : ℕ) (found : Finset ℕ) (q : Query)
    (hq : q.pair < N) : SameOutside μ (queryMemory μ dst found q) dst N := by
  intro addr haddr
  exact pairMemory_away μ _ _ _ _ (by omega)

/-- The exact memory changes made by a sequence of calls to `scanPair`. -/
def runMemory : List Query → Finset ℕ → (ℕ → ℤ) → ℕ → (ℕ → ℤ)
  | [], _, μ, _ => μ
  | q :: qs, found, μ, dst =>
    runMemory qs (run [q] found).found (queryMemory μ dst found q) dst

theorem runMemory_table (qs : List Query) {μ : ℕ → ℤ} {dst N : ℕ} {found : Finset ℕ}
    (htable : FlagTable μ dst N found) (hpairs : ∀ q ∈ qs, q.pair < N) :
    FlagTable (runMemory qs found μ dst) dst N (run qs found).found := by
  induction qs generalizing found μ with
  | nil => simpa [runMemory, run] using htable
  | cons q qs ih =>
    rw [runMemory, run_cons_found q qs found]
    exact ih (queryMemory_table htable (hpairs q (by simp)))
      (fun r hr => hpairs r (by simp [hr]))

theorem runMemory_outside (qs : List Query) (μ : ℕ → ℤ) (dst N : ℕ) (found : Finset ℕ)
    (hpairs : ∀ q ∈ qs, q.pair < N) : SameOutside μ (runMemory qs found μ dst) dst N := by
  induction qs generalizing found μ with
  | nil => exact SameOn.refl
  | cons q qs ih =>
    exact (queryMemory_outside μ dst N found q (hpairs q (by simp))).trans
      (ih _ _ (fun r hr => hpairs r (by simp [hr])))

theorem runMemory_append (qs rs : List Query) (found : Finset ℕ) (μ : ℕ → ℤ) (dst : ℕ) :
    runMemory (qs ++ rs) found μ dst =
      runMemory rs (run qs found).found (runMemory qs found μ dst) dst := by
  induction qs generalizing found μ with
  | nil => rfl
  | cons q qs ih =>
    rw [List.cons_append, runMemory, ih, runMemory, run_cons_found q qs found]

/-- The queryPrefix of the query sequence processed by a counting loop. -/
def queryPrefix (q : ℕ → Query) (i : ℕ) : List Query := (List.range i).map q

theorem prefix_succ (q : ℕ → Query) (i : ℕ) : queryPrefix q (i + 1) = queryPrefix q i ++ [q i] := by
  simp [queryPrefix, List.range_succ]

theorem prefixMemory_succ (q : ℕ → Query) (i : ℕ) (found : Finset ℕ) (μ : ℕ → ℤ)
    (dst : ℕ) :
    runMemory (queryPrefix q (i + 1)) found μ dst =
      queryMemory (runMemory (queryPrefix q i) found μ dst) dst (run (queryPrefix q i) found).found (q i) := by
  rw [prefix_succ, runMemory_append]
  rfl

theorem prefixScans_succ (q : ℕ → Query) (i : ℕ) (found : Finset ℕ) :
    (run (queryPrefix q (i + 1)) found).scans =
      (run (queryPrefix q i) found).scans +
        (if (q i).accepted && decide ((q i).pair ∉ (run (queryPrefix q i) found).found) then 1 else 0) := by
  rw [prefix_succ, run_append_scans]
  simp [run]
  split_ifs <;> rfl

end APSPImprovement.AllEdges




end

section


/-!
The original host's matrix writing, oracle calling, and counter lemmas remain
unchanged. The new invariant permits the persistent answer table to change and
keeps every original read-only host array disjoint from that table.
-/

namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

structure FlagsLay (X : HostData) (A : HostAddr) (dst : ℕ) : Prop where
  below : dst + X.n * X.n ≤ A.x
  ab : Apart A.ab (X.n * X.n) dst (X.n * X.n)
  bc : Apart A.bc (X.n * X.n) dst (X.n * X.n)
  ac : Apart A.ac (X.n * X.n) dst (X.n * X.n)
  rac : Apart A.rac (X.n * X.n) dst (X.n * X.n)
  rbc : Apart A.rbc (X.n * X.n) dst (X.n * X.n)
  qi : Apart A.qi (X.n * X.n) dst (X.n * X.n)
  qj : Apart A.qj (X.n * X.n) dst (X.n * X.n)
  cr : Apart A.cr X.chunkCount dst (X.n * X.n)
  cl : Apart A.cl X.chunkCount dst (X.n * X.n)
  cw : Apart A.cw X.chunkCount dst (X.n * X.n)

theorem FlagTable.keep_below {μ μ' : ℕ → ℤ} {dst N top : ℕ} {found : Finset ℕ}
    (h : FlagTable μ dst N found) (hs : Kept μ μ' top) (hb : dst + N ≤ top) :
    FlagTable μ' dst N found := by
  intro q hq
  rw [hs (dst + q) (by omega), h q hq]

/-- Updating only flags preserves all the arrays the next oracle instance reads. -/
theorem hostMem_keep_flags {X : HostData} {A : HostAddr} {dst : ℕ} {μ μ' : ℕ → ℤ}
    (hv : X.Valid) (h : HostMem X A μ) (F : FlagsLay X A dst)
    (hs : SameOutside μ μ' dst (X.n * X.n)) : HostMem X A μ' := by
  have lenRAC : X.RAC.length = X.n * X.n := by simp [HostData.RAC, residList, hv.lenAC]
  have lenRBC : X.RBC.length = X.n * X.n := by simp [HostData.RBC, residList, hv.lenBC]
  have lenQI := hv.length_QI
  have lenQJ := hv.length_QJ
  have lenCT : X.CT.length = X.chunkCount := rfl
  exact
    { segAB := h.segAB.of_sameOutside hs (by simpa only [hv.lenAB] using F.ab)
      segBC := h.segBC.of_sameOutside hs (by simpa only [hv.lenBC] using F.bc)
      segAC := h.segAC.of_sameOutside hs (by simpa only [hv.lenAC] using F.ac)
      segRAC := h.segRAC.of_sameOutside hs (by simpa only [lenRAC] using F.rac)
      segRBC := h.segRBC.of_sameOutside hs (by simpa only [lenRBC] using F.rbc)
      segQI := h.segQI.of_sameOutside hs (by simpa only [lenQI] using F.qi)
      segQJ := h.segQJ.of_sameOutside hs (by simpa only [lenQJ] using F.qj)
      segCR := h.segCR.of_sameOutside hs (by simpa only [List.length_map, lenCT] using F.cr)
      segCL := h.segCL.of_sameOutside hs (by simpa only [List.length_map, lenCT] using F.cl)
      segCW := h.segCW.of_sameOutside hs (by simpa only [List.length_map, lenCT] using F.cw) }

def foundAfter (X : HostData) (t : ℕ) : Finset ℕ := (run (hostQueries X t) ∅).found

def instanceScans (X : HostData) (t : ℕ) : ℕ :=
  (run (instanceQueries X t) (foundAfter X t)).scans



theorem foundAfter_succ (X : HostData) (t : ℕ) :
    foundAfter X (t + 1) = (run (instanceQueries X t) (foundAfter X t)).found := by
  exact run_append_found _ _ _

theorem sum_instanceScans (X : HostData) (T : ℕ) :
    ∑ t ∈ Finset.range T, instanceScans X t = (run (hostQueries X T) ∅).scans := by
  induction T with
  | zero => simp [hostQueries, run]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, hostQueries, run_append_scans]
    rfl

theorem sum_instanceScans_le {X : HostData} (hv : X.Valid) :
    ∑ t ∈ Finset.range X.m, instanceScans X t ≤
      (triOf X.n X.AB X.BC X.AC).F X.p + X.n * X.n := by
  rw [sum_instanceScans]
  exact scans_le_falsePositives hv

end APSPImprovement.AllEdges




end

section


/-!
# The number of chunks, on lists and on sets of pairs (proof of Theorem 17)

The routines work with lists of places: `classIdx` lists the places `a n + b` of the pairs of a
class, and the table `chunkTab` has one entry for each chunk.  The paper's class `W_ϱ` is a set of
pairs (`residueClass`).  The map `(a, b) ↦ a n + b` is a bijection between the set and the list, so
both have the same number of elements (`length_classIdx_eq_card`), and the table has as many entries
as there are chunks "in all" (`length_chunkTab_eq_totalChunks`).  The instance is
`triOf n AB BC AC`, whose weights `w(a,b)` are read from the list `AB`, row by row.
-/

public section

namespace ThreeSumApsp.Spec

variable (n : ℕ) {p : ℕ} (AB BC AC : List ℤ)




















/-- The table has one entry for each chunk. -/
theorem length_chunkTab_eq_totalChunks (hp : p ≠ 0) {D : ℕ} (hD : 1 ≤ D)
    (hcap : 1 ≤ queryCapNat n D) :
    (chunkTab n p (queryCapNat n D) (residList p AB)).length =
      (triOf n AB BC AC).totalChunks D p := by
  rw [length_chunkTab, List.sum_map_range, Finset.sum_range, TriangleInstance.totalChunks]
  refine Finset.sum_congr rfl fun ϱ _ => ?_
  rw [← queryCapNat_eq n hD, numChunks_eq _ hcap, ← length_classIdx_eq_card n AB BC AC hp ϱ]

end ThreeSumApsp.Spec

end
end

section


/-!
# The number of instances of the host of Theorem 17

Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances", where `s = ⌊√D⌋` and
`h` is the number of pieces.  The host's table of chunks has as many entries as the paper's count of
the chunks (`length_chunkTab_eq_totalChunks`), and its number of pieces is the paper's
(`numPiecesNat_eq`), so the bound of `TriangleInstance.card_instanceIndices_le` applies.
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances".  Here `m` is the
number of instances of the host. -/
theorem HostData.m_le {n D g p : ℕ} {AB BC AC : List ℤ} (h : BigCase n D g)
    (hp : p ∈ primesInRange D) :
    (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).m ≤ 4 * n * g := by
  obtain ⟨hD, hDn, hg, -⟩ := h
  have hD1 : 1 ≤ D := by omega
  have hcap : 1 ≤ queryCapNat n D := by rw [queryCapNat_eq n hD1]; exact one_le_queryCap hD1 hDn
  -- The host's numbers of pieces and of chunks are the paper's.
  have hpieces :
      (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).h = numPieces n D g :=
    numPiecesNat_eq n D hg (pieceSize_pos hD hg)
  have hchunks : (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).chunkCount
      = (triOf n AB BC AC).totalChunks D p :=
    length_chunkTab_eq_totalChunks n AB BC AC (mem_primesInRange.mp hp).1.ne_zero hD1 hcap
  have hcard : (((triOf n AB BC AC).instanceIndices D g p).card : ℝ) ≤ ((4 * n * g : ℕ) : ℝ) := by
    push_cast
    exact (triOf n AB BC AC).card_instanceIndices_le hD hDn hg hp
  rw [HostData.m, hpieces, hchunks, Nat.mul_comm, ← TriangleInstance.card_instanceIndices]
  exact_mod_cast hcard

end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the limits

The host procedure `et17` (Exact Triangle by Theorem 17) states what it needs of the limits of a
run: word size, memory, depth of calls (`hostNeedAt`).  This file shows that this need covers what
the procedures that it calls ask for.

* The arrays of the host lie one behind the other and fit into the cells that `hostLayout` counts
  (`aFr_le`).
* Every number that is at most `hostWord` fits in a word (`le_word_of_le_hostWord`).
* So the preconditions of the choice of the prime and of the loop over the instances hold
  (`choosePre_of_ok`, `hostLim_of_ok`).  For the solver this uses that an instance has at most
  `⌊n²/√D⌋` query pairs (`HostData.w_le_cap`, `need_le_supNeed`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The case that n is not small -/

/-- The host falls back on the brute force exactly if the hypotheses of Theorem 17 fail. -/
theorem not_smallCase_iff {n D g : ℕ} : ¬ SmallCase n D g ↔ BigCase n D g := by
  unfold SmallCase
  exact ⟨fun h => ⟨by omega, by omega, by omega, by omega⟩,
    fun ⟨_, _, _, _⟩ => by omega⟩

/-- The chosen prime is at most √D. -/
theorem hostData_p_le (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) :
    (hostData x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

/-- The chosen prime is at least 2. -/
theorem two_le_hostData_p (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) : 2 ≤ (hostData x D g).p :=
  two_le_chosenPrime x.AB x.BC x.AC hD

/-- There are at most `4ng` instances. -/
theorem hostData_m_le {x : TriInst} {D g : ℕ} (h : BigCase x.n D g) :
    (hostData x D g).m ≤ 4 * x.n * g :=
  HostData.m_le h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le)

/-- The data of a run are valid. -/
theorem hostData_valid {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData x D g).Valid :=
  HostData.valid_of_params h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le) hpre.lenAB hpre.lenBC
    hpre.lenAC

/-! ## The addresses -/

/-- The free pointer of the solver, written out. -/
private theorem aFr_eq (X : HostData) (U fr : ℕ) :
    aFr X U fr = fr + (bitLen U + 1) + 3 * (X.n * X.n) + (X.p + 1) + X.p + 2 * (X.n * X.n)
      + 3 * (X.n * X.n + X.p) + 2 * (X.n * X.D) + X.cap := by
  simp only [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, aRac, aRbc, aRab]
  omega

/-- The arrays of et17 fit into the cells that hostLayout counts. -/
theorem aFr_le {x : TriInst} {D g : ℕ} (hD : 16 ≤ D) (fr : ℕ) :
    aFr (hostData x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  have hp := hostData_p_le x g hD
  rw [aFr_eq]
  unfold hostLayout
  change fr + (bitLen x.U + 1) + 3 * (x.n * x.n) + ((hostData x D g).p + 1) + (hostData x D g).p
    + 2 * (x.n * x.n) + 3 * (x.n * x.n + (hostData x D g).p) + 2 * (x.n * D) + queryCapNat x.n D ≤ _
  omega

/-! ## The words -/

/-- The numbers of the host fit in a word. -/
private theorem hostWord_le {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) :
    ((hostWord a b n U D g : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast Nat.le_add_right _ _) hok.word

/-- A number that is at most hostWord fits in a word. -/
theorem le_word_of_le_hostWord {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) {z : ℕ}
    (hz : z ≤ hostWord a b n U D g := by unfold hostWord; omega) : ((z : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hz) (hostWord_le hok)





















/-- The need of the solver on an instance with at most cap query pairs is at most supNeed. -/
private theorem need_le_supNeed (need : List ℕ → Need) (n D : ℕ) {cap w : ℕ} (hw : w ≤ cap) :
    (need [n, D, w]).word ≤ (supNeed need n D cap).word ∧
      (need [n, D, w]).cells ≤ (supNeed need n D cap).cells ∧
      (need [n, D, w]).depth ≤ (supNeed need n D cap).depth := by
  have hm : w ∈ Finset.range (cap + 1) := Finset.mem_range.2 (by omega)
  exact ⟨Finset.le_sup (f := fun v => (need [n, D, v]).word) hm,
    Finset.le_sup (f := fun v => (need [n, D, v]).cells) hm,
    Finset.le_sup (f := fun v => (need [n, D, v]).depth) hm⟩

/-- What hostLoop asks of the limits. -/
theorem hostLim_of_ok {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst}
    {fr D g : ℕ} (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData x D g) x.U (hostAddr x (hostData x D g) fr) need := by
  have hD : 16 ≤ D := hbig.sixteen_le
  have hcells : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n D (queryCapNat x.n D)).cells + 2) ≤ lim.space := hok.cells
  have hdepth : d + (2 * Nat.clog 2 x.n + 8 + (supNeed need x.n D (queryCapNat x.n D)).depth)
      ≤ lim.depth := hok.depth
  have hword : ((hostWord a b x.n x.U D g + (supNeed need x.n D (queryCapNat x.n D)).word : ℕ) : ℤ)
      ≤ lim.word := hok.word
  have hfr := aFr_le (x := x) (g := g) hD fr
  have hp := hostData_p_le x g hD
  have hm := hostData_m_le hbig
  have hlay : 2 * Nat.sqrt D ≤ hostLayout x.n x.U D := by unfold hostLayout; omega
  exact
    { space := hok.space
      fr := by change aFr (hostData x D g) x.U fr < lim.space; omega
      prime := by omega
      count := le_word_of_le_hostWord hok (hm.trans (by unfold hostWord; omega))
      step := le_word_of_le_hostWord hok (by
        change x.n + pieceSizeNat D g ≤ _
        unfold hostWord
        omega)
      weights := le_word_of_le_hostWord hok
      depth := by omega
      solver := fun t ht => by
        have hwc : (hostData x D g).w t ≤ queryCapNat x.n D := (hostData x D g).w_le_cap ht
        obtain ⟨hsword, hscells, hsdepth⟩ := need_le_supNeed need x.n D hwc
        change (need [x.n, D, (hostData x D g).w t]).Ok lim (aFr (hostData x D g) x.U fr)
          (d + 1 + 1)
        exact ⟨le_trans (Nat.cast_le.2 (hsword.trans (Nat.le_add_left _ _))) hword, by omega,
          hok.space, by omega⟩ }

end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the time of a run is within the worst case

The host procedure `et17` (Exact Triangle by Theorem 17) first computes the parameters, chooses the
prime and computes the sizes.  The time of what follows (the table of doubles, the residues, the
classes, the chunks and the loop over the instances; `hostRunTime`) depends on the data: the prime,
the number of chunks, the scans.  Here it is bounded by the corresponding summands of `hostMain`,
which depend on `n`, `U`, `D` and `g` only (`hostRunTime_le`).

* The prime is at most `√D` (`hostData_p_le`), and there are at most `4ng` instances and no more
  chunks than instances (`hostData_m_le`, `HostTime.chunkCount_le_m`).
* An instance has a piece of at most `q = ⌈s/g⌉` vertices, where `s = ⌊√D⌋`, and at most `⌊n²/√D⌋`
  query pairs, so its time without the scans is at most the worst case (`HostTime.instance_le`).
* All scans but one fail, and a failed scan belongs to a false positive of the chosen prime.  The
  proof of Theorem 17 bounds their number (`F_le_falsePositiveBound`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The number of false positives of the chosen prime is at most `falsePositiveBound`. -/
theorem F_le_falsePositiveBound {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) :
    (triOf x.n x.AB x.BC x.AC).F (chosenPrime x.n D x.AB x.BC x.AC)
      ≤ falsePositiveBound x.n x.U D :=
  Nat.le_floor (F_chosenPrime_le h.sixteen_le h.le_n hpre.U_pos hpre.leAB hpre.leBC hpre.leAC)

namespace HostTime

/-! ## One instance -/

/-- Writing the two matrices of an instance takes longer for a longer piece. -/
private theorem tWrites_mono (n D : ℕ) {a b : ℕ} (h : a ≤ b) : tWrites n D a ≤ tWrites n D b := by
  unfold tWrites tWriteX tWriteY
  gcongr

/-- The time of the solver on an instance with at most `cap` query pairs is at most `supTime`, its
largest time on such instances. -/
private theorem le_supTime (Tn : List ℕ → ℕ) (n D : ℕ) {w cap : ℕ} (h : w ≤ cap) :
    Tn [n, D, w] ≤ supTime Tn n D cap :=
  Finset.le_sup (f := fun w => Tn [n, D, w]) (Finset.mem_range.2 (by omega))

/-- The time of an instance with a piece of `len ≤ q` vertices, `w ≤ cap` query pairs and `execs`
scans is at most the worst case for `q` and `cap` plus the time of the scans. -/
private theorem instance_le (Tn : List ℕ → ℕ) (n D execs : ℕ) {len q w cap : ℕ} (hlen : len ≤ q)
    (hw : w ≤ cap) :
    tWrites n D len + Tn [n, D, w] + tScanPairs w len execs
      ≤ tWrites n D q + supTime Tn n D cap + tAnswers cap + tScanCall q * execs := by
  have hwrites := tWrites_mono n D hlen
  have hsolver := le_supTime Tn n D hw
  have hanswers : tAnswers w ≤ tAnswers cap := by
    unfold tAnswers
    gcongr
  have hscans : tScanCall len * execs ≤ tScanCall q * execs := by
    unfold tScanCall tScan
    gcongr
  unfold tScanPairs
  omega

/-- A sum of `m ≤ M` terms `f t ≤ A + B e(t)` is at most `M A + B E` if the `e(t)` add up to at most
`E`. -/
private theorem sum_le_mul_add {m M A B E : ℕ} {f e : ℕ → ℕ} (hf : ∀ t < m, f t ≤ A + B * e t)
    (hm : m ≤ M) (he : ∑ t ∈ Finset.range m, e t ≤ E) :
    ∑ t ∈ Finset.range m, f t ≤ M * A + B * E :=
  calc ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
        Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ ≤ M * A + B * E := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

/-! ## The data of a run -/

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

/-- There are at most as many chunks as instances. -/
private theorem chunkCount_le_m {X : HostData} (hv : X.Valid) : X.chunkCount ≤ X.m := by
  have hn := hv.n_pos
  have hq := hv.q_pos
  have hpieces : 1 ≤ X.h := by
    rw [HostData.h, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]
    omega
  rw [HostData.m]
  exact Nat.le_mul_of_pos_left _ hpieces

/-- All scans but one fail, and there are at most `falsePositiveBound` failed scans. -/
private theorem sum_execs_le_falsePositiveBound (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) :
    ∑ t ∈ Finset.range (hostData x D g).m, (hostData x D g).execs t
      ≤ falsePositiveBound x.n x.U D + 1 :=
  (hostData x D g).sum_execs_le.trans (Nat.add_le_add_right
    ((HostData.sum_fails_le (hostData_valid hpre hbig)).trans
      (F_le_falsePositiveBound hpre hbig)) 1)

end HostTime

open HostTime

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

/-- The time of the loop over the instances is within its bound.  Both sides are a sum over the
instances plus the same constant; the piece of an instance has `min q (n - c₀)` vertices. -/
private theorem tHostLoop_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    tHostLoop Tn (hostData x D g) ≤ hostLoopBound Tn x.n x.U D g :=
  Nat.add_le_add_right (sum_le_mul_add
    (fun _ ht => instance_le Tn x.n D _ (Nat.min_le_left _ _) ((hostData x D g).w_le_cap ht))
    (hostData_m_le hbig) (sum_execs_le_falsePositiveBound hpre hbig)) 14

/-- **The time of a run after the choice of the prime is within the worst case.** -/
theorem hostRunTime_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    hostRunTime Tn (hostData x D g) x.U
      ≤ tDblTable (bitLen x.U) + 3 * tResidues (x.n * x.n) (bitLen x.U)
        + tClasses x.n (Nat.sqrt D) + tChunks (Nat.sqrt D) (4 * x.n * g)
        + hostLoopBound Tn x.n x.U D g + 80 := by
  have hprime : (hostData x D g).p ≤ Nat.sqrt D := hostData_p_le x g hbig.sixteen_le
  have hchunks : (hostData x D g).chunkCount ≤ 4 * x.n * g :=
    (chunkCount_le_m (hostData_valid hpre hbig)).trans (hostData_m_le hbig)
  have hloop := tHostLoop_le hpre hbig Tn
  have hn : (hostData x D g).n = x.n := rfl
  unfold hostRunTime
  rw [hn]
  unfold tClasses tChunks
  omega

end Light.Sec3

end
end

section


namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- A data-independent bound for the new loop, retaining the original `4ng`
coefficient of the oracle time. -/
noncomputable def allHostLoopBound (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
    (tWriteX n D (pieceSizeNat D g) + tWriteY n D (pieceSizeNat D g) +
      supTime Tn n D (queryCapNat n D) + 64 * queryCapNat n D + 113) +
    (tScan (pieceSizeNat D g) + 20) * (falsePositiveBound n U D + n * n) + 12

theorem all_instance_time_le (Tn : List ℕ → ℕ) (n D scans : ℕ) {len q w cap : ℕ}
    (hlen : len ≤ q) (hw : w ≤ cap) :
    tWriteX n D len + tWriteY n D len + Tn [n, D, w] +
        64 * w + (tScan len + 20) * scans + 113 ≤
      (tWriteX n D q + tWriteY n D q + supTime Tn n D cap + 64 * cap + 113) +
        (tScan q + 20) * scans := by
  have hx : tWriteX n D len ≤ tWriteX n D q := by unfold tWriteX; gcongr
  have hy : tWriteY n D len ≤ tWriteY n D q := by unfold tWriteY; gcongr
  have ht : Tn [n, D, w] ≤ supTime Tn n D cap :=
    Finset.le_sup (f := fun w => Tn [n, D, w]) (Finset.mem_range.2 (by omega))
  have ha := Nat.mul_le_mul_left 64 hw
  have hs : (tScan len + 20) * scans ≤ (tScan q + 20) * scans := by
    unfold tScan
    gcongr
  omega

theorem sum_times_le {m M A B E : ℕ} {f e : ℕ → ℕ}
    (hf : ∀ t < m, f t ≤ A + B * e t) (hm : m ≤ M)
    (he : ∑ t ∈ Finset.range m, e t ≤ E) :
    ∑ t ∈ Finset.range m, f t ≤ M * A + B * E := by
  calc
    ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
      Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.mul_sum]
    _ ≤ M * A + B * E :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

/-- Exact running-time sum for the new loop is bounded using the existing chosen
prime, with at most one additional successful scan per output pair. -/
theorem all_loop_time_le {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}
    (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    (∑ t ∈ Finset.range (hostData x D g).m,
      (tWriteX x.n D ((hostData x D g).len t) +
        tWriteY x.n D ((hostData x D g).len t) +
        Tn [x.n, D, (hostData x D g).w t] + 64 * (hostData x D g).w t +
        (tScan ((hostData x D g).len t) + 20) * instanceScans (hostData x D g) t + 113)) + 12 ≤
      allHostLoopBound Tn x.n x.U D g := by
  have hv := hostData_valid hpre hbig
  have he := (sum_instanceScans_le hv).trans
    (Nat.add_le_add_right (F_le_falsePositiveBound hpre hbig) (x.n * x.n))
  exact Nat.add_le_add_right (sum_times_le
    (fun _ ht => all_instance_time_le Tn x.n D _ (Nat.min_le_left _ _)
      ((hostData x D g).w_le_cap ht)) (hostData_m_le hbig) he) 12

end APSPImprovement.AllEdges



end

section


namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

theorem supTime_zero_all (n D cap : ℕ) : supTime (fun _ => 0) n D cap = 0 :=
  Finset.sup_const ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ 0

theorem loopBound_zero_steps :
    Steps (fun θ => allHostLoopBound (fun _ => 0) θ.n θ.U θ.D θ.g) allRestBound := by
  have h := ((Steps.toAllRest instance_setup_within_budget).add reading_answers_steps).add
    (Steps.toAllRest all_scans_within_budget)
  have hconst : Steps (fun _ => 12) allRestBound :=
    Steps.toAllRest ((Scale.SoftO.const 12).withinBuild)
  convert h.add hconst using 1
  funext θ
  simp only [allHostLoopBound, supTime_zero_all, Nat.add_zero]
  ring

theorem allHostLoopBound_eq (Tn : List ℕ → ℕ) (n U D g : ℕ) :
    allHostLoopBound Tn n U D g =
      4 * n * g * supTime Tn n D (queryCapNat n D) +
        allHostLoopBound (fun _ => 0) n U D g := by
  simp only [allHostLoopBound, supTime_zero_all, Nat.add_zero]
  ring

/-- Time for the new inner host with a conservative quadratic allowance. The old
host contributes only its zero-oracle cost; the new loop accounts for every oracle
call exactly once. -/
noncomputable def allHostTime (c : ℕ) (Dfun Gfun tD tG : ℕ → ℕ)
    (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostTime Dfun Gfun tD tG (fun _ => 0) n U +
    allHostLoopBound Tn n U (Dfun n) (Gfun (Dfun n)) + c * (n * n + 1) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then 150 * n ^ 3 + 150 else 0

theorem rest_with_quadratic_steps (c : ℕ) :
    Steps (fun θ => allHostLoopBound (fun _ => 0) θ.n θ.U θ.D θ.g +
      c * (θ.n * θ.n + 1)) allRestBound := by
  have hquad : Steps (fun θ => c * (θ.n * θ.n + 1)) budget := by
    have h : StepsMon (fun θ => c * (θ.n * θ.n + 1)) 2 0 0 := by first
                                                                    |
                                                                      ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                        (·
                                                                            repeat'
                                                                              with_reducible
                                                                                first
                                                                                | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                | apply steps_n
                                                                                | apply ThreeSumApsp.Scale.SoftO.add
                                                                                | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                | apply ThreeSumApsp.Scale.SoftO.max
                                                                                | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                | apply ThreeSumApsp.Scale.SoftO.div);
                                                                        (·
                                                                            first
                                                                            | decide
                                                                            | exact isEmptyElim))
                                                                    |
                                                                      ((fail_if_success
                                                                            (fail_if_success
                                                                                ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                                  (on_goal 1 =>
                                                                                      ((repeat'
                                                                                            with_reducible
                                                                                              first
                                                                                              | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                              | apply steps_n
                                                                                              | apply ThreeSumApsp.Scale.SoftO.add
                                                                                              | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                              | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                              | apply ThreeSumApsp.Scale.SoftO.max
                                                                                              | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                              | apply ThreeSumApsp.Scale.SoftO.div);
                                                                                        (done))))));
                                                                        (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                                                                        (all_goals
                                                                            try
                                                                              ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                                (·
                                                                                    repeat'
                                                                                      with_reducible
                                                                                        first
                                                                                        | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                        | apply steps_n
                                                                                        | apply ThreeSumApsp.Scale.SoftO.add
                                                                                        | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                        | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                        | apply ThreeSumApsp.Scale.SoftO.max
                                                                                        | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                        | apply ThreeSumApsp.Scale.SoftO.div);
                                                                                (· decide))))
                                                                    |
                                                                      ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                        (·
                                                                            repeat'
                                                                              with_reducible
                                                                                first
                                                                                | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                | apply steps_n
                                                                                | apply ThreeSumApsp.Scale.SoftO.add
                                                                                | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                | apply ThreeSumApsp.Scale.SoftO.max
                                                                                | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                | apply ThreeSumApsp.Scale.SoftO.div))
    exact h.withinScans
  exact loopBound_zero_steps.add (Steps.toAllRest hquad)

theorem solver_sup_time_le {Tn : List ℕ → ℕ} {T : ℕ → ℕ → ℕ → ℝ}
    (hT : ∀ n D w w' : ℕ, 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w')
    {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D) (cap : ℕ) :
    (supTime Tn n D cap : ℝ) ≤ T n D cap := by
  obtain ⟨w, hw, hsup⟩ : ∃ w ∈ Finset.range (cap + 1),
      (Finset.range (cap + 1)).sup (fun w => Tn [n, D, w]) = Tn [n, D, w] :=
    Finset.exists_mem_eq_sup _ ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ _
  rw [supTime, hsup]
  exact hT n D w cap hn hD (Nat.lt_succ_iff.1 (Finset.mem_range.1 hw))

/-- The all-edges host satisfies the same Theorem 17 bound, including the exact
`4ng` coefficient of the oracle time. -/
theorem obeysBound17_allHostTime (c : ℕ) (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ}
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hD : Steps (fun θ => tD θ.n) budget) (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17 strassen D g (allHostTime c Dfun Gfun tD tG) := by
  obtain ⟨C₀, hC₀, hold⟩ := obeysBound17_hostTime D g hDf hGf hD hG
  obtain ⟨C₁, hC₁, hrest⟩ := rest_with_quadratic_steps c
  refine ⟨C₀ + C₁, by positivity, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  have hθ : CostParams.Hyp ⟨n, D n, g n, U, κ⟩ := ⟨h16, hDn, hg1, hg, hκ, hU⟩
  have hn := hθ.one_le_n_nat
  have hDn1 := hθ.one_le_D_nat
  have hbase := hold (fun _ => 0) (fun _ _ _ => 0) (by intros; norm_num)
    n U κ h16 hDn hg1 hg hκ hU
  have hcost := hrest ⟨n, D n, g n, U, κ⟩ hθ
  have hsolver := solver_sup_time_le hT hn hDn1 (queryCapNat n (D n))
  rw [queryCapNat_eq n hDn1] at hsolver
  have hnonneg : 0 ≤ C₁ * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))) := by positivity
  have hgood : ¬ SmallCase n (D n) (g n) := by
    have hgNat : g n ≤ Nat.sqrt (D n) := by
      rw [Nat.le_sqrt']
      exact_mod_cast (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).1 hg
    unfold SmallCase
    omega
  unfold allHostTime
  rw [hDf n, hGf n hn, if_neg hgood, Nat.add_zero, allHostLoopBound_eq, queryCapNat_eq n hDn1]
  push_cast
  simp only [allRestBound, budget] at hcost
  push_cast at hcost
  unfold bound17 at hbase ⊢
  have hsolver' := mul_le_mul_of_nonneg_left hsolver
    (show 0 ≤ 4 * (n : ℝ) * g n by positivity)
  nlinarith

end APSPImprovement.AllEdges



end

section


namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- The original five matrix arguments are retained. The output pointer is
stored immediately below the workspace, and its flag vector is initialized. -/
noncomputable def preparedAllEdgesTask : Task where
  Inst := AllEdgesInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre x μ fr := x.Pre μ fr ∧ FlagTable μ x.out (x.n * x.n) ∅ ∧
    0 < fr ∧ μ (fr - 1) = x.out
  Post := allEdgesTask.Post

namespace Adapter

def body (pInner pFill : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pFill [v 5, (Light.Expr.op Light.Op.mul) (v 0) (v 0), k 0] 7)
    (Light.Stmt.seq (.store (v 6) (v 5))
      (.call pInner
        [v 0, v 1, v 2, v 3, v 4, (Light.Expr.op Light.Op.add) (v 6) (k 1)] 7)))

def time (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := 20 * n * n + 100 + T n U

def need (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := (r n U).word + 1
  cells := 1 + (r n U).cells
  depth := (r n U).depth + 1

theorem prepared_pre {x : AllEdgesInst} {fr : ℕ} {μ μ' : ℕ → ℤ}
    (hpre : x.Pre μ fr) (hzero : Seg μ' x.out (List.replicate (x.n * x.n) (0 : ℤ)))
    (hkeep : SameOutside μ μ' x.out (x.n * x.n)) :
    preparedAllEdgesTask.Pre x (Function.update μ' fr (x.out : ℤ)) (fr + 1) := by
  ((obtain ⟨⟩ := id hpre.toPre); (obtain ⟨⟩ := id hpre))
  have hk : KeptBut μ (Function.update μ' fr (x.out : ℤ)) fr x.out (x.n * x.n) := by
    intro a ⟨ha, hout⟩
    rw [Function.update_of_ne (by omega : a ≠ fr)]
    exact hkeep a hout
  have hp := hpre.keep hk
  refine ⟨{ hp with
    belowAB := by omega
    belowBC := by omega
    belowAC := by omega
    belowOut := by omega }, ?_, by omega, ?_⟩
  · intro q hq
    rw [Function.update_of_ne (by omega : x.out + q ≠ fr)]
    have hq' : q < (List.replicate (x.n * x.n) (0 : ℤ)).length := by simpa using hq
    have hz := hzero.getD hq' 0
    simpa [bit] using hz
  · simp

theorem spec {P R : Program} {pInner pFill : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} {lim : Limits} {d : ℕ} {x : AllEdgesInst}
    {μ : ℕ → ℤ} {fr : ℕ}
    (hsol : Solves preparedAllEdgesTask P pInner T r)
    (hFill : (P ++ R)[pFill]? = some fillBody)
    (hpre : x.Pre μ fr) (hok : (need r x.n x.U).Ok lim fr d) :
    Ends lim (P ++ R) d (body pInner pFill)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩ (time T x.n x.U)
      fun σ' => allEdgesTask.Post x μ fr (σ'.loc 7) σ'.mem := by
  ((obtain ⟨⟩ := id hpre.toPre); (obtain ⟨⟩ := id hpre))
  have hw := hok.word
  have hs := hok.cells
  have hd := hok.depth
  have hspace := hok.space
  dsimp [need] at hw hs hd
  unfold body time
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((fill_meets hFill hok.space
                (by omega : x.out + x.n * x.n ≤ lim.space) (x := 0))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (fill_meets hFill hok.space (by omega : x.out + x.n * x.n ≤ lim.space)
              (x := 0))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro a μ₁ ⟨hzero, hkeep⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen fr (x.out : ℤ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((hsol.meets R x (fr + 1) (prepared_pre hpre hzero hkeep)
                { word := by
                    simpa [preparedAllEdgesTask] using
                      (show ((r x.n x.U).word : ℤ) ≤ lim.word by omega)
                  cells := by (dsimp [preparedAllEdgesTask]); (omega)
                  space := hok.space
                  depth := by (dsimp [preparedAllEdgesTask]); (omega) })
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (hsol.meets R x (fr + 1) (prepared_pre hpre hzero hkeep)
              { word := by
                  simpa [preparedAllEdgesTask] using
                    (show ((r x.n x.U).word : ℤ) ≤ lim.word by omega)
                cells := by (dsimp [preparedAllEdgesTask]); (omega)
                space := hok.space
                depth := by (dsimp [preparedAllEdgesTask]); (omega) })
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                preparedAllEdgesTask]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [preparedAllEdgesTask] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, preparedAllEdgesTask] <;>
              omega)));
    (on_goal -1 =>
        ((rintro b μ₂ ⟨hflags, hkept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hflags, ?_⟩
  intro c ⟨hc, hout⟩
  exact (hkept c ⟨by omega, hout⟩).trans
    ((Function.update_of_ne (by omega : c ≠ fr) _ _).trans (hkeep c hout))

end Adapter

theorem polyNeed_adapter {r : ℕ → ℕ → Need} (h : PolyNeed r) :
    PolyNeed (Adapter.need r) := by
  unfold Adapter.need
  (refine Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
      first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply h.word
                  | apply h.cells
                  | apply h.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply h.word
                                | apply h.cells
                                | apply h.depth
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply h.word
                          | apply h.cells
                          | apply h.depth
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply h.word
                  | apply h.cells
                  | apply h.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)))

/-- Zero-initialize the output vector, save its address, and call the prepared
inner solver. Only quadratic work and one workspace cell are added. -/
theorem isHost_prepareAllEdges :
    IsHost preparedAllEdgesTask allEdgesTask Adapter.time Adapter.need := by
  refine ⟨fun P p T r hsol =>
    ⟨[fillBody, Adapter.body p P.length], P.length + 1, Adapter.body p P.length, by simp,
      fun R lim d x μ fr hpre hok => ?_⟩, fun r => polyNeed_adapter⟩
  rw [List.append_assoc]
  exact Adapter.spec hsol (by simp) hpre hok

end APSPImprovement.AllEdges



end

section


namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

theorem solves_larger_time {task : Task} {P : Program} {p : ℕ}
    {T T' : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (h : Solves task P p T r) (ht : ∀ n U, T n U ≤ T' n U) : Solves task P p T' r := by
  obtain ⟨body, hp, hs⟩ := h
  exact ⟨body, hp, fun R lim d x μ fr hpre hok =>
    (hs R lim d x μ fr hpre hok).mono (ht _ _) (fun _ h => h)⟩

/-- The verified initialization adapter's quadratic work is absorbed by increasing
the conservative quadratic allowance of the inner host. -/
theorem adapter_time_le (c : ℕ) (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) :
    Adapter.time (allHostTime c Dfun Gfun tD tG Tn) n U ≤
      allHostTime (c + 100) Dfun Gfun tD tG Tn n U := by
  unfold Adapter.time allHostTime
  nlinarith

/-- Turn an actual prepared inner solver into the all-edges solver with initialized
output memory. Procedure append order and the polynomial resource bounds are retained. -/
theorem full_host_of_prepared (c : ℕ) (Dfun Gfun tD tG : ℕ → ℕ)
    (need : (List ℕ → Need) → ℕ → ℕ → Need)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves preparedAllEdgesTask (Q ++ R) p'
        (allHostTime c Dfun Gfun tD tG Tn) (need r) ∧ PolyNeed (need r)) :
    ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves allEdgesTask (Q ++ R) p'
        (allHostTime (c + 100) Dfun Gfun tD tG Tn) (Adapter.need (need r)) ∧
        PolyNeed (Adapter.need (need r)) := by
  intro Q pS Tn r hr hs
  obtain ⟨R, p', hinner, hneed⟩ := host Q pS Tn r hr hs
  obtain ⟨S, p'', hfull⟩ := isHost_prepareAllEdges.1 _ _ _ _ hinner
  refine ⟨R ++ S, p'', ?_, isHost_prepareAllEdges.2 _ hneed⟩
  rw [← List.append_assoc]
  exact solves_larger_time hfull (adapter_time_le c Dfun Gfun tD tG Tn)

/-- The original claim-from-host proof, now for the all-edges output task. -/
theorem claim17_of_allEdges_host (MM : ℕ → ℝ) (D g : ℕ → ℕ)
    (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ)
    (need : (List ℕ → Need) → ℕ → ℕ → Need)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves allEdgesTask (Q ++ R) p' (time Tn) (need r) ∧ PolyNeed (need r))
    (bound : ObeysBound17 MM D g time) : Claim.Theorem_17 allEdgesModel MM D g := by
  obtain ⟨C, hC, bound⟩ := bound
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs, hp⟩ := host Q pS Tn r hpoly hsolves
  exact ⟨timeUpTo (time Tn), hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

end APSPImprovement.AllEdges




end

section


/-!
# The host of Theorem 17: the need stays polynomial

The need of a procedure says what it asks of the limits of a run: the largest number that it forms,
the cells that it uses, and the depth of its calls.  If the need of the solver is polynomially
bounded (`PolyNeedN`), then so is the need of the host (`hostNeed_poly`: `PolyNeed` of `hostNeed`).
The need of the host is an explicit expression in `n`, `U`, `D`, `g` and a few quantities derived
from them.  Each of these is at most a polynomial in `(n + 1)(U + 1)` (`PolyBounded`), and such
bounds are closed under sums, products and powers.

* The quantities: `⌊√D⌋ ≤ D`, the number of binary digits of `U` is at most `U`,
  `2^{len + 1} ≤ 4(U + 1)`, `2^⌈log₂ n⌉ ≤ 2(n + 1)`, `⌊n²/√D⌋ ≤ n²`, `⌈s/g⌉ ≤ s + g` with
  `s = ⌊√D⌋`.
* The numbers (`polyBounded_hostWord`), the cells (`polyBounded_chooseCells`,
  `polyBounded_hostLayout`), and each of the three parts of the need of the solver on the instances
  of the host (`polyBounded_sup`).  The depth adds `O(⌈log₂ n⌉)` calls (`polyBounded_clog`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostPoly

/-! ## The quantities -/

/-- `⌊n²/√D⌋ ≤ n²`. -/
private theorem queryCapNat_le_sq (n D : ℕ) : queryCapNat n D ≤ n ^ 2 := by
  unfold queryCapNat
  calc Nat.sqrt (n ^ 4 / D) ≤ Nat.sqrt (n ^ 4) := Nat.sqrt_le_sqrt (Nat.div_le_self _ _)
    _ = Nat.sqrt (n ^ 2 * n ^ 2) := by rw [← pow_add]
    _ = n ^ 2 := Nat.sqrt_eq _

/-- `2^{len + 1} ≤ 4(U + 1)` for the number `len` of binary digits of `U`. -/
private theorem two_pow_bitLen_le (U : ℕ) : 2 ^ (bitLen U + 1) ≤ 4 * (U + 1) := by
  rcases Nat.eq_zero_or_pos U with rfl | hU
  · simp [bitLen]
  · have hlen : 0 < bitLen U := Nat.size_pos.2 hU
    obtain ⟨b, hb⟩ : ∃ b, bitLen U = b + 1 := ⟨bitLen U - 1, by omega⟩
    have hpow : 2 ^ b ≤ U := Nat.lt_size.1 (by unfold bitLen at hb; omega)
    rw [hb, pow_succ, pow_succ]
    omega

/-- `2^⌈log₂ n⌉ ≤ 2(n + 1)`. -/
private theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Nat.pow_clog_le_mul Nat.one_lt_two hn
    omega

/-- The number of binary digits of `U` is at most `U`. -/
private theorem polyBounded_bitLen : PolyBounded fun _ U => bitLen U :=
  PolyBounded.snd.of_le fun _ _ => Nat.size_le.2 Nat.lt_two_pow_self

/-- `2^{len + 1} ≤ 4(U + 1)` is polynomially bounded. -/
private theorem polyBounded_two_pow_bitLen : PolyBounded fun _ U => 2 ^ (bitLen U + 1) := by
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le two_pow_bitLen_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply Scale.SoftO.of_forall_le two_pow_bitLen_le
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply Scale.SoftO.of_forall_le two_pow_bitLen_le
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le two_pow_bitLen_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The size of the matrices of Strassen's recursion. -/
private theorem polyBounded_two_pow_clog : PolyBounded fun n _ => 2 ^ Nat.clog 2 n := by
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le two_pow_clog_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply Scale.SoftO.of_forall_le two_pow_clog_le
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply Scale.SoftO.of_forall_le two_pow_clog_le
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le two_pow_clog_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The depth of Strassen's recursion. -/
private theorem polyBounded_clog : PolyBounded fun n _ => Nat.clog 2 n :=
  polyBounded_two_pow_clog.of_le fun _ _ => Nat.lt_two_pow_self.le

/-- `(2^c)^⌈log₂ n⌉ = (2^⌈log₂ n⌉)^c`. -/
private theorem polyBounded_pow_clog (c : ℕ) : PolyBounded fun n _ => (2 ^ c) ^ Nat.clog 2 n :=
  (by first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply polyBounded_two_pow_clog
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply polyBounded_two_pow_clog
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply polyBounded_two_pow_clog
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply polyBounded_two_pow_clog
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)) :
    PolyBounded fun n _ => (2 ^ Nat.clog 2 n) ^ c).of_le fun n _ => by
      rw [← pow_mul, ← pow_mul, mul_comm]

variable {D g : ℕ → ℕ}

/-- The number of query pairs of an instance. -/
private theorem polyBounded_queryCapNat : PolyBounded fun n _ => queryCapNat n (D n) := by
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le₂ queryCapNat_le_sq
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply Scale.SoftO.of_forall_le₂ queryCapNat_le_sq
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply Scale.SoftO.of_forall_le₂ queryCapNat_le_sq
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le₂ queryCapNat_le_sq
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-! ## The numbers, the cells, and the solver -/

section parts

variable (hD : PolyBounded fun n _ => D n)
include hD

/-- The numbers that the host forms. -/
private theorem polyBounded_hostWord {a b : ℕ → ℕ} (ha : PolyBounded fun n _ => a n)
    (hb : PolyBounded fun n _ => b n) (hg : PolyBounded fun n _ => g n) :
    PolyBounded fun n U => hostWord (a n) (b n) n U (D n) (g n) := by
  have hring : PolyBounded fun n _ => 16 ^ Nat.clog 2 n := polyBounded_pow_clog 4
  unfold hostWord pieceSizeNat
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply ha
              | apply hb
              | apply hD
              | apply hg
              | apply polyBounded_two_pow_bitLen
              | apply hring
              | apply Scale.SoftO.ceilDiv
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply ha
                            | apply hb
                            | apply hD
                            | apply hg
                            | apply polyBounded_two_pow_bitLen
                            | apply hring
                            | apply Scale.SoftO.ceilDiv
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply ha
                      | apply hb
                      | apply hD
                      | apply hg
                      | apply polyBounded_two_pow_bitLen
                      | apply hring
                      | apply Scale.SoftO.ceilDiv
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply ha
              | apply hb
              | apply hD
              | apply hg
              | apply polyBounded_two_pow_bitLen
              | apply hring
              | apply Scale.SoftO.ceilDiv
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The cells of the arrays of the host. -/
private theorem polyBounded_hostLayout : PolyBounded fun n U => hostLayout n U (D n) := by
  unfold hostLayout
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply hD
              | apply polyBounded_bitLen
              | apply polyBounded_queryCapNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply hD
                            | apply polyBounded_bitLen
                            | apply polyBounded_queryCapNat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply hD
                      | apply polyBounded_bitLen
                      | apply polyBounded_queryCapNat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply hD
              | apply polyBounded_bitLen
              | apply polyBounded_queryCapNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The cells for the choice of the prime.  The scratch space of Strassen's recursion is at most
the size `4^K s` of a matrix, with `K = ⌈log₂ n⌉` and `s = ⌊√D⌋`. -/
private theorem polyBounded_chooseCells : PolyBounded fun n U => chooseCells n U (D n) := by
  have hmatrix : PolyBounded fun n _ => 4 ^ Nat.clog 2 n := polyBounded_pow_clog 2
  unfold chooseCells countCells
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply hD
              | apply polyBounded_bitLen
              | apply polyBounded_two_pow_clog
              | apply polyBounded_clog
              | apply hmatrix
              | apply Scale.SoftO.of_forall_le₂ strScr_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply hD
                            | apply polyBounded_bitLen
                            | apply polyBounded_two_pow_clog
                            | apply polyBounded_clog
                            | apply hmatrix
                            | apply Scale.SoftO.of_forall_le₂ strScr_le
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply hD
                      | apply polyBounded_bitLen
                      | apply polyBounded_two_pow_clog
                      | apply polyBounded_clog
                      | apply hmatrix
                      | apply Scale.SoftO.of_forall_le₂ strScr_le
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply hD
              | apply polyBounded_bitLen
              | apply polyBounded_two_pow_clog
              | apply polyBounded_clog
              | apply hmatrix
              | apply Scale.SoftO.of_forall_le₂ strScr_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- A polynomially bounded function of the parameters `n`, `D`, `w` of an instance, at its largest
over the instances of the host, which have at most `⌊n²/√D⌋` query pairs. -/
private theorem polyBounded_sup {f : List ℕ → ℕ} {s k : ℕ} (hf : ∀ ps, f ps ≤ polyBound s k ps) :
    PolyBounded fun n _ => (Finset.range (queryCapNat n (D n) + 1)).sup fun w => f [n, D n, w] := by
  have hbound :
      PolyBounded fun n _ => 2 ^ s * ((n + 1) * ((D n + 1) * (queryCapNat n (D n) + 1))) ^ k := by
    first
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply Light.PolyBounded.fst
                | apply Light.PolyBounded.snd
                | apply ThreeSumApsp.Scale.SoftO.log
                | apply ThreeSumApsp.Scale.SoftO.sqrt
                | apply hD
                | apply polyBounded_queryCapNat
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div);
        (·
            first
            | decide
            | exact isEmptyElim))
    |
      ((fail_if_success
            (fail_if_success
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (on_goal 1 =>
                      ((repeat'
                            with_reducible
                              first
                              | exact ThreeSumApsp.Scale.SoftO.const _
                              | apply Light.PolyBounded.fst
                              | apply Light.PolyBounded.snd
                              | apply ThreeSumApsp.Scale.SoftO.log
                              | apply ThreeSumApsp.Scale.SoftO.sqrt
                              | apply hD
                              | apply polyBounded_queryCapNat
                              | apply ThreeSumApsp.Scale.SoftO.add
                              | apply ThreeSumApsp.Scale.SoftO.mul
                              | apply ThreeSumApsp.Scale.SoftO.pow
                              | apply ThreeSumApsp.Scale.SoftO.max
                              | apply ThreeSumApsp.Scale.SoftO.sub
                              | apply ThreeSumApsp.Scale.SoftO.div);
                        (done))))));
        (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
        (all_goals
            try
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (·
                    repeat'
                      with_reducible
                        first
                        | exact ThreeSumApsp.Scale.SoftO.const _
                        | apply Light.PolyBounded.fst
                        | apply Light.PolyBounded.snd
                        | apply ThreeSumApsp.Scale.SoftO.log
                        | apply ThreeSumApsp.Scale.SoftO.sqrt
                        | apply hD
                        | apply polyBounded_queryCapNat
                        | apply ThreeSumApsp.Scale.SoftO.add
                        | apply ThreeSumApsp.Scale.SoftO.mul
                        | apply ThreeSumApsp.Scale.SoftO.pow
                        | apply ThreeSumApsp.Scale.SoftO.max
                        | apply ThreeSumApsp.Scale.SoftO.sub
                        | apply ThreeSumApsp.Scale.SoftO.div);
                (· decide))))
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply Light.PolyBounded.fst
                | apply Light.PolyBounded.snd
                | apply ThreeSumApsp.Scale.SoftO.log
                | apply ThreeSumApsp.Scale.SoftO.sqrt
                | apply hD
                | apply polyBounded_queryCapNat
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div))
  refine hbound.of_le fun n _ => Finset.sup_le fun w hw => (hf _).trans ?_
  have hw' : w ≤ queryCapNat n (D n) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hw)
  simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  gcongr

end parts

end HostPoly

open HostPoly in
/-- **The need of the host stays polynomial**, if the parameters, the numbers that the parameter
procedures form, and the need of the solver are polynomially bounded. -/
theorem hostNeed_poly {Dfun Gfun wD wG : ℕ → ℕ} {need : List ℕ → Need}
    (hD : PolyBounded fun n _ => Dfun n) (hG : PolyBounded fun n _ => Gfun (Dfun n))
    (hwD : PolyBounded fun n _ => wD n) (hwG : PolyBounded fun n _ => wG (Dfun n))
    (h : PolyNeedN need) :
    PolyNeed (hostNeed Dfun Gfun wD wG need) := by
  obtain ⟨s, k, hle⟩ := h
  unfold hostNeed hostNeedAt supNeed
  (refine Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
      first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply polyBounded_hostWord hD hwD hwG hG
                  | apply polyBounded_chooseCells hD
                  | apply polyBounded_hostLayout hD
                  | apply polyBounded_clog
                  | apply polyBounded_sup hD fun ps => (hle ps).1
                  | apply polyBounded_sup hD fun ps => (hle ps).2.1
                  | apply polyBounded_sup hD fun ps => (hle ps).2.2
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply polyBounded_hostWord hD hwD hwG hG
                                | apply polyBounded_chooseCells hD
                                | apply polyBounded_hostLayout hD
                                | apply polyBounded_clog
                                | apply polyBounded_sup hD fun ps => (hle ps).1
                                | apply polyBounded_sup hD fun ps => (hle ps).2.1
                                | apply polyBounded_sup hD fun ps => (hle ps).2.2
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply polyBounded_hostWord hD hwD hwG hG
                          | apply polyBounded_chooseCells hD
                          | apply polyBounded_hostLayout hD
                          | apply polyBounded_clog
                          | apply polyBounded_sup hD fun ps => (hle ps).1
                          | apply polyBounded_sup hD fun ps => (hle ps).2.1
                          | apply polyBounded_sup hD fun ps => (hle ps).2.2
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply polyBounded_hostWord hD hwD hwG hG
                  | apply polyBounded_chooseCells hD
                  | apply polyBounded_hostLayout hD
                  | apply polyBounded_clog
                  | apply polyBounded_sup hD fun ps => (hle ps).1
                  | apply polyBounded_sup hD fun ps => (hle ps).2.1
                  | apply polyBounded_sup hD fun ps => (hle ps).2.2
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)))

end Light.Sec3

end
end

section


/-!
# Pure facts about the starts of the classes and the table of chunks

Proof of Theorem 17.  The `n²` pairs `(a, b)` are listed class after class, where the class
of a residue `ϱ < p` holds the pairs whose weight is congruent to `ϱ` modulo the prime `p`, and each
class is cut into chunks of at most `cap` pairs.  The list of the starts of the classes has `p + 1`
entries, none above `n²`; the table of chunks has at most `n² + p` entries.
-/

public section

namespace ThreeSumApsp.Spec

/-- The list of the starts of the classes has one entry for each residue, and one more for the
end. -/
theorem length_classStarts (n p : ℕ) (RAB : List ℕ) : (classStarts n p RAB).length = p + 1 := by
  simp [classStarts]

/-- A class starts at a place of the list of all n² pairs, or at its end. -/
theorem classStart_le_sq (n : ℕ) (RAB : List ℕ) (rho : ℕ) : classStart n RAB rho ≤ n * n := by
  rw [classStart_eq_length_filter]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- No entry of the list of the starts of the classes is above n². -/
theorem le_of_mem_classStarts {n p : ℕ} {RAB : List ℕ} {x : ℕ} (hx : x ∈ classStarts n p RAB) :
    x ≤ n * n := by
  obtain ⟨rho, -, rfl⟩ := List.mem_map.1 hx
  exact classStart_le_sq n RAB rho

/-- If `cap ≥ 1` and every residue is below `p`, the table of chunks has at most `n² + p` entries.
This is the number of cells that the host procedure of Theorem 17 reserves for each of its three
components. -/
theorem length_chunkTab_le_add {n p cap : ℕ} {RAB : List ℕ} (hcap : 1 ≤ cap)
    (hlt : ∀ i < n * n, RAB.getD i 0 < p) : (chunkTab n p cap RAB).length ≤ n * n + p := by
  have hlen := length_chunkTab_le hcap hlt
  have hdiv := Nat.div_le_self (n * n) cap
  omega

end ThreeSumApsp.Spec

end
end

section


/-!
# The host of Theorem 17: the arrays and the loop

The third part of the host procedure `et17` (Exact Triangle by Theorem 17) fills the table of
doubles and the three lists of residues (`resid_then`), sorts the pairs into classes and cuts the
classes into chunks (`classes_then`), and calls the loop over the instances.

`et17Tables_spec` is the specification of the whole part: within `hostRunTime` steps, local 0 holds
the bit `found m` of the loop over the instances, and the cells below the free pointer are
unchanged.  Three lemmas connect the calls to the loop: `ready_of` (a run of et17 provides what this
part needs), `hostMem_of` (the arrays that the loop reads are in the memory) and `hostLay_of` (they
lie where the loop expects them).
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec3

open ThreeSumApsp

namespace Et17

/-- A call that puts its result into the local Small. -/
theorem setLocal_res (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res r : ℤ) :
    setLocal (locals x X fr g s nch res) Small r = locals x X fr g s nch r := rfl























variable {lim : Limits} {P : Program} {d : ℕ} {x : TriInst} {X : HostData} {μ : ℕ → ℤ} {fr : ℕ}

/-- The places of the lists of residues: they stand one after the other behind the table of doubles,
and end where the array of the classes begins, below the free pointer of the solver. -/
private theorem resid_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCls X U fr ≤ aFr X U fr := by
  have := host_places X U fr
  omega

/-- The places of the arrays of the classes and the chunks: they stand one after the other behind
the lists of residues, and end at aX, the first matrix of the instance that is handed to the solver,
below the free pointer of the solver. -/
private theorem class_places (X : HostData) (U fr : ℕ) :
    aRbc X U fr = aRab X U fr + X.n * X.n ∧ aRac X U fr = aRbc X U fr + X.n * X.n ∧
      aCls X U fr = aRac X U fr + X.n * X.n ∧ aCur X U fr = aCls X U fr + (X.p + 1) ∧
      aQi X U fr = aCur X U fr + X.p ∧ aQj X U fr = aQi X U fr + X.n * X.n ∧
      aCr X U fr = aQj X U fr + X.n * X.n ∧ aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧
      aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧ aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧
      aX X U fr ≤ aFr X U fr := by
  have := host_places X U fr
  omega




















/-- What residues needs, for a matrix below the free pointer and a destination between the table of
doubles and the end of the arrays. -/
theorem Ready.residuesPre (h : Ready lim d x X μ fr) {μ' : ℕ → ℤ} {src dst : ℕ} {l : List ℤ}
    (hdbl : Seg μ' fr (dblList X.p (bitLen x.U))) (hsrc : Seg μ' src l)
    (hlen : l.length = X.n * X.n) (hle : AbsLe l x.U) (hbelow : src + X.n * X.n ≤ fr)
    (hlow : fr + (bitLen x.U + 1) ≤ dst := by omega)
    (hhigh : dst + X.n * X.n < lim.space := by omega) :
    ResiduesPre lim μ' src dst (X.n * X.n) fr X.p (bitLen x.U) x.U l :=
  { hw := h.space
    prime := h.prime
    segDbl := hdbl
    segSrc := hsrc
    length := hlen
    le := hle
    lt := Nat.lt_size_self _
    spaceDbl := by omega
    spaceSrc := by omega
    spaceDst := by omega
    count := by omega
    apartSrc := by omega
    apartDbl := by omega
    word := h.word }

/-- **The table of doubles and the three lists of residues**, followed by the rest t of the text. -/
theorem resid_then {pDbl pResid pResidues : ℕ} (hDbl : P[pDbl]? = some dblTableBody)
    (hResid : P[pResid]? = some residBody) (hResidues : P[pResidues]? = some (residuesBody pResid))
    (hr : Ready lim d x X μ fr) {g s : ℤ} {t : Stmt} {T : ℕ} {Q : State → Prop}
    (h : ∀ res μ', ResidMem x X fr μ μ' → Ends lim P d t ⟨frame (locals x X fr g s 0 res), μ'⟩
      (T - (tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26)) Q)
    (hT : tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26 ≤ T) :
    Ends lim P d
      ((Light.Stmt.seq (.call pDbl [v Free, v ThePrime, v Bits] Small)
         (Light.Stmt.seq
           (.call pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small)
           (Light.Stmt.seq
             (.call pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small)
             (Light.Stmt.seq
               (.call pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small)
               t)))))
      ⟨frame (locals x X fr g s 0 0), μ⟩ T Q := by
  have hdepth := hr.depth
  have htop := hr.top
  have hplaces := resid_places X x.U fr
  have lenAB := hr.lenAB
  have lenBC := hr.lenBC
  have lenAC := hr.lenAC
  have hAB := hr.belowAB
  have hBC := hr.belowBC
  have hAC := hr.belowAC
  have hword : ((X.p * 2 ^ bitLen x.U : ℕ) : ℤ) ≤ lim.word := le_trans (by
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)))
    hr.word
  have lenDbl : (dblList X.p (bitLen x.U)).length = bitLen x.U + 1 := by simp [dblList]
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have lenRBC : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  -- Small := pDbl(Free, ThePrime, Bits)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((dblTable_meets (dst := fr) (p := X.p) (len := bitLen x.U) hDbl
                hr.space (by omega) hword)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (dblTable_meets (dst := fr) (p := X.p) (len := bitLen x.U) hDbl
              hr.space (by omega) hword)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₁ μ₁ ⟨hdbl, same₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [setLocal_res]
  -- Small := pResidues(AdrAB, ResAB, SizeSq, Free, Bits)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((residues_meets hResidues hResid (by omega)
                (hr.residuesPre (dst := aRab X x.U fr) hdbl hr.segAB.keep hr.lenAB
                  hr.leAB hr.belowAB))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets hResidues hResid (by omega)
              (hr.residuesPre (dst := aRab X x.U fr) hdbl hr.segAB.keep hr.lenAB
                hr.leAB hr.belowAB))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₂ μ₂ ⟨hrab, same₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [setLocal_res]
  -- Small := pResidues(AdrBC, ResBC, SizeSq, Free, Bits)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((residues_meets hResidues hResid (by omega)
                (hr.residuesPre (dst := aRbc X x.U fr) hdbl.keep hr.segBC.keep
                  hr.lenBC hr.leBC hr.belowBC))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets hResidues hResid (by omega)
              (hr.residuesPre (dst := aRbc X x.U fr) hdbl.keep hr.segBC.keep
                hr.lenBC hr.leBC hr.belowBC))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₃ μ₃ ⟨hrbc, same₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [setLocal_res]
  -- Small := pResidues(AdrAC, ResAC, SizeSq, Free, Bits)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((residues_meets hResidues hResid (by omega)
                (hr.residuesPre (dst := aRac X x.U fr) hdbl.keep hr.segAC.keep
                  hr.lenAC hr.leAC hr.belowAC))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets hResidues hResid (by omega)
              (hr.residuesPre (dst := aRac X x.U fr) hdbl.keep hr.segAC.keep
                hr.lenAC hr.leAC hr.belowAC))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₄ μ₄ ⟨hrac, same₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [setLocal_res]
  exact (h r₄ μ₄ ⟨hrab.keep, hrbc.keep, hrac, by ((try refine Light.SameOn.cell ?_);
                                                          (intro apspMacro_576227_0 apspMacro_576227_1);
                                                          (first
                                                            |
                                                              ((((repeat
                                                                        (((with_reducible
                                                                                rename Light.SameOn _ _ _ => apspMacro_576227_2));
                                                                          ((try
                                                                                have :=
                                                                                  apspMacro_576227_2 apspMacro_576227_0 (by omega)));
                                                                          (revert apspMacro_576227_2)));
                                                                    (intros);
                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                (omega))
                                                            |
                                                              ((simp [] at apspMacro_576227_1);
                                                                (((repeat
                                                                        (((with_reducible
                                                                                rename Light.SameOn _ _ _ => apspMacro_576227_3));
                                                                          ((try
                                                                                have :=
                                                                                  apspMacro_576227_3 apspMacro_576227_0 (by omega)));
                                                                          (revert apspMacro_576227_3)));
                                                                    (intros);
                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                (omega))
                                                            |
                                                              ((((repeat
                                                                        (((with_reducible
                                                                                rename Light.SameOn _ _ _ => apspMacro_576227_4));
                                                                          ((try
                                                                                have :=
                                                                                  apspMacro_576227_4 apspMacro_576227_0 (by omega)));
                                                                          (revert apspMacro_576227_4)));
                                                                    (intros);
                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                (fail
                                                                    "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                              SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                              its condition K x does not follow from the hypotheses."))))⟩).mono (by simp; omega) fun _ hQ => hQ

/-- There are at most n² + p chunks. -/
theorem Ready.chunkCount_le (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap) :
    X.chunkCount ≤ X.n * X.n + X.p :=
  length_chunkTab_le_add hcap fun i hi => lt_of_mem_residList hr.prime (by
    rw [List.getD_eq_getElem _ _ (by rw [HostData.RAB, length_residList, hr.lenAB]; exact hi)]
    exact List.getElem_mem _)

/-- **The classes and the chunks**, followed by the rest t of the text. -/
theorem classes_then {pClasses pChunks : ℕ} (hClasses : P[pClasses]? = some classesBody)
    (hChunks : P[pChunks]? = some chunksBody) (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap)
    {μ₁ : ℕ → ℤ} (hrab : SegN μ₁ (aRab X x.U fr) X.RAB) {g s res : ℤ} {t : Stmt} {T : ℕ}
    {Q : State → Prop}
    (h : ∀ res' μ', ClassMem x X fr μ₁ μ' → Ends lim P d t
      ⟨frame (locals x X fr g s X.chunkCount res'), μ'⟩
      (T - (tClasses X.n X.p + tChunks X.p X.chunkCount + 17)) Q)
    (hT : tClasses X.n X.p + tChunks X.p X.chunkCount + 17 ≤ T) :
    Ends lim P d
      ((Light.Stmt.seq
         (.call pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols]
           Small)
         (Light.Stmt.seq
           (.call pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks)
           t)))
      ⟨frame (locals x X fr g s 0 res), μ₁⟩ T Q := by
  have hchunks : X.chunkCount = (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length := rfl
  rw [hchunks] at h hT
  have hdepth := hr.depth
  have hp := hr.prime
  have htop := hr.top
  have hplaces := class_places X x.U fr
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have ltRAB : ∀ r ∈ X.RAB, r < X.p := fun r hmem => lt_of_mem_residList (by omega) hmem
  have hroom : (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length ≤ X.n * X.n + X.p :=
    hr.chunkCount_le hcap
  -- Small := pClasses(ResAB, Size, ThePrime, Cls, Cur, Rows, Cols)
  refine Ends.callToThen (classes_meets hClasses hr.space
    { rab := aRab X x.U fr, n := X.n, p := X.p, cls := aCls X x.U fr, cur := aCur X x.U fr,
      qi := aQi X x.U fr, qj := aQj X x.U fr, RAB := X.RAB } μ₁
    { seg := hrab, len := lenRAB, lt := ltRAB }) ?_ (by simp)
  rintro r₁ μ₂ ⟨hcls, hqi, hqj, same₂⟩
  dsimp only at hcls hqi hqj same₂
  rw [setLocal_res]
  -- NumChunks := pChunks(Cls, ThePrime, Cap, TabR, TabL, TabW)
  refine Ends.callToThen (chunks_meets hChunks hr.space
    { cls := aCls X x.U fr, p := X.p, cap := X.cap, cr := aCr X x.U fr, cl := aCl X x.U fr,
      cw := aCw X x.U fr, R := X.n * X.n + X.p, B := X.n * X.n, C := classStarts X.n X.p X.RAB } μ₂
    { seg := hcls, len := length_classStarts X.n X.p X.RAB,
      le := fun y hy => le_of_mem_classStarts hy, room := hroom }) ?_ (by simp)
    (hT := by simp only [ChunksArgs.table]; first
                                            |
                                              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                (first
                                                  | omega
                                                  | ((ring_nf); (omega))))
                                            | omega
                                            |
                                              (simp [] <;>
                                                  first
                                                  | omega
                                                  | ((ring_nf); (omega))))
  rintro _ μ₃ ⟨rfl, hcr, hcl, hcw, same₃⟩
  simp only [ChunksArgs.table, ChunksArgs.Same] at hcr hcl hcw same₃ ⊢
  have hsorted : (sortedIdx X.n X.p X.RAB).length ≤ X.n * X.n := by
    rw [length_sortedIdx_eq]
    exact classStart_le_sq X.n X.RAB X.p
  have keep : ∀ {a : ℕ} {l : List ℕ}, SegN μ₂ a l → a + l.length ≤ aCr X x.U fr → SegN μ₃ a l := by
    intro a l hs hle
    refine Seg.congr hs fun i hi => same₃ _ ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;>
      (simp only [List.length_map] at hi; omega)
  refine (h r₁ μ₃ ⟨keep hqi (by simp only [HostData.QI, queryRows, List.length_map]; omega),
    keep hqj (by simp only [HostData.QJ, queryCols, List.length_map]; omega), hcr, hcl, hcw,
    fun c hc => ?_⟩).mono (by simp; omega) fun _ hQ => hQ
  exact (same₃ c ⟨by omega, by omega, by omega⟩).trans (same₂ c (by simp only [Outside]; omega))

/-- Where the arrays lie, for the addresses of et17. -/
theorem hostLay_of (hr : Ready lim d x X μ fr) (hchunks : X.chunkCount ≤ X.n * X.n + X.p) :
    HostLay X (hostAddr x X fr) := by
  (obtain ⟨⟩ := id hr)
  have hplaces := host_places X x.U fr
  have hcomm : X.D * X.n = X.n * X.D := Nat.mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_⟩
  case refine_13 =>
    have := X.w_le_cap ht
    simp only [hostAddr]
    omega
  all_goals
    simp only [hostAddr]
    omega

/-- The arrays that the loop over the instances reads are in the memory. -/
theorem hostMem_of (hr : Ready lim d x X μ fr) {μ₁ μ₂ : ℕ → ℤ}
    (hresid : ResidMem x X fr μ μ₁) (hclass : ClassMem x X fr μ₁ μ₂) :
    HostMem X (hostAddr x X fr) μ₂ := by
  ((obtain ⟨⟩ := id hr); (obtain ⟨⟩ := id hresid); (obtain ⟨⟩ := id hclass))
  have hplaces := resid_places X x.U fr
  have lenRAC : X.RAC.length = X.n * X.n := (length_residList _ _).trans hr.lenAC
  have lenRBC : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  exact
    { segAB := hr.segAB.keep
      segBC := hr.segBC.keep
      segAC := hr.segAC.keep
      segRAC := hresid.rac.keep
      segRBC := hresid.rbc.keep
      segQI := hclass.qi
      segQJ := hclass.qj
      segCR := hclass.cr
      segCL := hclass.cl
      segCW := hclass.cw }

/-- What the third part needs holds for the data of a run of et17. -/
theorem ready_of {need : List ℕ → Need} {D g a b : ℕ} (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ready lim d x (hostData x D g) μ fr := by
  have hD16 := hbig.sixteen_le
  have hcells := hok.cells
  have hdepth := hok.depth
  have htop := aFr_le (x := x) (g := g) hD16 fr
  have hp := two_le_hostData_p x g hD16
  have hps := Nat.mul_le_mul_right (2 ^ (bitLen x.U + 1)) (hostData_p_le x g hD16)
  simp only [hostNeedAt] at hcells hdepth
  exact
    { space := hok.space
      depth := by omega
      prime := by omega
      word := le_word_of_le_hostWord hok
      top := by omega
      segAB := hpre.segAB
      segBC := hpre.segBC
      segAC := hpre.segAC
      lenAB := hpre.lenAB
      lenBC := hpre.lenBC
      lenAC := hpre.lenAC
      leAB := hpre.leAB
      leBC := hpre.leBC
      leAC := hpre.leAC
      belowAB := hpre.belowAB
      belowBC := hpre.belowBC
      belowAC := hpre.belowAC }

end Et17














































end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the parameters and the small case

The first part of the host procedure `et17` (Exact Triangle by Theorem 17) computes `D`, `g` and
`s = ⌊√D⌋` and tests whether `n` is small (`et17Params_spec`).  If it is, the host calls the brute
force (`et17Small_spec`; proof of Theorem 19: "smaller instances are solved by brute force").
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-- **The first part of et17**: the parameters, and whether n is small.  No cell changes. -/
theorem et17Params_spec (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Params ν) ⟨frame (et17Loc0 x fr), μ⟩
      (tD x.n + tG (Dfun x.n) + (18 * Nat.sqrt (Dfun x.n) + 12) + 40)
      fun σ' => σ' = ⟨frame (et17LocA x fr (Dfun x.n) (Gfun (Dfun x.n))), μ⟩ := by
  have hn := hpre.n_pos
  have hDpos := C.D_pos x.n hn
  unfold hostNeed at hok
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  generalize hD : Dfun x.n = D at *
  generalize hg : Gfun D = g at *
  -- The numbers that this part forms fit in a word.
  have hwD : ((wD x.n : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hwG : ((wG D : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hsqrt : ((3 * D + 4 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have h16 : ((16 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  unfold et17Params et17Loc0 et17LocA
  -- D := Dfun(n); g := Gfun(D)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((C.dProc lim d x.n μ hn hok.space hwD (by omega)) _ (by omega)) ?_ ?_
            ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.dProc lim d x.n μ hn hok.space hwD (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ ⟨rfl, rfl⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hD]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((C.gProc lim d D μ hDpos hok.space hwG (by omega)) _ (by omega)) ?_
            ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.gProc lim d D μ hDpos hok.space hwG (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ ⟨rfl, rfl⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hg]
  -- s := sqrt(D)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((sqrt_meets (K := D) C.hSqrt μ hsqrt) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (sqrt_meets (K := D) C.hSqrt μ hsqrt) ?_ ?_ ?_
            ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ
              ⟨rfl, rfl⟩
                  -- the four tests: D < 16, n < D, g < 1, s < g
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the four tests: D < 16, n < D, g < 1, s < g
  refine Ends.block ⟨by simp; omega, ?_⟩
  by_cases hD16 : D < 16 <;> by_cases hnD : x.n < D <;> by_cases hg0 : g = 0 <;>
    by_cases hsg : Nat.sqrt D < g <;> simp [update_frame_setLocal, SmallCase, hD16, hnD, hg0, hsg]


















end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the program, assembled

The procedures of the host are appended to a program `P₀` that already holds a solver of
Lop-AE-SparseTri and the two procedures that compute the parameters `D` and `g`.  This file has the
list of the procedures (`et17Procs`), their numbers (`et17NumsAt`), the proof that the program so
obtained is the context that the top procedure assumes (`et17Ctx_assembled`), and the
result: the host solves Exact Triangle (`et17_solves`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec




































































                                              -- 28

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}

/-- **The context of the top procedure**, in the assembled program with anything appended to
it. -/
theorem et17Ctx_assembled (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    Et17Ctx P₀ (et17Procs pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length) Tn need Dfun Gfun
      tD tG wD wG := by
  -- Procedure number `i` of the list.
  have L : ∀ {i : ℕ} {body : Stmt}, (et17Procs pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (et17Procs pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  exact
    { loop := ⟨hsol, L rfl, L rfl, L rfl, L rfl⟩
      hLoop := L rfl
      hSqrt := L (i := 0) rfl
      hBrute := L rfl
      hChoose := L rfl
      ch := ⟨L rfl, L rfl, L rfl,
        ⟨L rfl, L rfl, L rfl, L rfl, L rfl,
          L rfl, L rfl,
          ⟨L rfl, L rfl, L rfl, L rfl, L rfl⟩⟩,
        ⟨L (i := 0) rfl, L rfl⟩⟩
      hCap := L rfl
      hCeil := L rfl
      hBitLen := L rfl
      hDbl := L rfl
      hResid := L rfl
      hResidues := L rfl
      hClasses := L rfl
      hChunks := L rfl
      dProc := hD _
      gProc := hG _
      D_pos := hpos }
















end Light.Sec3

end
end

section


/-!
The parameter routines for the Corollary 26 choice, exposed for the new all-edges
host. These definitions and proofs are reproduced from the private declarations
in `ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean` at commit
`e1a4e6508154ea59f030480661590a9fe3018011`. The six-procedure list and its offsets
are unchanged: `D = floor(n^(1/18))` is at offset 2 and
`g = ceil(D^(63/2000))` is at offset 5. The two unused alternative-parameter
procedures remain in the list to preserve these established calling conventions.
-/

@[expose] public section

namespace APSPImprovement.AllEdges.Parameters

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- The exact six-entry source parameter program, appended at offset `o`. -/
def paramProcs (o : ℕ) : Program :=
  [powLtBody, rootCeilBody o, d26Body (o + 1), d5Body (o + 2), g5Body (o + 1), g26Body (o + 1)]

/-- Bound on the integer values formed while computing `D`. -/
def wD26 (n : ℕ) : ℕ := (n + 1) * (paramD₂₆Nat n + 1) + 19

/-- Bound on the integer values formed while computing `g`. -/
def wG26 (D : ℕ) : ℕ := D ^ 63 * paramG₂₆Nat D + 2001

theorem paramProcs_get (Q R : Program) {i : ℕ} {body : Stmt}
    (h : (paramProcs Q.length)[i]? = some body) :
    (Q ++ paramProcs Q.length ++ R)[Q.length + i]? = some body := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

/-- The executable floor-eighteenth-root procedure satisfies the host contract. -/
theorem paramProc_d26 (Q R : Program) :
    ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + 2) paramD₂₆Nat tD26 wD26 := by
  intro lim d x μ _ _ hw hd
  exact ⟨_, paramProcs_get Q R (i := 2) rfl, d26_spec (paramProcs_get Q R (i := 1) rfl)
    (paramProcs_get Q R (i := 0) rfl) hw (by omega)⟩

/-- The executable rational-power ceiling procedure satisfies the host contract. -/
theorem paramProc_g26 (Q R : Program) :
    ParamProc (Q ++ paramProcs Q.length ++ R) (Q.length + 5) paramG₂₆Nat tG26 wG26 := by
  intro lim d x μ hx _ hw hd
  exact ⟨_, paramProcs_get Q R (i := 5) rfl, g26_spec (paramProcs_get Q R (i := 1) rfl)
    (paramProcs_get Q R (i := 0) rfl) hx hw (by omega)⟩

theorem polyBounded_paramD₂₆Nat : PolyBounded fun n _ => paramD₂₆Nat n :=
  PolyBounded.fst.of_le fun n _ => paramD₂₆Nat_le n

theorem polyBounded_paramG₂₆Nat {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramG₂₆Nat (D n) :=
  (by first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply hD
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply hD
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply hD
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply hD
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)) : PolyBounded fun n _ => D n + 1).of_le fun n _ => by
    rcases Nat.eq_zero_or_pos (D n) with h0 | hpos
    · simp [h0, paramG₂₆Nat, rootCeil]
    · exact (paramG₂₆Nat_le hpos).trans (Nat.le_succ _)

theorem polyBounded_wD26 : PolyBounded fun n _ => wD26 n := by
  unfold wD26
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply polyBounded_paramD₂₆Nat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply polyBounded_paramD₂₆Nat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply polyBounded_paramD₂₆Nat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply polyBounded_paramD₂₆Nat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

theorem polyBounded_wG26 : PolyBounded fun n _ => wG26 (paramD₂₆Nat n) := by
  unfold wG26
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply polyBounded_paramD₂₆Nat
              | apply polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply polyBounded_paramD₂₆Nat
                            |
                              apply
                                polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply polyBounded_paramD₂₆Nat
                      | apply polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply polyBounded_paramD₂₆Nat
              | apply polyBounded_paramG₂₆Nat polyBounded_paramD₂₆Nat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

theorem steps_paramD₂₆Nat : StepsMon (fun θ => paramD₂₆Nat θ.n) 1 0 0 :=
  steps_n.of_le fun θ _ => paramD₂₆Nat_le θ.n

theorem steps_tD26 : StepsMon (fun θ => tD26 θ.n) 1 0 0 := by
  unfold tD26
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_paramD₂₆Nat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply steps_paramD₂₆Nat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply steps_paramD₂₆Nat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply steps_paramD₂₆Nat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

theorem steps_tG26 : StepsMon (fun θ => tG26 θ.D) 0 2 0 := by
  have hg : StepsMon (fun θ => paramG₂₆Nat θ.D) 0 2 0 :=
    steps_D.of_le fun _ hθ => paramG₂₆Nat_le hθ.one_le_D_nat
  unfold tG26
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply hg
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply hg
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply hg
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply hg
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

end APSPImprovement.AllEdges.Parameters








end
end

section


namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

noncomputable def allEdges26Time : (List ℕ → ℕ) → ℕ → ℕ → ℕ :=
  allHostTime 100 paramD₂₆Nat paramG₂₆Nat tD26 tG26

def allEdges26Need : (List ℕ → Need) → ℕ → ℕ → Need :=
  hostNeed paramD₂₆Nat paramG₂₆Nat Parameters.wD26 Parameters.wG26

theorem allEdges26Need_poly {r : List ℕ → Need} (hr : PolyNeedN r) : PolyNeed (allEdges26Need r) :=
  hostNeed_poly Parameters.polyBounded_paramD₂₆Nat
    (Parameters.polyBounded_paramG₂₆Nat Parameters.polyBounded_paramD₂₆Nat)
    Parameters.polyBounded_wD26 Parameters.polyBounded_wG26 hr

/-- The analytic pipeline now requires only the actual prepared solver at the
specified parameters. All resource, small-case, initialization and exponent
obligations outside that program are discharged by proved constructions. -/
theorem claim17_from_prepared26
    (hhost : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ),
        Solves preparedAllEdgesTask (Q ++ R) p' (allEdges26Time Tn) (allEdges26Need r)) :
    Claim.Theorem_17 allEdgesModel strassen paramD₂₆ paramG₂₆ := by
  apply claim17_of_allEdges_host strassen paramD₂₆ paramG₂₆
    (allHostTime 200 paramD₂₆Nat paramG₂₆Nat tD26 tG26)
    (fun r => Adapter.need (allEdges26Need r))
  · apply full_host_of_prepared 100 paramD₂₆Nat paramG₂₆Nat tD26 tG26 allEdges26Need
    intro Q pS Tn r hr hs
    obtain ⟨R, p', hsol⟩ := hhost Q pS Tn r hr hs
    exact ⟨R, p', hsol, allEdges26Need_poly hr⟩
  · exact obeysBound17_allHostTime 200 paramD₂₆ paramG₂₆ paramD₂₆Nat_eq
      (fun _ hn => paramG₂₆Nat_eq hn)
      Parameters.steps_tD26.withinBuild Parameters.steps_tG26.withinBuild









end APSPImprovement.AllEdges



end

section


/-! A verified counting loop over the oracle answers of one Theorem 17 instance. -/

namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

structure ScanSeparation (dst n ab bc ac out qa qb w : ℕ) : Prop where
  ab : Apart ab (n * n) dst (n * n)
  bc : Apart bc (n * n) dst (n * n)
  ac : Apart ac (n * n) dst (n * n)
  out : Apart out w dst (n * n)
  qa : Apart qa w dst (n * n)
  qb : Apart qb w dst (n * n)

theorem weights_keep_flags {lim : Limits} {μ μ' : ℕ → ℤ} {ab bc ac n U dst : ℕ}
    {AB BC AC : List ℤ} (C : Weights lim μ ab bc ac n U AB BC AC)
    (hs : SameOutside μ μ' dst (n * n))
    (ha : Apart ab (n * n) dst (n * n)) (hb : Apart bc (n * n) dst (n * n))
    (hc : Apart ac (n * n) dst (n * n)) : Weights lim μ' ab bc ac n U AB BC AC := by
  exact { C with
    arrAB := C.arrAB.keep (SameOn.mono hs fun _ h => by omega)
    arrBC := C.arrBC.keep (SameOn.mono hs fun _ h => by omega)
    arrAC := C.arrAC.keep (SameOn.mono hs fun _ h => by omega) }

theorem answers_keep_flags {lim : Limits} {μ μ' : ℕ → ℤ} {out qa qb w n dst : ℕ}
    {OUT : List ℤ} {QA QB : List ℕ} (A : Answers lim μ out qa qb w n OUT QA QB)
    (hs : SameOutside μ μ' dst (n * n))
    (ho : Apart out w dst (n * n)) (ha : Apart qa w dst (n * n))
    (hb : Apart qb w dst (n * n)) : Answers lim μ' out qa qb w n OUT QA QB := by
  exact { A with
    arrOUT := A.arrOUT.keep (SameOn.mono hs fun _ h => by omega)
    arrQA := A.arrQA.keep (SameOn.mono hs fun _ h => by omega)
    arrQB := A.arrQB.keep (SameOn.mono hs fun _ h => by omega) }

def inputQuery (n : ℕ) (AB BC AC OUT : List ℤ) (QA QB : List ℕ) (c0 len i : ℕ) : Query :=
  ⟨QA.getD i 0 * n + QB.getD i 0, accOf OUT i, hitOf n AB BC AC QA QB c0 len i⟩

theorem inputQuery_pair_lt {lim : Limits} {μ : ℕ → ℤ} {out qa qb w n c0 len i : ℕ}
    {AB BC AC OUT : List ℤ} {QA QB : List ℕ}
    (A : Answers lim μ out qa qb w n OUT QA QB) (hi : i < w) :
    (inputQuery n AB BC AC OUT QA QB c0 len i).pair < n * n :=
  Nat.mul_add_lt_mul (A.arrQA.getD_lt hi) (A.arrQB.getD_lt hi)

namespace QueriesLocal
abbrev Out : ℕ := 0
abbrev Rows : ℕ := 1
abbrev Cols : ℕ := 2
abbrev Num : ℕ := 3
abbrev Flags : ℕ := 4
abbrev AB : ℕ := 5
abbrev BC : ℕ := 6
abbrev AC : ℕ := 7
abbrev Size : ℕ := 8
abbrev First : ℕ := 9
abbrev Len : ℕ := 10
abbrev Cnt : ℕ := 11
abbrev Unused : ℕ := 12
end QueriesLocal

open QueriesLocal in
def scanQueriesCall (pPair : ℕ) : Stmt :=
  .call pPair [v AB, v BC, v AC, v Size, M (((Light.Expr.op Light.Op.add) (v Rows) (v Cnt))), M (((Light.Expr.op Light.Op.add) (v Cols) (v Cnt))),
    v First, v Len, ((Light.Expr.op Light.Op.add) (v Flags)
                      ((Light.Expr.op Light.Op.add)
                        ((Light.Expr.op Light.Op.mul)
                          (M ((Light.Expr.op Light.Op.add) (v Rows) (v Cnt))) (v Size))
                        (M ((Light.Expr.op Light.Op.add) (v Cols) (v Cnt))))),
    M (((Light.Expr.op Light.Op.add) (v Out) (v Cnt)))] Unused

open QueriesLocal in
def scanQueriesBody (pPair : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Cnt (k 0))
    (.while (Light.Cond.lt (v Cnt) (v Num))
      (Light.Stmt.seq (scanQueriesCall pPair)
        (.set Cnt ((Light.Expr.op Light.Op.add) (v Cnt) (k 1))))))

def queriesState (μ : ℕ → ℤ) (out qa qb w dst ab bc ac n c0 len i : ℕ) (unused : ℤ) : State :=
  ⟨frame [out, qa, qb, w, dst, ab, bc, ac, n, c0, len, i, unused], μ⟩

def executed (q : ℕ → Query) (found : Finset ℕ) (i : ℕ) : Bool :=
  (q i).accepted && decide ((q i).pair ∉ (run (queryPrefix q i) found).found)

theorem sum_query_times (q : ℕ → Query) (found : Finset ℕ) (len w : ℕ) :
    ∑ i ∈ Finset.range w, (64 + if executed q found i then tScan len + 20 else 0) =
      64 * w + (tScan len + 20) * (run (queryPrefix q w) found).scans := by
  induction w with
  | zero => simp [queryPrefix, run]
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, prefixScans_succ]
    unfold executed
    split_ifs <;> ring

/-- Scan all answers of one instance, retaining all successes in the persistent pair table.
Only actually executed scans contribute their `tScan len` cost. -/
theorem scanQueries_spec {lim : Limits} {P : Program} {d pPair pScan : ℕ} {μ : ℕ → ℤ}
    {ab bc ac n c0 len U dst out qa qb w : ℕ} {AB BC AC OUT : List ℤ} {QA QB : List ℕ}
    {found : Finset ℕ}
    (hpair : P[pPair]? = some (scanPairBody pScan)) (hscan : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC)
    (A : Answers lim μ out qa qb w n OUT QA QB)
    (R : ScanSeparation dst n ab bc ac out qa qb w)
    (hf : FlagTable μ dst (n * n) found)
    (h01 : ∀ i < w, OUT.getD i 0 = bit (accOf OUT i))
    (hc : c0 + len ≤ n) (hn : n ≤ lim.space) (hflags : dst + n * n ≤ lim.space)
    (hd : d + 1 < lim.depth) :
    Ends lim P d (scanQueriesBody pPair)
      ⟨frame [out, qa, qb, w, dst, ab, bc, ac, n, c0, len], μ⟩
      (64 * w + (tScan len + 20) *
        (run (queryPrefix (inputQuery n AB BC AC OUT QA QB c0 len) w) found).scans + 6)
      (fun σ' => σ'.mem =
        runMemory (queryPrefix (inputQuery n AB BC AC OUT QA QB c0 len) w) found μ dst) := by
  let q := inputQuery n AB BC AC OUT QA QB c0 len
  let μi := fun i => runMemory (queryPrefix q i) found μ dst
  have hq : ∀ i ≤ w, ∀ r ∈ queryPrefix q i, r.pair < n * n := by
    intro i hi r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
    exact inputQuery_pair_lt A (lt_of_lt_of_le (List.mem_range.1 hj) hi)
  have hkept : ∀ i ≤ w, SameOutside μ (μi i) dst (n * n) :=
    fun i hi => runMemory_outside _ _ _ _ _ (hq i hi)
  have htable : ∀ i ≤ w, FlagTable (μi i) dst (n * n) (run (queryPrefix q i) found).found :=
    fun i hi => runMemory_table _ hf (hq i hi)
  have hC : ∀ i ≤ w, Weights lim (μi i) ab bc ac n U AB BC AC :=
    fun i hi => weights_keep_flags C (hkept i hi) R.ab R.bc R.ac
  have hA : ∀ i ≤ w, Answers lim (μi i) out qa qb w n OUT QA QB :=
    fun i hi => answers_keep_flags A (hkept i hi) R.out R.qa R.qb
  have hsum := sum_query_times q found len w
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.arrAB); (obtain ⟨⟩ := id C.arrBC);
    (obtain ⟨⟩ := id C.arrAC); (obtain ⟨⟩ := id A); (obtain ⟨⟩ := id A.arrOUT);
    (obtain ⟨⟩ := id A.arrQA); (obtain ⟨⟩ := id A.arrQB))
  unfold scanQueriesBody
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine (Ends.while
    (fun i σ => ∃ unused, σ = queriesState (μi i) out qa qb w dst ab bc ac n c0 len i unused)
    w (fun i => 60 + if executed q found i then tScan len + 20 else 0)
    ?start ?round ?done).mono ?time (fun _ h => h)
  case start =>
    refine ⟨0, ?_⟩
    simp only [queriesState, μi, queryPrefix, List.range_zero, List.map_nil, runMemory]
    congr 1
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro i _ hi ⟨unused, rfl⟩
    have C' := hC i hi.le
    have A' := hA i hi.le
    have hreadQA := A'.arrQA.read hi
    have hreadQB := A'.arrQB.read hi
    have hreadOUT := (A'.arrOUT.read hi).trans (h01 i hi)
    have ha := A'.arrQA.getD_lt hi
    have hb := A'.arrQB.getD_lt hi
    have hpidx := inputQuery_pair_lt (AB := AB) (BC := BC) (AC := AC) (c0 := c0) (len := len) A' hi
    have hreadFlag := htable i hi.le _ hpidx
    have hpairZ : (QA.getD i 0 : ℤ) * n + QB.getD i 0 < (n * n : ℕ) := by
      exact_mod_cast hpidx
    have hprodZ : (0 : ℤ) ≤ (QA.getD i 0 : ℤ) * n := by positivity
    simp only [List.getD_eq_getElem?_getD] at hpairZ hprodZ
    ((obtain ⟨⟩ := id A'); (obtain ⟨⟩ := id A'.arrOUT); (obtain ⟨⟩ := id A'.arrQA);
      (obtain ⟨⟩ := id A'.arrQB))
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, queriesState] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                               ((try have := Light.Std.const_le (by assumption)));
                                                                                               (simp [Light.Limits.Addr, abs_le, -abs_mul, queriesState] <;> omega)), ?_⟩
    unfold scanQueriesCall queriesState
    refine Ends.callToThen (scanPair_meets (accepted := accOf OUT i) hpair hscan C' ha hb hc hn
      (by exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hpidx dst) hflags) hreadFlag hd) ?_
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadQA, hreadQB, hreadOUT, q,
                  inputQuery, bit] <;>
                omega)))
      (by omega) (by simp only [executed, q, inputQuery]; first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega))))
    rintro r _ rfl
    simp only [executed, q, inputQuery]
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨r, ?_⟩
    congr 1
    exact (prefixMemory_succ q i found μ dst).symm
  case done =>
    rintro _ ⟨unused, rfl⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, queriesState] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                              ((try have := Light.Std.const_le (by assumption)));
                                                                                              (simp [Light.Limits.Addr, abs_le, -abs_mul, queriesState] <;> omega)), rfl⟩
  case time =>
    simp only [Cond.cost, Expr.cost, Nat.reduceAdd]
    have hsum' : (∑ i ∈ Finset.range w, (4 + (60 + if executed q found i then tScan len + 20 else 0))) =
        64 * w + (tScan len + 20) * (run (queryPrefix q w) found).scans := by
      simpa only [← Nat.add_assoc, Nat.reduceAdd] using hsum
    rw [hsum']
    dsimp only [q] at hsum' ⊢
    omega































end APSPImprovement.AllEdges




end

section


namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

theorem host_inputQuery_eq (X : HostData) (t i : ℕ) (hi : i < X.w t) :
    inputQuery X.n X.AB X.BC X.AC (X.ans t) (X.WI t) (X.WJ t) (X.c0 t) (X.len t) i =
      hostQuery X t i := by
  unfold inputQuery hostQuery
  congr 1
  rw [HostData.getD_WI hi, HostData.getD_WJ hi, HostData.rowOf_mul_add_colOf]

theorem host_queryPrefix_eq (X : HostData) (t : ℕ) :
    queryPrefix (inputQuery X.n X.AB X.BC X.AC (X.ans t) (X.WI t) (X.WJ t)
      (X.c0 t) (X.len t)) (X.w t) = instanceQueries X t := by
  apply List.map_congr_left
  intro i hi
  exact host_inputQuery_eq X t i (List.mem_range.1 hi)









end APSPImprovement.AllEdges




end

section


set_option maxHeartbeats 1000000

namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec
open Light.Sec3.HostLocal

/-- The old Found local now holds the persistent flag-table address. -/
def allHostCalls (pS pWriteX pWriteY pQueries : ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pWriteX
      [v MatX, v ResAC, v Size, v ParD, v ThePrime, v PieceStart, v Len,
        v Residue]
      Unused)
    (Light.Stmt.seq
      (.call pWriteY
        [v MatY, v ResBC, v Size, v ParD, v ThePrime, v PieceStart, v Len] Unused)
      (Light.Stmt.seq
        (.call pS
          [v Size, v ParD, v NumPairs, k 1, v MatX, v MatY,
            (Light.Expr.op Light.Op.add) (v Rows) (v Start),
            (Light.Expr.op Light.Op.add) (v Cols) (v Start), v AdrOut,
            v SolverFree]
          Unused)
        (.call pQueries
          [v AdrOut, (Light.Expr.op Light.Op.add) (v Rows) (v Start),
            (Light.Expr.op Light.Op.add) (v Cols) (v Start), v NumPairs, v Found,
            v AdrAB, v AdrBC, v AdrAC, v Size, v PieceStart, v Len]
          Unused))))

def allHostRound (pS pWriteX pWriteY pQueries : ℕ) : Stmt :=
  (Light.Stmt.seq hostParams
    (Light.Stmt.seq (allHostCalls pS pWriteX pWriteY pQueries) hostNext))

def allHostLoopBody (pS pWriteX pWriteY pQueries : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Inst (k 0))
    (Light.Stmt.seq (.set ChunkNo (k 0))
      (Light.Stmt.seq (.set PieceStart (k 0))
        (Light.Stmt.seq
          (.while (Light.Cond.lt (v Inst) (v NumInst))
            (allHostRound pS pWriteX pWriteY pQueries))
          (.set 0 (k 1))))))

def allHostLoopArgs (X : HostData) (A : HostAddr) (dst : ℕ) : List ℤ :=
  hostLoopArgs X A ++ [0, 0, 0, (dst : ℤ)]

def tAllCalls (Tn : List ℕ → ℕ) (X : HostData) (t : ℕ) : ℕ :=
  tWriteX X.n X.D (X.len t) + tWriteY X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    64 * X.w t + (tScan (X.len t) + 20) * instanceScans X t + 64

def tAllHostLoop (Tn : List ℕ → ℕ) (X : HostData) : ℕ :=
  (∑ t ∈ Finset.range X.m, (tAllCalls Tn X t + 49)) + 12

theorem inputQueries_eq (X : HostData) (t : ℕ) :
    queryPrefix (inputQuery X.n X.AB X.BC X.AC (X.ans t) (X.WI t) (X.WJ t)
      (X.c0 t) (X.len t)) (X.w t) = instanceQueries X t := host_queryPrefix_eq X t

variable {lim : Limits} {d : ℕ} {P₀ R : Program}
  {pS pWriteX pWriteY pOldPairs pScan pPair pQueries : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {X : HostData} {U : ℕ} {A : HostAddr} {dst t : ℕ} {μ μ' : ℕ → ℤ}

theorem allQueries_meets
    (C : HostCtx P₀ R pS pWriteX pWriteY pOldPairs pScan Tn need)
    (hp : (P₀ ++ R)[pPair]? = some (scanPairBody pScan))
    (hq : (P₀ ++ R)[pQueries]? = some (scanQueriesBody pPair))
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (F : FlagsLay X A dst) (hd : d + 3 ≤ lim.depth)
    (hans : Seg μ' A.out (X.ans t))
    (hf : FlagTable μ' dst (X.n * X.n) (foundAfter X t)) :
    Meets lim (P₀ ++ R) pQueries (d + 1)
      [(A.out : ℤ), (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), X.w t, dst,
        A.ab, A.bc, A.ac, X.n, X.c0 t, X.len t] μ'
      (64 * X.w t + (tScan (X.len t) + 20) * instanceScans X t + 6)
      fun _ μ'' => FlagTable μ'' dst (X.n * X.n) (foundAfter X (t + 1)) ∧
        SameOutside μ' μ'' dst (X.n * X.n) := by
  have hplaces := S.places ht
  have hfbelow := F.below
  have hn : X.n ≤ X.n * X.n := Nat.le_mul_self _
  have sep : ScanSeparation dst X.n A.ab A.bc A.ac A.out
      (A.qi + X.lo t) (A.qj + X.lo t) (X.w t) := by
    refine ⟨F.ab, F.bc, F.ac, Or.inr (by omega), ?_, ?_⟩
    · rcases F.qi with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · rcases F.qj with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have h01 : ∀ i < X.w t, (X.ans t).getD i 0 = bit (accOf (X.ans t) i) := by
    intro i hi
    simp only [accOf, S.ok.valid.getD_ans ht hi]
    split_ifs <;> norm_num [bit]
  have h := scanQueries_spec (d := d + 1) hp C.scan (S.weights ht) (S.answers ht hans) sep hf h01
    (S.ok.valid.piece_le ht) (by omega) (by omega) (by omega)
  rw [inputQueries_eq] at h
  refine Meets.of_body hq (h.mono le_rfl ?_)
  intro σ hs
  rw [hs]
  have hpairs : ∀ q ∈ instanceQueries X t, q.pair < X.n * X.n := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := (mem_instanceQueries X t q).1 hq
    exact S.ok.valid.place_lt ht hi
  exact ⟨by rw [foundAfter_succ]; exact runMemory_table _ hf hpairs,
    runMemory_outside _ _ _ _ _ hpairs⟩

theorem allHostCalls_spec
    (C : HostCtx P₀ R pS pWriteX pWriteY pOldPairs pScan Tn need)
    (hp : (P₀ ++ R)[pPair]? = some (scanPairBody pScan))
    (hq : (P₀ ++ R)[pQueries]? = some (scanQueriesBody pPair))
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (F : FlagsLay X A dst) (hd : d + 3 ≤ lim.depth)
    (hf : FlagTable μ' dst (X.n * X.n) (foundAfter X t)) (ch : ℕ) (res : ℤ) :
    Ends lim (P₀ ++ R) d (allHostCalls pS pWriteX pWriteY pQueries)
      (hostState X A t ch (X.c0 t) dst (X.len t) (X.rho t) (X.lo t) (X.w t) res μ')
      (tAllCalls Tn X t) fun σ => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ = hostState X A t ch (X.c0 t) dst (X.len t) (X.rho t) (X.lo t)
          (X.w t) res' μ'' ∧ HostMem X A μ'' ∧
          FlagTable μ'' dst (X.n * X.n) (foundAfter X (t + 1)) ∧
          KeptBut μ' μ'' A.x dst (X.n * X.n) := by
  have hplaces := S.places ht
  have hfbelow := F.below
  unfold allHostCalls tAllCalls
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen ((C.writeX_meets S ht) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (C.writeX_meets S ht) ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₁ μ₁ ⟨hX, hrest₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have S₁ := S.next fun a ha => hrest₁ a (Or.inl ha)
  have hf₁ := hf.keep_below (fun a ha => hrest₁ a (Or.inl ha)) F.below
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen ((C.writeY_meets S₁ ht) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (C.writeY_meets S₁ ht) ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₂ μ₂ ⟨hY, hrest₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have S₂ := S₁.next fun a ha => hrest₂ a (Or.inl (by omega))
  have hf₂ := hf₁.keep_below (fun a ha => hrest₂ a (Or.inl (by omega))) F.below
  replace hX : Seg μ₂ A.x (X.matX t) := hX.keep (by ((try have := X.length_matX t);
                                                         (((try refine Light.SameOn.cell ?_);
                                                             (intro apspMacro_607040_0 apspMacro_607040_1);
                                                             (first
                                                               |
                                                                 ((((repeat
                                                                           (((with_reducible
                                                                                   rename Light.SameOn _ _ _ => apspMacro_607040_2));
                                                                             ((try
                                                                                   have :=
                                                                                     apspMacro_607040_2 apspMacro_607040_0
                                                                                       (by omega)));
                                                                             (revert apspMacro_607040_2)));
                                                                       (intros);
                                                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                   (omega))
                                                               |
                                                                 ((simp [X.length_matX t] at apspMacro_607040_1);
                                                                   (((repeat
                                                                           (((with_reducible
                                                                                   rename Light.SameOn _ _ _ => apspMacro_607040_3));
                                                                             ((try
                                                                                   have :=
                                                                                     apspMacro_607040_3 apspMacro_607040_0
                                                                                       (by omega)));
                                                                             (revert apspMacro_607040_3)));
                                                                       (intros);
                                                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                   (omega))
                                                               |
                                                                 ((((repeat
                                                                           (((with_reducible
                                                                                   rename Light.SameOn _ _ _ => apspMacro_607040_4));
                                                                             ((try
                                                                                   have :=
                                                                                     apspMacro_607040_4 apspMacro_607040_0
                                                                                       (by omega)));
                                                                             (revert apspMacro_607040_4)));
                                                                       (intros);
                                                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                   (fail
                                                                       "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                 SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                 its condition K x does not follow from the hypotheses.")))))))
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen ((C.solver_meets S₂ ht hX hY) _ (by omega)) ?_ ?_
            ?_ ?_
      | refine Light.Ends.callToThen (C.solver_meets S₂ ht hX hY) ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₃ μ₃ ⟨hans, hkept₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have S₃ := S₂.next fun a ha => hkept₃ a (by omega)
  have hf₃ := hf₂.keep_below (fun a ha => hkept₃ a (by omega)) F.below
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((allQueries_meets C hp hq S₃ ht F hd hans hf₃) _ (by omega)) ?_ ?_ ?_
            ?_
      |
        refine
          Light.Ends.callToThen (allQueries_meets C hp hq S₃ ht F hd hans hf₃) ?_
            ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₄ μ₄ ⟨hf₄, hrest₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨r₄, μ₄, rfl, hostMem_keep_flags S.ok.valid S₃.mem_prime F hrest₄, hf₄, ?_⟩
  intro addr ha
  exact (hrest₄ addr ha.2).trans
    ((hkept₃ addr (by omega)).trans ((hrest₂ addr (Or.inl (by omega))).trans
      (hrest₁ addr (Or.inl ha.1))))

def AllHostInv (X : HostData) (A : HostAddr) (dst : ℕ) (μ : ℕ → ℤ)
    (t : ℕ) (σ : State) : Prop :=
  ∃ (len rho lo w res : ℤ) (μ' : ℕ → ℤ),
    σ = hostState X A t (t % X.chunkCount) (X.c0 t) dst len rho lo w res μ' ∧
    HostMem X A μ' ∧ FlagTable μ' dst (X.n * X.n) (foundAfter X t) ∧
    KeptBut μ μ' A.x dst (X.n * X.n)

theorem allHostRound_spec
    (C : HostCtx P₀ R pS pWriteX pWriteY pOldPairs pScan Tn need)
    (hp : (P₀ ++ R)[pPair]? = some (scanPairBody pScan))
    (hq : (P₀ ++ R)[pQueries]? = some (scanQueriesBody pPair))
    (hok : HostOk X U) (hlay : HostLay X A) (hlim : HostLim lim d X U A need)
    (F : FlagsLay X A dst) (hd : d + 3 ≤ lim.depth)
    (ht : t < X.m) {σ : State} (hσ : AllHostInv X A dst μ t σ) :
    Ends lim (P₀ ++ R) d (allHostRound pS pWriteX pWriteY pQueries) σ
      (tAllCalls Tn X t + 45) (AllHostInv X A dst μ (t + 1)) := by
  obtain ⟨len, rho, lo, w, res, μ', rfl, hm, hf, hk⟩ := hσ
  have S : HostSetting lim d X U A need μ' μ' := ⟨hok, hm, hlay, hlim, SameOn.refl⟩
  unfold allHostRound
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (hostParams_spec S ht (dst : ℤ) len rho lo w res)
            ?_ ?_
      |
        refine
          Light.Ends.pieceLast (hostParams_spec S ht (dst : ℤ) len rho lo w res)
            ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => rintro _ rfl)
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (allHostCalls_spec C hp hq S ht F hd hf _ res) ?_
            ?_
      |
        refine
          Light.Ends.pieceLast (allHostCalls_spec C hp hq S ht F hd hf _ res) ?_
            ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => rintro _ ⟨res', μ'', rfl, hm', hf', hk'⟩)
  have S' : HostSetting lim d X U A need μ'' μ'' := ⟨hok, hm', hlay, hlim, SameOn.refl⟩
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (hostNext_spec S' ht (dst : ℤ) _ _ _ _ res') ?_ ?_
      |
        refine
          Light.Ends.pieceLast (hostNext_spec S' ht (dst : ℤ) _ _ _ _ res') ?_
            ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => rintro _ rfl)
  exact ⟨_, _, _, _, _, μ'', rfl, hm', hf', hk.trans hk'⟩

theorem allHostLoop_spec
    (C : HostCtx P₀ R pS pWriteX pWriteY pOldPairs pScan Tn need)
    (hp : (P₀ ++ R)[pPair]? = some (scanPairBody pScan))
    (hq : (P₀ ++ R)[pQueries]? = some (scanQueriesBody pPair))
    (hok : HostOk X U) (hmem : HostMem X A μ) (hlay : HostLay X A)
    (hlim : HostLim lim d X U A need) (F : FlagsLay X A dst)
    (hd : d + 3 ≤ lim.depth) (hf : FlagTable μ dst (X.n * X.n) ∅) :
    Ends lim (P₀ ++ R) d (allHostLoopBody pS pWriteX pWriteY pQueries)
      ⟨frame (allHostLoopArgs X A dst), μ⟩ (tAllHostLoop Tn X) fun σ' =>
      FlagTable σ'.mem dst (X.n * X.n) (foundAfter X X.m) ∧
        KeptBut μ σ'.mem A.x dst (X.n * X.n) := by
  have hw := hlim.space
  have hfbelow := F.below
  have hfr := hlim.fr
  have hxy := hlay.xy
  have hyo := hlay.yo
  have hone : (1 : ℤ) ≤ lim.word := by
    have := hok.valid.n_pos
    have := hlay.bAB
    have := hlim.weights
    omega
  have heq : ∑ t ∈ Finset.range X.m, (4 + (tAllCalls Tn X t + 45)) =
      ∑ t ∈ Finset.range X.m, (tAllCalls Tn X t + 49) := by
    apply Finset.sum_congr rfl
    intro t _
    omega
  unfold allHostLoopBody tAllHostLoop allHostLoopArgs hostLoopArgs
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine Ends.next _ (Ends.while (AllHostInv X A dst μ) X.m
    (fun t => tAllCalls Tn X t + 45) ?start ?round ?done) ?time
  case start =>
    refine ⟨0, 0, 0, 0, 0, μ, ?_, hmem, hf, SameOn.refl⟩
    simp [hostState, HostData.c0]
    exact (frame_append_zeros (allHostLoopArgs X A dst) 5).symm
  case round =>
    intro t σ ht hσ
    obtain ⟨len, rho, lo, w, res, μ', rfl, _⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using ht,
      allHostRound_spec C hp hq hok hlay hlim F hd ht hσ⟩
  case done =>
    rintro _ ⟨len, rho, lo, w, res, μ', rfl, _, hf', hk'⟩
    exact ⟨⟨trivial, trivial⟩, by simp, Ends.setTo (1 : ℤ) ⟨hf', hk'⟩
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT := by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩
  case time =>
    simp only [Cond.cost, Expr.cost, Nat.reduceAdd]
    rw [heq]
    omega

end APSPImprovement.AllEdges



end

section


set_option maxHeartbeats 1500000

namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

open Light.Sec3.Et17 in
/-- Reuse the certified residue/class construction and invoke the persistent all-edges loop. -/
def allEt17Tables (ν : Et17Nums) (pAllLoop : ℕ) : Stmt :=
  (Light.Stmt.seq (.call ν.pDbl [v Free, v ThePrime, v Bits] Small)
    (Light.Stmt.seq
      (.call ν.pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small)
      (Light.Stmt.seq
        (.call ν.pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small)
        (Light.Stmt.seq
          (.call ν.pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small)
          (Light.Stmt.seq
            (.call ν.pClasses
              [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small)
            (Light.Stmt.seq
              (.call ν.pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW]
                NumChunks)
              (Light.Stmt.seq
                (.set NumInst
                  ((Light.Expr.op Light.Op.mul) (v NumPieces) (v NumChunks)))
                (.call pAllLoop
                  [v Size, v ParD, v ThePrime, v PieceLen, v NumChunks, v NumInst,
                    v AdrAB, v AdrBC, v AdrAC, v ResAC, v ResBC, v Rows, v Cols,
                    v TabR, v TabL, v TabW, v MatX, v MatY, v AdrOut,
                    v SolverFree, k 0, k 0, k 0,
                    M ((Light.Expr.op Light.Op.sub) (v Free) (k 1))]
                  0))))))))

def allHostRunTime (Tn : List ℕ → ℕ) (X : HostData) (U : ℕ) : ℕ :=
  tDblTable (bitLen U) + 3 * tResidues (X.n * X.n) (bitLen U) + tClasses X.n X.p +
    tChunks X.p X.chunkCount + tAllHostLoop Tn X + 100

theorem allHostRunTime_le (Tn : List ℕ → ℕ) (X : HostData) (U : ℕ) :
    allHostRunTime Tn X U ≤ hostRunTime (fun _ => 0) X U + tAllHostLoop Tn X + 20 := by
  unfold allHostRunTime hostRunTime
  omega

theorem flagsLay_of {x : AllEdgesInst} {μ : ℕ → ℤ} {fr : ℕ} {X : HostData}
    (hpre : x.Pre μ fr) (hn : X.n = x.n) :
    FlagsLay X (hostAddr x.toTriInst X fr) x.out := by
  have hplaces := host_places X x.U fr
  have hb := hpre.belowOut
  rw [← hn] at hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hostAddr]; omega
  · simpa only [hostAddr, hn] using hpre.apartAB
  · simpa only [hostAddr, hn] using hpre.apartBC
  · simpa only [hostAddr, hn] using hpre.apartAC
  all_goals
    simp only [hostAddr]
    apply Or.inr
    omega

theorem FlagTable.seg_outputFlags {μ : ℕ → ℤ} {X : HostData} {dst : ℕ}
    (hf : FlagTable μ dst (X.n * X.n) (foundAfter X X.m)) :
    Seg μ dst (outputFlags X) := by
  intro i hi
  simp only [outputFlags, List.length_map, List.length_range] at hi
  classical
  by_cases h : i ∈ (run (hostQueries X X.m) ∅).found <;>
    simpa [outputFlags, foundAfter, bit, h] using hf i hi

open Light.Sec3.Et17 in
theorem allEt17Tables_spec {P₀ R : Program} {ν : Et17Nums}
    {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ}
    (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    {pPair pQueries pAllLoop : ℕ}
    (hp : (P₀ ++ R)[pPair]? = some (scanPairBody ν.pScan))
    (hq : (P₀ ++ R)[pQueries]? = some (scanQueriesBody pPair))
    (hl : (P₀ ++ R)[pAllLoop]? =
      some (allHostLoopBody ν.pS ν.pWriteX ν.pWriteY pQueries))
    {lim : Limits} {d : ℕ} (x : AllEdgesInst) (μ : ℕ → ℤ) (fr D g a b : ℕ)
    (hpre : preparedAllEdgesTask.Pre x μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (allEt17Tables ν pAllLoop)
      ⟨frame (et17LocB x.toTriInst fr D g), μ⟩
      (allHostRunTime Tn (hostData x.toTriInst D g) x.U)
      fun σ' => preparedAllEdgesTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨hpre, hf, hfrpos, hmeta⟩ := hpre
  have hr := ready_of hpre.toPre hbig hok
  have hlim := hostLim_of_ok hbig hok
  have hv := hostData_valid hpre.toPre hbig
  have hF := flagsLay_of (X := hostData x.toTriInst D g) hpre rfl
  have hd : (d + 1) + 3 ≤ lim.depth := by
    have h := hok.depth
    simp only [hostNeedAt] at h
    omega
  have hn : (hostData x.toTriInst D g).n = x.n := rfl
  have hAB : (hostData x.toTriInst D g).AB = x.AB := rfl
  have hBC : (hostData x.toTriInst D g).BC = x.BC := rfl
  have hAC : (hostData x.toTriInst D g).AC = x.AC := rfl
  unfold et17LocB
  generalize hostData x.toTriInst D g = X at hr hlim hv hF hn hAB hBC hAC ⊢
  have hdepth := hr.depth
  have hplaces := host_places X x.U fr
  have hfr : fr ≤ aX X x.U fr := by omega
  have hcls : fr ≤ aCls X x.U fr := by omega
  have hout : x.out + X.n * X.n ≤ fr := by simpa only [hn] using hpre.belowOut
  unfold allEt17Tables allHostRunTime
  refine resid_then C.hDbl C.hResid C.hResidues hr (fun r₁ μ₁ hresid => ?_) (by omega)
  refine classes_then C.hClasses C.hChunks hr hv.cap_pos hresid.rab
    (fun r₂ μ₂ hclass => ?_) (by omega)
  have hk : Kept μ μ₂ fr := fun c hc =>
    (hclass.same c (Or.inl (by omega))).trans (hresid.same c (Or.inl hc))
  have hf₂ : FlagTable μ₂ x.out (X.n * X.n) ∅ := by
    apply FlagTable.keep_below (by simpa only [hn] using hf) hk hout
  have hmeta₂ : μ₂ (fr - 1) = (x.out : ℤ) := (hk _ (by omega)).trans hmeta
  have hcount := hlim.count
  have hm : (X.m : ℤ) = (X.h : ℤ) * X.chunkCount := by
    rw [HostData.m]
    push_cast
    rfl
  have hpos : (0 : ℤ) ≤ (X.h : ℤ) * X.chunkCount := by positivity
  have htop := hr.top
  have hspace := hr.space
  have hmetaint : (fr : ℤ) - 1 = ((fr - 1 : ℕ) : ℤ) := by omega
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (X.m : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hm]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hm] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hm] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((Meets.of_body (Q := fun _ μ' =>
                FlagTable μ' x.out (X.n * X.n) (foundAfter X X.m) ∧
                  KeptBut μ₂ μ' (hostAddr x.toTriInst X fr).x x.out (X.n * X.n))
                hl
                (allHostLoop_spec C.loop hp hq ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩
                  (hostMem_of hr hresid hclass)
                  (hostLay_of hr (hr.chunkCount_le hv.cap_pos)) hlim hF hd hf₂))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (Meets.of_body (Q := fun _ μ' =>
              FlagTable μ' x.out (X.n * X.n) (foundAfter X X.m) ∧
                KeptBut μ₂ μ' (hostAddr x.toTriInst X fr).x x.out (X.n * X.n))
              hl
              (allHostLoop_spec C.loop hp hq ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩
                (hostMem_of hr hresid hclass)
                (hostLay_of hr (hr.chunkCount_le hv.cap_pos)) hlim hF hd hf₂))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                allHostLoopArgs, hostLoopArgs, hostAddr, hmetaint, hmeta₂]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [allHostLoopArgs, hostLoopArgs, hostAddr, hmetaint, hmeta₂] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, allHostLoopArgs,
                hostLoopArgs, hostAddr, hmetaint, hmeta₂] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r μ₃ ⟨hf₃, hkept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨?_, fun c hc => ?_⟩
  · have hseg := hf₃.seg_outputFlags
    rw [outputFlags_eq hv, hn, hAB, hBC, hAC] at hseg
    exact hseg
  · exact (hkept c ⟨lt_of_lt_of_le hc.1 hfr, by simpa only [hn] using hc.2⟩).trans (hk c hc.1)

end APSPImprovement.AllEdges



end

section


namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

theorem tAllHostLoop_le {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}
    (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    tAllHostLoop Tn (hostData x D g) ≤ allHostLoopBound Tn x.n x.U D g := by
  have h := all_loop_time_le hpre hbig Tn
  convert h using 1
  unfold tAllHostLoop
  congr 1









end APSPImprovement.AllEdges



end

section


set_option maxHeartbeats 1500000

namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

theorem preparedPre_keep {x : AllEdgesInst} {μ μ' : ℕ → ℤ} {fr : ℕ}
    (h : preparedAllEdgesTask.Pre x μ fr) (hk : Kept μ μ' fr) :
    preparedAllEdgesTask.Pre x μ' fr := by
  obtain ⟨hp, hf, hfr, hm⟩ := h
  exact ⟨hp.keep (by intro a ha; exact hk a ha.1),
    hf.keep_below hk hp.belowOut, hfr, (hk _ (by omega)).trans hm⟩

open Light.Sec3.Et17 in
def allEt17Small (pBrute : ℕ) : Stmt :=
  .call pBrute [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, M (((Light.Expr.op Light.Op.sub) (v Free) (k 1))), v Free] 0

open Light.Sec3.Et17 in
def allEt17Body (ν : Et17Nums) (pAllLoop pBrute : ℕ) : Stmt :=
  (Light.Stmt.seq (et17Params ν)
    (.ite (Light.Cond.eq (v Small) (k 1)) (allEt17Small pBrute)
      (Light.Stmt.seq (et17Sizes ν) (allEt17Tables ν pAllLoop))))

theorem allEt17Small_spec {P : Program} {pBrute pScan : ℕ}
    (hBrute : P[pBrute]? = some (AllEdgesBrute.body pScan))
    (hScan : P[pScan]? = some scanBody)
    {lim : Limits} {d : ℕ} (x : AllEdgesInst) (μ : ℕ → ℤ) (fr D g a b : ℕ)
    {need : List ℕ → Need} (hpre : preparedAllEdgesTask.Pre x μ fr)
    (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim P d (allEt17Small pBrute) ⟨frame (et17LocA x.toTriInst fr D g), μ⟩
      (AllEdgesBrute.time x.n + 15)
      fun σ' => preparedAllEdgesTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨hpre, hf, hfr, hmeta⟩ := hpre
  have hbrute : (bruteNeed x.n x.U).Ok lim fr (d + 1) :=
    hok.mono (by simp only [bruteNeed, hostNeedAt, hostWord]; omega)
      (by simp only [bruteNeed]; omega) (by simp only [bruteNeed, hostNeedAt]; omega)
  have hd := hok.depth
  have hs := hok.cells
  have hw := hok.space
  have hmetaZ : (fr : ℤ) - 1 = ((fr - 1 : ℕ) : ℤ) := by omega
  unfold allEt17Small
  refine Ends.callTo (Meets.of_body hBrute (AllEdgesBrute.spec hScan x μ fr hpre hbrute))
    (fun _ _ h => h) (ha := ?_) (hd := by simp only [hostNeedAt] at hd; omega)
  (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, et17LocA, hmetaZ, hmeta] <;>
        omega))

theorem loopTime_le {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}
    (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    tAllHostLoop Tn (hostData x D g) ≤ allHostLoopBound Tn x.n x.U D g := by
  exact tAllHostLoop_le hpre hbig Tn

theorem allEt17_spec {P₀ R : Program} {ν : Et17Nums}
    {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ}
    (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    {pPair pQueries pAllLoop pBrute : ℕ}
    (hp : (P₀ ++ R)[pPair]? = some (scanPairBody ν.pScan))
    (hq : (P₀ ++ R)[pQueries]? = some (scanQueriesBody pPair))
    (hl : (P₀ ++ R)[pAllLoop]? = some (allHostLoopBody ν.pS ν.pWriteX ν.pWriteY pQueries))
    (hb : (P₀ ++ R)[pBrute]? = some (AllEdgesBrute.body ν.pScan))
    {lim : Limits} {d : ℕ} (x : AllEdgesInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : preparedAllEdgesTask.Pre x μ fr)
    (hok : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (allEt17Body ν pAllLoop pBrute)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩
      (allHostTime 100 Dfun Gfun tD tG Tn x.n x.U)
      fun σ' => preparedAllEdgesTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hparams := et17Params_spec C x.toTriInst μ fr hpre.1.toPre hok
  have hone : (1 : ℤ) ≤ lim.word := by
    have hword := hok.word
    simp only [hostNeed, hostNeedAt, hostWord] at hword
    omega
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr] 29]
  unfold hostNeed at hok
  unfold allEt17Body allHostTime hostTime hostSetup
  generalize Dfun x.n = D at *
  generalize Gfun D = g at *
  refine Ends.next _ (hparams.mono le_rfl ?_) (by omega)
  rintro _ rfl
  by_cases hs : SmallCase x.n D g
  · simp only [if_pos hs]
    exact Ends.iteLast
      (fun _ => (allEt17Small_spec hb C.loop.scan x μ fr D g _ _ hpre hok).mono
        (by simp [AllEdgesBrute.time, tBrute]; omega) fun _ h => h)
      (fun h => absurd (by simp [et17LocA, hs]) h) (by simp; omega)
  simp only [if_neg hs]
  refine Ends.iteLast (fun h => absurd h (by simp [et17LocA, hs])) (fun _ => ?_) (by simp; omega)
  have hbig := not_smallCase_iff.1 hs
  have htime := hostRunTime_le hpre.1.toPre hbig (fun _ => 0)
  have hlooptime := loopTime_le hpre.1.toPre hbig Tn
  have htabletime := allHostRunTime_le Tn (hostData x.toTriInst D g) x.U
  refine Ends.next _ ((et17Sizes_spec C x.toTriInst μ fr D g _ _ hpre.1.toPre hbig hok).mono
    le_rfl ?_) (by unfold hostMain; simp; omega)
  rintro _ ⟨μ', rfl, hk⟩
  refine (allEt17Tables_spec C hp hq hl x μ' fr D g _ _ (preparedPre_keep hpre hk) hbig hok).mono
    (by unfold hostMain; simp; omega) ?_
  rintro σ'' ⟨hflags, hk'⟩
  exact ⟨hflags, fun a ha => (hk' a ha).trans (hk a ha.1)⟩

def allEt17Extra (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [scanPairBody ν.pScan,
   scanQueriesBody (o + 29),
   allHostLoopBody pS ν.pWriteX ν.pWriteY (o + 30),
   AllEdgesBrute.body ν.pScan,
   allEt17Body ν (o + 31) (o + 32)]

def allEt17Procs (pS pD pG o : ℕ) : Program :=
  et17Procs pS pD pG o ++ allEt17Extra pS pD pG o

theorem extra_registration {P₀ R : Program} {pS pD pG i : ℕ} {s : Stmt}
    (h : (allEt17Extra pS pD pG P₀.length)[i]? = some s) :
    (P₀ ++ (allEt17Procs pS pD pG P₀.length ++ R))[P₀.length + 29 + i]? = some s := by
  have he : (et17Procs pS pD pG P₀.length).length = 29 := rfl
  simpa only [allEt17Procs, List.append_assoc, List.length_append, he] using
    (getElem?_append_append (P₀ := P₀ ++ et17Procs pS pD pG P₀.length) R h)

theorem allEt17_solves {P₀ : Program} {pS pD pG : ℕ}
    {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ}
    (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD)
    (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves preparedAllEdgesTask (P₀ ++ allEt17Procs pS pD pG P₀.length) (P₀.length + 33)
      (allHostTime 100 Dfun Gfun tD tG Tn) (hostNeed Dfun Gfun wD wG need) := by
  refine ⟨allEt17Body (et17NumsAt pS pD pG P₀.length) (P₀.length + 31) (P₀.length + 32),
    ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · simpa only [List.append_nil, Nat.add_assoc] using
      (extra_registration (P₀ := P₀) (R := []) (i := 4) (pS := pS) (pD := pD) (pG := pG) rfl)
  · rw [List.append_assoc]
    have C := et17Ctx_assembled hsol hD hG hpos (allEt17Extra pS pD pG P₀.length ++ R)
    rw [← List.append_assoc] at C
    apply allEt17_spec C (pPair := P₀.length + 29) (pQueries := P₀.length + 30)
      (pAllLoop := P₀.length + 31) (pBrute := P₀.length + 32)
    · simpa [Nat.add_assoc, allEt17Procs, et17NumsAt] using (extra_registration (R := R) (i := 0)
        (pS := pS) (pD := pD) (pG := pG) (P₀ := P₀) rfl)
    · simpa [Nat.add_assoc, allEt17Procs, et17NumsAt] using (extra_registration (R := R) (i := 1)
        (pS := pS) (pD := pD) (pG := pG) (P₀ := P₀) rfl)
    · simpa [Nat.add_assoc, allEt17Procs, et17NumsAt] using (extra_registration (R := R) (i := 2)
        (pS := pS) (pD := pD) (pG := pG) (P₀ := P₀) rfl)
    · simpa [Nat.add_assoc, allEt17Procs, et17NumsAt] using (extra_registration (R := R) (i := 3)
        (pS := pS) (pD := pD) (pG := pG) (P₀ := P₀) rfl)
    · exact hpre
    · exact hok

end APSPImprovement.AllEdges




end

section


@[expose] public section

namespace APSPImprovement

open Light ThreeSumApsp ThreeSumApsp.Spec

def transposeList (n : ℕ) (L : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => entry n L (q % n) (q / n)

@[simp] theorem transposeList_length (n : ℕ) (L : List ℤ) :
    (transposeList n L).length = n * n := by simp [transposeList]

theorem entry_transposeList {n i j : ℕ} {L : List ℤ} (hi : i < n) (hj : j < n) :
    entry n (transposeList n L) i j = entry n L j i := by
  rw [entry, transposeList, List.getD_map_range _ (Nat.mul_add_lt_mul hi hj),
    Nat.mul_add_div_of_lt hj, Nat.mul_add_mod_of_lt hj]

theorem transposeList_absLe {n : ℕ} {L : List ℤ} {U : ℤ}
    (hU : 0 ≤ U) (hL : AbsLe L U) : AbsLe (transposeList n L) U :=
  List.forall_mem_map.2 fun _ _ => AbsLe.abs_getD_le hU hL _

namespace ColumnCopy

abbrev Src : ℕ := 0
abbrev Dst : ℕ := 1
abbrev Side : ℕ := 2
abbrev Col : ℕ := 3
abbrev Idx : ℕ := 4

end ColumnCopy

open ColumnCopy in
/-- Copy one column of a square matrix to a contiguous row. -/
def columnCopyBody : Stmt :=
  pass Idx (v Side) (v Dst) (M (((Light.Expr.op Light.Op.add)
                                  ((Light.Expr.op Light.Op.add) (v Src)
                                    ((Light.Expr.op Light.Op.mul) (v Idx) (v Side)))
                                  (v Col))))

@[simp] def columnCopyTime (n : ℕ) : ℕ := 24 * n + 6

theorem columnCopy_meets {lim : Limits} {P : Program} {d p : ℕ}
    (hp : P[p]? = some columnCopyBody) {μ : ℕ → ℤ} {src dst n col : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n * n ≤ lim.space)
    (hdst : dst + n ≤ lim.space) (hcol : col < n)
    (hsep : Apart src (n * n) dst n) :
    Meets lim P p d [(src : ℤ), dst, n, col] μ (columnCopyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i * n + col)) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass (fun i => μ (src + i * n + col)) (fun i hi => ?_)
    ⟨fun i hi => wrote_done (f := fun i => μ (src + i * n + col)) hi, by ((try refine Light.SameOn.cell ?_);
                                                                              (intro apspMacro_627150_0 apspMacro_627150_1);
                                                                              (first
                                                                                |
                                                                                  ((((repeat
                                                                                            (((with_reducible
                                                                                                    rename Light.SameOn _ _ _ => apspMacro_627150_2));
                                                                                              ((try
                                                                                                    have :=
                                                                                                      apspMacro_627150_2 apspMacro_627150_0 (by omega)));
                                                                                              (revert apspMacro_627150_2)));
                                                                                        (intros);
                                                                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                    (omega))
                                                                                |
                                                                                  ((simp [] at apspMacro_627150_1);
                                                                                    (((repeat
                                                                                            (((with_reducible
                                                                                                    rename Light.SameOn _ _ _ => apspMacro_627150_3));
                                                                                              ((try
                                                                                                    have :=
                                                                                                      apspMacro_627150_3 apspMacro_627150_0 (by omega)));
                                                                                              (revert apspMacro_627150_3)));
                                                                                        (intros);
                                                                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                    (omega))
                                                                                |
                                                                                  ((((repeat
                                                                                            (((with_reducible
                                                                                                    rename Light.SameOn _ _ _ => apspMacro_627150_4));
                                                                                              ((try
                                                                                                    have :=
                                                                                                      apspMacro_627150_4 apspMacro_627150_0 (by omega)));
                                                                                              (revert apspMacro_627150_4)));
                                                                                        (intros);
                                                                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                    (fail
                                                                                        "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                  SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                  its condition K x does not follow from the hypotheses."))))⟩
    hw hdst rfl rfl (hT := by first
                              |
                                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                                      columnCopyTime]);
                                  (first
                                    | omega
                                    | ((ring_nf); (omega))))
                              | omega
                              |
                                (simp [columnCopyTime] <;>
                                    first
                                    | omega
                                    | ((ring_nf); (omega)))))
  have hidx : i * n + col < n * n := Nat.mul_add_lt_mul hi hcol
  have hidxZ : 0 ≤ (i : ℤ) * n ∧ (i : ℤ) * n + col < n * n := by
    exact_mod_cast And.intro (Nat.zero_le _) hidx
  have hread : wrote μ dst (fun i => μ (src + i * n + col)) i (src + i * n + col) =
      μ (src + i * n + col) := wrote_rest (by omega)
  have hreadZ : wrote μ dst (fun i => μ (src + i * n + col)) i
      ((src : ℤ) + i * n + col).toNat = μ (src + i * n + col) := by
    simpa only [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast] using hread
  (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadZ] <;> omega))

namespace Transpose

abbrev Src : ℕ := 0
abbrev Dst : ℕ := 1
abbrev Side : ℕ := 2
abbrev Row : ℕ := 3
abbrev Unused : ℕ := 4

def Inv (μ : ℕ → ℤ) (src dst n : ℕ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src, dst, n, i, r], μ'⟩ ∧
    (∀ q < i * n, μ' (dst + q) = (transposeList n L).getD q 0) ∧
    SameOutside μ μ' dst (n * n)

end Transpose

open Transpose in
def transposeBody (pColumn : ℕ) : Stmt :=
  .for Row (v Side) (
    .call pColumn [v Src, ((Light.Expr.op Light.Op.add) (v Dst)
                            ((Light.Expr.op Light.Op.mul) (v Row) (v Side))), v Side, v Row] Unused)

def transposeTime (n : ℕ) : ℕ := n * (24 * n + 40) + 6

open Transpose in
theorem transpose_meets {lim : Limits} {P : Program} {d p pColumn : ℕ}
    (hp : P[p]? = some (transposeBody pColumn)) (hColumn : P[pColumn]? = some columnCopyBody)
    {μ : ℕ → ℤ} {src dst n : ℕ} {L : List ℤ}
    (hL : Seg μ src L) (hlen : L.length = n * n)
    (hplace : src + n * n ≤ dst)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ dst + n * n ≤ lim.space ∧ d < lim.depth) :
    Meets lim P p d [(src : ℤ), dst, n] μ (transposeTime n) fun _ μ' =>
      Seg μ' dst (transposeList n L) ∧ SameOutside μ μ' dst (n * n) := by
  obtain ⟨hw, hdst, hd⟩ := hlim
  have hn2 : n ≤ n * n := Nat.le_mul_self n
  unfold transposeTime
  refine .of_body hp (Ends.for (Inv μ src dst n L) n (24 * n + 32)
    ?start ?round ?done ?bound)
  case start =>
    exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl,
      fun q hq => absurd hq (by omega), .refl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hrows, hrest⟩
    have hrowD : i * n + n ≤ n * n := Nat.mul_add_le_mul hi le_rfl
    have hrowZ : 0 ≤ (i : ℤ) * n ∧ (i : ℤ) * n + n ≤ n * n := by
      exact_mod_cast And.intro (Nat.zero_le _) hrowD
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (first
        |
          refine
            Light.Ends.callToThen
              ((columnCopy_meets hColumn (src := src) (dst := dst + i * n) (n := n)
                  hw (by omega) (by omega) hi (.inl (by omega)))
                _ (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            Light.Ends.callToThen
              (columnCopy_meets hColumn (src := src) (dst := dst + i * n) (n := n)
                hw (by omega) (by omega) hi (.inl (by omega)))
              ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (on_goal -1 =>
          ((rintro r' μ'' ⟨hcopy, hout⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    refine ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl,
      fun q hq => ?_, hrest.trans (hout.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge q (i * n) with hq' | hq'
    · exact (hout _ (.inl (by omega))).trans (hrows q hq')
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hq'
      have hj : j < n := by rw [Nat.add_mul, Nat.one_mul] at hq; omega
      have hidx : j * n + i < L.length := hlen ▸ Nat.mul_add_lt_mul hj hi
      rw [← Nat.add_assoc, hcopy j hj, hrest _ (.inl (by omega))]
      change μ (src + j * n + i) = entry n (transposeList n L) i j
      rw [entry_transposeList hi hj]
      change μ (src + j * n + i) = L.getD (j * n + i) 0
      rw [Nat.add_assoc]
      exact (hL _ hidx).trans (List.getD_eq_getElem _ _ hidx).symm
  case done =>
    rintro _ - ⟨r, μ', rfl, hrows, hrest⟩
    exact ⟨fun q hq => (hrows q (by simpa using hq)).trans (List.getD_eq_getElem _ _ hq), hrest⟩

end APSPImprovement




end
end

section


@[expose] public section

namespace APSPImprovement

open Light ThreeSumApsp ThreeSumApsp.Spec

theorem abZeroFlags_to_ac (n : ℕ) (AB BC AC : List ℤ) :
    abZeroFlags n AC (transposeList n BC) AB = acZeroFlags n AB BC AC := by
  unfold abZeroFlags acZeroFlags
  apply List.map_congr_left
  intro q hq
  have hq' : q < n * n := List.mem_range.1 hq
  have hn : 0 < n := by nlinarith
  have hc : q % n < n := Nat.mod_lt q hn
  apply flag_congr
  constructor
  · rintro ⟨b, hb, hs⟩
    change AC.getD q 0 + entry n (transposeList n BC) (q % n) b +
      AB.getD (q / n * n + b) 0 = 0 at hs
    rw [entry_transposeList hc hb] at hs
    exact ⟨b, hb, by dsimp [entry] at hs; omega⟩
  · rintro ⟨b, hb, hs⟩
    refine ⟨b, hb, ?_⟩
    change AC.getD q 0 + entry n (transposeList n BC) (q % n) b +
      AB.getD (q / n * n + b) 0 = 0
    rw [entry_transposeList hc hb]
    dsimp [entry]
    omega

namespace OrientAC




























































































end OrientAC














end APSPImprovement



end
end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace APSPImprovement

open ThreeSumApsp Light Light.Sec3

/-- The natural AB all-edges task at each fixed polynomial weight bound. The solver still
certifies every legal task input; only the asymptotic estimate is specialized. -/
def AllEdgesInPolylog (a : ℝ) : Prop :=
  Claim.SolvedAlongPow (SolvedIn allEdgesTask) UpperPowPolylog a























theorem solvedIn_time_nonneg {task : Task} {T : ℕ → ℝ → ℝ} (h : SolvedIn task T)
    {n : ℕ} {u : ℝ} (hn : 1 ≤ n) (hu : 1 ≤ u) : 0 ≤ T n u := by
  obtain ⟨P, p, Tn, r, hr, hs, ht⟩ := h
  exact (Nat.cast_nonneg (Tn n 1)).trans (ht n 1 u hn le_rfl (by simpa using hu))




















































/-- The all-edges version of the uniform Theorem 19 bound implies the exact
polylogarithmic interface consumed by the same-size reductions. -/
theorem allEdges_polylog_of_uniform {δ : ℝ} {e : ℕ}
    (h : ∃ K : ℝ, 1 ≤ K ∧ SolvedIn allEdgesTask (uniformTime K δ e)) :
    AllEdgesInPolylog (3 - δ) := by
  obtain ⟨K, _hK, hT⟩ := h
  intro κ hκ
  refine ⟨uniformTime K δ e, hT, ?_⟩
  have hwords := ((isPowPolylog_const 1).add
    (isPowPolylog_logU_mul_rpow (c := 1) (by norm_num) hκ)).pow 2
  have htotal := ((isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).mul hwords).const_mul K
  simpa only [uniformTime, one_mul, zero_mul, add_zero] using htotal.upperPowPolylog






















end APSPImprovement








end

section


@[expose] public section

namespace APSPImprovement

open Light ThreeSumApsp ThreeSumApsp.Spec

theorem abZeroFlags_to_bc (n : ℕ) (AB BC AC : List ℤ) :
    abZeroFlags n BC (transposeList n AC) (transposeList n AB) =
      bcZeroFlags n AB BC AC := by
  unfold abZeroFlags bcZeroFlags
  apply List.map_congr_left
  intro q hq
  have hq' : q < n * n := List.mem_range.1 hq
  have hn : 0 < n := by nlinarith
  have hc : q % n < n := Nat.mod_lt q hn
  have hb : q / n < n := (Nat.div_lt_iff_lt_mul hn).2 hq'
  apply flag_congr
  constructor
  · rintro ⟨a, ha, hs⟩
    change BC.getD q 0 + entry n (transposeList n AC) (q % n) a +
      entry n (transposeList n AB) (q / n) a = 0 at hs
    rw [entry_transposeList hc ha, entry_transposeList hb ha] at hs
    exact ⟨a, ha, by dsimp [entry] at hs; omega⟩
  · rintro ⟨a, ha, hs⟩
    refine ⟨a, ha, ?_⟩
    change BC.getD q 0 + entry n (transposeList n AC) (q % n) a +
      entry n (transposeList n AB) (q / n) a = 0
    rw [entry_transposeList hc ha, entry_transposeList hb ha]
    dsimp [entry]
    omega

namespace FullHost

abbrev Verts : ℕ := 0
abbrev Bound : ℕ := 1
abbrev MatAB : ℕ := 2
abbrev MatBC : ℕ := 3
abbrev MatAC : ℕ := 4
abbrev Out : ℕ := 5
abbrev Free : ℕ := 6
abbrev Res : ℕ := 7

def cells : Expr := ((Light.Expr.op Light.Op.mul) (v Verts) (v Verts))
def base (k' : ℕ) : Expr := ((Light.Expr.op Light.Op.add) (v Free)
                                ((Light.Expr.op Light.Op.mul) (k k') cells))
def output (k' : ℕ) : Expr := ((Light.Expr.op Light.Op.add) (v Out) ((Light.Expr.op Light.Op.mul) (k k') cells))

def body (pAB pTrans : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pTrans [v MatAB, base 0, v Verts] Res)
    (Light.Stmt.seq (.call pTrans [v MatBC, base 1, v Verts] Res)
      (Light.Stmt.seq (.call pTrans [v MatAC, base 2, v Verts] Res)
        (Light.Stmt.seq
          (.call pAB
            [v Verts, v Bound, v MatAB, v MatBC, v MatAC, output 0, base 3] Res)
          (Light.Stmt.seq
            (.call pAB
              [v Verts, v Bound, v MatBC, base 2, base 0, output 1, base 3] Res)
            (.call pAB
              [v Verts, v Bound, v MatAC, base 1, v MatAB, output 2, base 3]
              Res))))))

def time (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := 3 * transposeTime n + 3 * T n U + 400

def need (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := U + 3 + (r n U).word
  cells := 3 * (n * n) + (r n U).cells
  depth := (r n U).depth + 2

def questionAB (x : AllEdgesInst) : AllEdgesInst := x

def questionBC (x : AllEdgesInst) (fr : ℕ) : AllEdgesInst where
  n := x.n
  U := x.U
  ab := x.bc
  bc := fr + 2 * (x.n * x.n)
  ac := fr
  AB := x.BC
  BC := transposeList x.n x.AC
  AC := transposeList x.n x.AB
  out := x.out + x.n * x.n

def questionAC (x : AllEdgesInst) (fr : ℕ) : AllEdgesInst where
  n := x.n
  U := x.U
  ab := x.ac
  bc := fr + x.n * x.n
  ac := x.ab
  AB := x.AC
  BC := transposeList x.n x.BC
  AC := x.AB
  out := x.out + 2 * (x.n * x.n)

structure Mem (x : AllEdgesInst) (μ : ℕ → ℤ) (fr : ℕ) (μ' : ℕ → ℤ) : Prop where
  pre : x.FullPre μ' fr
  transAB : Seg μ' fr (transposeList x.n x.AB)
  transBC : Seg μ' (fr + x.n * x.n) (transposeList x.n x.BC)
  transAC : Seg μ' (fr + 2 * (x.n * x.n)) (transposeList x.n x.AC)
  kept : KeptBut μ μ' fr x.out (3 * (x.n * x.n))

theorem Mem.keep {x : AllEdgesInst} {μ μ' μ'' : ℕ → ℤ} {fr out : ℕ}
    (h : Mem x μ fr μ') (ho : x.out ≤ out ∧ out + x.n * x.n ≤ x.out + 3 * (x.n * x.n))
    (hk : KeptBut μ' μ'' (fr + 3 * (x.n * x.n)) out (x.n * x.n)) :
    Mem x μ fr μ'' := by
  have hp := h.pre
  (obtain ⟨⟩ := id hp.toPre)
  (obtain ⟨⟩ := id hp)
  refine ⟨hp.keep (by ((try refine Light.SameOn.cell ?_);
                          (intro apspMacro_636829_0 apspMacro_636829_1);
                          (first
                            |
                              ((((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ => apspMacro_636829_2));
                                          ((try
                                                have :=
                                                  apspMacro_636829_2 apspMacro_636829_0 (by omega)));
                                          (revert apspMacro_636829_2)));
                                    (intros);
                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                (omega))
                            |
                              ((simp [] at apspMacro_636829_1);
                                (((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ => apspMacro_636829_3));
                                          ((try
                                                have :=
                                                  apspMacro_636829_3 apspMacro_636829_0 (by omega)));
                                          (revert apspMacro_636829_3)));
                                    (intros);
                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                (omega))
                            |
                              ((((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ => apspMacro_636829_4));
                                          ((try
                                                have :=
                                                  apspMacro_636829_4 apspMacro_636829_0 (by omega)));
                                          (revert apspMacro_636829_4)));
                                    (intros);
                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                (fail
                                    "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                              SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                              its condition K x does not follow from the hypotheses."))))), h.transAB.keep, h.transBC.keep, h.transAC.keep, ?_⟩
  intro c ⟨hc, hout⟩
  exact (hk c ⟨by omega, by rcases hout with hl | hr <;> omega⟩).trans (h.kept c ⟨hc, hout⟩)

theorem preAB {x : AllEdgesInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.FullPre μ fr) :
    (questionAB x).Pre μ (fr + 3 * (x.n * x.n)) := by
  exact { h.abPre with
    toPre := h.toPre.mono (by omega)
    belowOut := by dsimp [questionAB]; have := h.belowOut; omega }

theorem preBC {x : AllEdgesInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : Mem x μ fr μ') :
    (questionBC x fr).Pre μ' (fr + 3 * (x.n * x.n)) := by
  have hp := h.pre
  (obtain ⟨⟩ := id hp.toPre)
  (obtain ⟨⟩ := id hp)
  refine {
    n_pos := hp.n_pos
    U_pos := hp.U_pos
    lenAB := hp.lenBC
    lenBC := by simp [questionBC]
    lenAC := by simp [questionBC]
    segAB := hp.segBC
    segBC := h.transAC
    segAC := h.transAB
    leAB := hp.leBC
    leBC := transposeList_absLe (by positivity) hp.leAC
    leAC := transposeList_absLe (by positivity) hp.leAB
    belowAB := by dsimp [questionBC]; omega
    belowBC := by dsimp [questionBC]; omega
    belowAC := by dsimp [questionBC]; omega
    belowOut := by dsimp [questionBC]; omega
    apartAB := by dsimp [questionBC, Apart]; rcases hp.apartBC with hl | hr <;> omega
    apartBC := .inr (by dsimp [questionBC]; omega)
    apartAC := .inr (by dsimp [questionBC]; omega) }

theorem preAC {x : AllEdgesInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : Mem x μ fr μ') :
    (questionAC x fr).Pre μ' (fr + 3 * (x.n * x.n)) := by
  have hp := h.pre
  (obtain ⟨⟩ := id hp.toPre)
  (obtain ⟨⟩ := id hp)
  refine {
    n_pos := hp.n_pos
    U_pos := hp.U_pos
    lenAB := hp.lenAC
    lenBC := by simp [questionAC]
    lenAC := hp.lenAB
    segAB := hp.segAC
    segBC := h.transBC
    segAC := hp.segAB
    leAB := hp.leAC
    leBC := transposeList_absLe (by positivity) hp.leBC
    leAC := hp.leAB
    belowAB := by dsimp [questionAC]; omega
    belowBC := by dsimp [questionAC]; omega
    belowAC := by dsimp [questionAC]; omega
    belowOut := by dsimp [questionAC]; omega
    apartAB := by dsimp [questionAC, Apart]; rcases hp.apartAC with hl | hr <;> omega
    apartBC := .inr (by dsimp [questionAC]; omega)
    apartAC := by dsimp [questionAC, Apart]; rcases hp.apartAB with hl | hr <;> omega }

theorem spec {P R : Program} {pAB pTrans pColumn : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} {lim : Limits} {d : ℕ} {x : AllEdgesInst}
    {μ : ℕ → ℤ} {fr : ℕ}
    (hsol : Solves allEdgesTask P pAB T r)
    (hTrans : (P ++ R)[pTrans]? = some (transposeBody pColumn))
    (hColumn : (P ++ R)[pColumn]? = some columnCopyBody)
    (hpre : x.FullPre μ fr) (hok : (need r x.n x.U).Ok lim fr d) :
    Ends lim (P ++ R) d (body pAB pTrans)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩ (time T x.n x.U)
      fun σ' => Seg σ'.mem x.out (fullZeroFlags x.n x.AB x.BC x.AC) ∧
        KeptBut μ σ'.mem fr x.out (3 * (x.n * x.n)) := by
  (obtain ⟨⟩ := id hpre.toPre)
  (obtain ⟨⟩ := id hpre)
  have hw := hok.word
  have hs := hok.cells
  have hd := hok.depth
  dsimp [need] at hw hs hd
  have hspace := hok.space
  have hn2 : x.n ≤ x.n * x.n := Nat.le_mul_self _
  have hsq : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  have hlower : (r x.n x.U).Ok lim (fr + 3 * (x.n * x.n)) (d + 1) :=
    ⟨by omega, by omega, hok.space, by omega⟩
  unfold body time
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((transpose_meets hTrans hColumn hpre.segAB hpre.lenAB hpre.belowAB
                ⟨hok.space, by omega, by omega⟩)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (transpose_meets hTrans hColumn hpre.segAB hpre.lenAB hpre.belowAB
              ⟨hok.space, by omega, by omega⟩)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, base,
                cells, output]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [base, cells, output] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, base, cells, output] <;>
              omega)));
    (on_goal -1 =>
        ((rintro a μ₁ ⟨hTAB, h₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hpre₁ : x.FullPre μ₁ fr := hpre.keep
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((transpose_meets hTrans hColumn hpre₁.segBC hpre₁.lenBC (dst :=
                fr + x.n * x.n) (by omega) ⟨hok.space, by omega, by omega⟩)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (transpose_meets hTrans hColumn hpre₁.segBC hpre₁.lenBC (dst :=
              fr + x.n * x.n) (by omega) ⟨hok.space, by omega, by omega⟩)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, base,
                cells, output]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [base, cells, output] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, base, cells, output] <;>
              omega)));
    (on_goal -1 =>
        ((rintro b μ₂ ⟨hTBC, h₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hpre₂ : x.FullPre μ₂ fr := hpre₁.keep
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((transpose_meets hTrans hColumn hpre₂.segAC hpre₂.lenAC (dst :=
                fr + 2 * (x.n * x.n)) (by omega) ⟨hok.space, by omega, by omega⟩)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (transpose_meets hTrans hColumn hpre₂.segAC hpre₂.lenAC (dst :=
              fr + 2 * (x.n * x.n)) (by omega) ⟨hok.space, by omega, by omega⟩)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, base,
                cells, output]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [base, cells, output] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, base, cells, output] <;>
              omega)));
    (on_goal -1 =>
        ((rintro c μ₃ ⟨hTAC, h₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hm₃ : Mem x μ fr μ₃ := ⟨hpre₂.keep, hTAB.keep, hTBC.keep, hTAC, by ((try refine Light.SameOn.cell ?_);
                                                                                      (intro apspMacro_641005_0 apspMacro_641005_1);
                                                                                      (first
                                                                                        |
                                                                                          ((((repeat
                                                                                                    (((with_reducible
                                                                                                            rename Light.SameOn _ _ _ => apspMacro_641005_2));
                                                                                                      ((try
                                                                                                            have :=
                                                                                                              apspMacro_641005_2 apspMacro_641005_0 (by omega)));
                                                                                                      (revert apspMacro_641005_2)));
                                                                                                (intros);
                                                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                            (omega))
                                                                                        |
                                                                                          ((simp [] at apspMacro_641005_1);
                                                                                            (((repeat
                                                                                                    (((with_reducible
                                                                                                            rename Light.SameOn _ _ _ => apspMacro_641005_3));
                                                                                                      ((try
                                                                                                            have :=
                                                                                                              apspMacro_641005_3 apspMacro_641005_0 (by omega)));
                                                                                                      (revert apspMacro_641005_3)));
                                                                                                (intros);
                                                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                            (omega))
                                                                                        |
                                                                                          ((((repeat
                                                                                                    (((with_reducible
                                                                                                            rename Light.SameOn _ _ _ => apspMacro_641005_4));
                                                                                                      ((try
                                                                                                            have :=
                                                                                                              apspMacro_641005_4 apspMacro_641005_0 (by omega)));
                                                                                                      (revert apspMacro_641005_4)));
                                                                                                (intros);
                                                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                            (fail
                                                                                                "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                          its condition K x does not follow from the hypotheses."))))⟩
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((hsol.meets R (questionAB x) (fr + 3 * (x.n * x.n)) (preAB hm₃.pre)
                hlower)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (hsol.meets R (questionAB x) (fr + 3 * (x.n * x.n)) (preAB hm₃.pre)
              hlower)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                allEdgesTask, questionAB, base, cells, output]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [allEdgesTask, questionAB, base, cells, output] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, allEdgesTask, questionAB,
                base, cells, output] <;>
              omega)));
    (on_goal -1 =>
        ((rintro e μ₄ ⟨hAB, h₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hm₄ : Mem x μ fr μ₄ := hm₃.keep (by dsimp [questionAB]; omega) h₄
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((hsol.meets R (questionBC x fr) (fr + 3 * (x.n * x.n)) (preBC hm₄)
                hlower)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (hsol.meets R (questionBC x fr) (fr + 3 * (x.n * x.n)) (preBC hm₄)
              hlower)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                allEdgesTask, questionAB, questionBC, base, cells, output]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [allEdgesTask, questionAB, questionBC, base, cells, output] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, allEdgesTask, questionAB,
                questionBC, base, cells, output] <;>
              omega)));
    (on_goal -1 =>
        ((rintro f μ₅ ⟨hBC, h₅⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hm₅ : Mem x μ fr μ₅ := hm₄.keep (by dsimp [questionBC]; omega) h₅
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((hsol.meets R (questionAC x fr) (fr + 3 * (x.n * x.n)) (preAC hm₅)
                hlower)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (hsol.meets R (questionAC x fr) (fr + 3 * (x.n * x.n)) (preAC hm₅)
              hlower)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                allEdgesTask, questionAB, questionBC, questionAC, base, cells,
                output]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [allEdgesTask, questionAB, questionBC, questionAC, base, cells,
                output] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, allEdgesTask, questionAB,
                questionBC, questionAC, base, cells, output] <;>
              omega)));
    (on_goal -1 =>
        ((rintro g μ₆ ⟨hAC, h₆⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hm₆ : Mem x μ fr μ₆ := hm₅.keep (by dsimp [questionAC]; omega) h₆
  change Seg μ₄ x.out (abZeroFlags x.n x.AB x.BC x.AC) at hAB
  change Seg μ₅ (x.out + x.n * x.n)
    (abZeroFlags x.n x.BC (transposeList x.n x.AC) (transposeList x.n x.AB)) at hBC
  change Seg μ₆ (x.out + 2 * (x.n * x.n))
    (abZeroFlags x.n x.AC (transposeList x.n x.BC) x.AB) at hAC
  rw [abZeroFlags_to_bc] at hBC
  rw [abZeroFlags_to_ac] at hAC
  dsimp [questionBC] at h₅
  dsimp [questionAC] at h₆
  have hAB₆ : Seg μ₆ x.out (abZeroFlags x.n x.AB x.BC x.AC) :=
    hAB.keep
  have hBC₆ : Seg μ₆ (x.out + x.n * x.n) (bcZeroFlags x.n x.AB x.BC x.AC) :=
    hBC.keep
  refine ⟨?_, hm₆.kept⟩
  rw [fullZeroFlags, seg_append, seg_append]
  exact ⟨⟨hAB₆, by simpa using hBC₆⟩, by simpa [two_mul, Nat.add_assoc] using hAC⟩

end FullHost

theorem polyNeed_fullHost {r : ℕ → ℕ → Need} (h : PolyNeed r) :
    PolyNeed (FullHost.need r) := by
  unfold FullHost.need
  (refine Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
      first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply h.word
                  | apply h.cells
                  | apply h.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply h.word
                                | apply h.cells
                                | apply h.depth
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply h.word
                          | apply h.cells
                          | apply h.depth
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply h.word
                  | apply h.cells
                  | apply h.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)))

theorem isHost_fullAllEdges : IsHost allEdgesTask fullAllEdgesTask FullHost.time FullHost.need := by
  refine ⟨fun P p T r hsol =>
    ⟨[columnCopyBody, transposeBody P.length, FullHost.body p (P.length + 1)],
      P.length + 2, FullHost.body p (P.length + 1), by simp,
      fun R lim d x μ fr hpre hok => ?_⟩, fun r => polyNeed_fullHost⟩
  rw [List.append_assoc]
  exact FullHost.spec (pColumn := P.length) hsol (by simp) (by simp) hpre hok

end APSPImprovement



end
end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace APSPImprovement

open ThreeSumApsp Light

/-- Three edge orientations and their quadratic matrix passes preserve the
all-edges exponent. The output contains all three Boolean flag matrices. -/
theorem fullAllEdges_polylog_of_allEdges {a : ℝ} (ha : 2 ≤ a)
    (h : AllEdgesInPolylog a) :
    Claim.SolvedAlongPow (SolvedIn fullAllEdgesTask) UpperPowPolylog a := by
  intro κ hκ
  obtain ⟨T, hT, hb⟩ := h κ hκ
  let Tpad : ℕ → ℝ → ℝ := fun n u => T n (max u 1) + (n : ℝ) ^ 2
  have hpad : SolvedIn allEdgesTask Tpad :=
    (Improvement.APSP.solvedIn_raiseMagnitude hT (fun _ => 1)).mono fun n u _ _ =>
      le_add_of_nonneg_right (sq_nonneg (n : ℝ))
  have hquad : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → (n : ℝ) ^ 2 ≤ Tpad n u := by
    intro n u hn
    exact le_add_of_nonneg_left (solvedIn_time_nonneg hT hn (le_max_right u 1))
  refine ⟨fun n u => 1000 * Tpad n u, ?_, ?_⟩
  · refine isHost_fullAllEdges.solvedIn hpad fun Tn hTn n U u hn hU hu => ?_
    have hτ := hTn n U u hn hU hu
    have hN := hquad n u hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    unfold FullHost.time transposeTime
    push_cast
    nlinarith
  · have hsq : UpperPowPolylog (fun n : ℕ => (n : ℝ) ^ 2) a :=
      ((isBigOPow_natCast_pow 2).isPowPolylog.mono ha).upperPowPolylog
    refine ((hb.add hsq).const_mul (by norm_num : (0 : ℝ) ≤ 1000)).mono_left ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hu := Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ
    dsimp [Tpad]
    rw [max_eq_left hu]

/-- The public all-edges milestone follows from the same single-orientation
uniform bound used for the min-plus and APSP milestones. -/
theorem mission_allEdges_of_uniform
    (h : ∃ K : ℝ, 1 ≤ K ∧ SolvedIn allEdgesTask (uniformTime K 0.00175 1)) :
    ∀ r : ℚ, 2.99825 < r →
      APSPExponentImprovement.AllEdgesExactTriangle.SolvedInTime r := by
  apply mission_allEdges_of_sourceClaim
  apply fullAllEdges_polylog_of_allEdges (by norm_num : (2 : ℝ) ≤ 2.99825)
  convert allEdges_polylog_of_uniform h using 1
  norm_num











end APSPImprovement





end

section


/-!
The all-edges extension of the Theorem 17 host is instantiated with the same
Corollary 26 parameter routines as the source formalization. The per-pair flag
table limits successful verification scans to n²; false-positive scans retain
the source bound. This module closes the actual program proof and its running
time analysis, then applies the verified same-size reductions.
-/

namespace APSPImprovement.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

theorem prepared26_solves
    (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need)
    (_hr : PolyNeedN r) (hs : SolvesN lopDetectTask Q pS Tn r) :
    ∃ (R : Program) (p' : ℕ),
      Solves preparedAllEdgesTask (Q ++ R) p' (allEdges26Time Tn) (allEdges26Need r) := by
  have h := allEt17_solves (P₀ := Q ++ Parameters.paramProcs Q.length)
    (hs.append _) (Parameters.paramProc_d26 Q) (Parameters.paramProc_g26 Q)
    (fun _ hn => one_le_paramD₂₆Nat hn)
  rw [List.append_assoc] at h
  exact ⟨_, _, h⟩

/-- The actual all-edges host satisfies Theorem 17 at the Corollary 26 parameters. -/
theorem claim_theorem_17_allEdges :
    Claim.Theorem_17 allEdgesModel strassen paramD₂₆ paramG₂₆ :=
  claim17_from_prepared26 prepared26_solves

/-- A deterministic all-edges Exact Triangle solver with the full 0.00175 saving. -/
theorem uniform_allEdges :
    ∃ K : ℝ, 1 ≤ K ∧ SolvedIn allEdgesTask (uniformTime K 0.00175 1) :=
  uniform_from_host claim_theorem_17_allEdges










end APSPImprovement.AllEdges






end

section


theorem APSPExponentImprovement.allEdgesExactTriangle_sourceProof :
    ∀ r : Rat, 2.99825 < r →
      APSPExponentImprovement.AllEdgesExactTriangle.SolvedInTime r :=
  APSPImprovement.mission_allEdges_of_uniform APSPImprovement.AllEdges.uniform_allEdges














end


theorem solution : ∀ (r : Rat),
  @LT.lt.{0} Rat Rat.instLT
      (@OfScientific.ofScientific.{0} Rat Rat.instOfScientific (nat_lit 299825) Bool.true (nat_lit 5)) r →
    APSPExponentImprovement.AllEdgesExactTriangle.SolvedInTime r := by
  exact @APSPExponentImprovement.allEdgesExactTriangle_sourceProof

#print axioms solution
