-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library05
-- name    : CH_ConstructibleAC_Library05
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:05:49.400214+00:00
-- url     : https://prove2.me/theorems/10282851-872e-4aeb-a67d-270be3866954
-- title:
--   Compiling set operations into programs
-- statement:
--   A finite composition of elementary set operations can be compiled into a rudimentary program. This library supplies the compiler data and the constructor proofs needed to relate its output to evaluation. It connects the simple-operation and rudimentary descriptions of definability and introduces the stack programs used for internal set-theoretic coding.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/SimpleComposition.lean#L1-L159; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/SimpleTerms.lean#L1-L140; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/SimpleCompiler.lean#L1-L301; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/SimpleGenerated.lean#L1-L134; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/SimpleF3F4.lean#L1-L234; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/SimpleF6F8.lean#L1-L296; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Equivalence.lean#L1-L70; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryConstructible.lean#L1-L168; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackProgram.lean#L1-L238

import Definitions.Def_CH_ConstructibleAC_Library04
import Definitions.Def_CH_Constructible
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Sum.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic.FinCases

/-!
# Adaptation of Zike Liu's constructible-universe Choice proof

Original formalization: Copyright (c) 2026 Zike Liu, Apache-2.0.
Source: https://github.com/05-02-07/lean-constructible-universe
Commit: 7f5a7d03d63d9769172f17350bbe8303996e5b53.
All original per-file copyright notices are retained below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

This credit concerns the Prove2Me adaptation and semantic bridge. The original
well-ordering formalization is by Zike Liu, credited above and in each source section.
-/

set_option autoImplicit false


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleComposition -/
section CUAdapterModule19
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Composition of simple set functions

This file proves that strong simplicity is preserved by unary and binary composition. The tuple
renamings below arrange arguments and intermediate values for the corresponding bounded formulas.
-/


universe u

namespace Constructible.Godel

/-- Move the distinguished value immediately following the argument block to
the front, leaving the trailing context in place. -/
def rotateAfterArgs (n k : Nat) : Fin (n + (1 + k)) → Fin (1 + (n + k)) :=
  fun i => Fin.addCases
    (fun j : Fin n => Fin.natAdd 1 (Fin.castAdd k j))
    (fun j : Fin (1 + k) => Fin.addCases
      (fun _ : Fin 1 => (0 : Fin (1 + (n + k))))
      (fun l : Fin k =>
        Fin.natAdd 1 (Fin.natAdd n l)) j) i

theorem addCases_comp_rotateAfterArgs {A : Type u} (n k : Nat)
    (args : Tuple A n) (value : A) (extra : Tuple A k) :
    (fun i =>
      Fin.addCases (fun _ : Fin 1 => value) (Fin.addCases args extra)
        (rotateAfterArgs n k i)) =
      Fin.addCases args (Fin.addCases (fun _ : Fin 1 => value) extra) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [rotateAfterArgs]
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro l
      fin_cases l
      simp only [rotateAfterArgs, Fin.addCases_right, Fin.addCases_left]
      change Fin.addCases
          (fun _ : Fin 1 => value)
          (fun i : Fin (n + k) => Fin.addCases args extra i)
          (Fin.castAdd (n + k) (0 : Fin 1)) = value
      simpa only [] using
        (Fin.addCases_left
          (motive := fun _ => A)
          (left := fun _ : Fin 1 => value)
          (right := fun i : Fin (n + k) =>
            Fin.addCases (motive := fun _ => A) args extra i)
          (0 : Fin 1))
    · intro l
      simp only [rotateAfterArgs, Fin.addCases_right]

/-- Identify two consecutive copies of the same argument tuple. -/
def diagonalRename (n k : Nat) : Fin (n + (n + k)) → Fin (n + k) :=
  Fin.addCases (fun i => Fin.castAdd k i) (fun i => i)

theorem addCases_comp_diagonalRename {A : Type u} (n k : Nat)
    (args : Tuple A n) (extra : Tuple A k) :
    (fun i : Fin (n + (n + k)) =>
      Fin.addCases (motive := fun _ => A) args extra
        (diagonalRename n k i)) =
      (fun i : Fin (n + (n + k)) =>
        Fin.addCases (motive := fun _ => A) args
          (fun j : Fin (n + k) =>
            Fin.addCases (motive := fun _ => A) args extra j) i) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · simp only [diagonalRename, Fin.addCases_left]
  · simp only [diagonalRename, Fin.addCases_right]

/-- The two-component tuple formed by two set-valued functions. -/
def binaryTuple {n : Nat}
    (f g : Tuple ZFSet.{u} n → ZFSet.{u})
    (args : Tuple ZFSet.{u} n) : Tuple ZFSet.{u} 2 :=
  fun i => Fin.cases (f args) (fun _ => g args) i

/-- Reassociate a two-coordinate output followed by a context. -/
def unflattenPairContext (k : Nat) : Fin (2 + k) → Fin (1 + (1 + k)) :=
  fun i => Fin.addCases
    (fun j : Fin 2 => Fin.cases 0
      (fun _ : Fin 1 => Fin.natAdd 1 (0 : Fin (1 + k))) j)
    (fun l : Fin k => Fin.natAdd 1 (Fin.natAdd 1 l)) i

theorem nested_comp_unflattenPairContext {n k : Nat}
    (f g : Tuple ZFSet.{u} n → ZFSet.{u})
    (args : Tuple ZFSet.{u} n) (extra : Tuple ZFSet.{u} k) :
    (fun i : Fin (2 + k) =>
      Fin.addCases (fun _ : Fin 1 => f args)
        (fun j : Fin (1 + k) =>
          Fin.addCases (fun _ : Fin 1 => g args) extra j)
        (unflattenPairContext k i)) =
      Fin.addCases (binaryTuple f g args) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Fin.addCases_left]
      change Fin.addCases
          (fun _ : Fin 1 => f args)
          (fun j : Fin (1 + k) =>
            Fin.addCases (fun _ : Fin 1 => g args) extra j)
          (Fin.castAdd (1 + k) (0 : Fin 1)) = f args
      exact Fin.addCases_left (0 : Fin 1)
    · simp only [Fin.mk_one, Fin.isValue, Fin.addCases_left]
      change Fin.addCases
          (fun _ : Fin 1 => f args)
          (fun j : Fin (1 + k) =>
            Fin.addCases (fun _ : Fin 1 => g args) extra j)
          (Fin.natAdd 1 (0 : Fin (1 + k))) = g args
      exact (Fin.addCases_right (0 : Fin (1 + k))).trans
        (Fin.addCases_left (0 : Fin 1))
  · intro j
    simp only [unflattenPairContext, Fin.addCases_right]

/-- Two simple functions can be substituted simultaneously as a two-tuple. -/
theorem IsSimpleSetFunction.binaryTuple {n : Nat}
    {f g : Tuple ZFSet.{u} n → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) (hg : IsSimpleSetFunction g) :
    IsSimpleTupleMap (binaryTuple f g) := by
  intro k phi
  let nestedPhi : Delta0Formula (1 + (1 + k)) :=
    Delta0Formula.rename (unflattenPairContext k) phi
  rcases hf (1 + k) nestedPhi with ⟨afterF, hafterF⟩
  let rotated : Delta0Formula (1 + (n + k)) :=
    Delta0Formula.rename (rotateAfterArgs n k) afterF
  rcases hg (n + k) rotated with ⟨afterG, hafterG⟩
  refine ⟨Delta0Formula.rename (diagonalRename n k) afterG, ?_⟩
  intro args extra
  rw [Delta0Formula.satisfies_rename,
    addCases_comp_diagonalRename]
  rw [hafterG args (Fin.addCases args extra)]
  simp only [rotated, Delta0Formula.satisfies_rename,
    addCases_comp_rotateAfterArgs]
  rw [hafterF args
    (Fin.addCases (fun _ : Fin 1 => g args) extra)]
  simp only [nestedPhi, Delta0Formula.satisfies_rename]
  rw [nested_comp_unflattenPairContext]

/-- Binary composition of simple set functions. -/
theorem IsSimpleSetFunction.compBinary {n : Nat}
    {outer : Tuple ZFSet.{u} 2 → ZFSet.{u}}
    {left right : Tuple ZFSet.{u} n → ZFSet.{u}}
    (hOuter : IsSimpleSetFunction outer)
    (hLeft : IsSimpleSetFunction left)
    (hRight : IsSimpleSetFunction right) :
    IsSimpleSetFunction
      (fun args => outer
        (_root_.Constructible.Godel.binaryTuple left right args)) :=
  hOuter.compTuple (IsSimpleSetFunction.binaryTuple hLeft hRight)

end Constructible.Godel
end CUAdapterModule19



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleTerms -/
section CUAdapterModule20
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Simplicity of rudimentary terms

This file lifts simplicity from the basic Gödel operations to arbitrary finite rudimentary terms
and reifies their parameters over an internal carrier.
-/


universe u

namespace Constructible.Godel

/-- Each coordinate projection is simple. -/
theorem isSimpleSetFunction_projection {n : Nat} (i : Fin n) :
    IsSimpleSetFunction
      (fun args : Tuple ZFSet.{u} n => args i) := by
  simpa only [IsSimpleSetFunction, IsSimpleTupleMap] using
    (isSimpleTupleMap_projection
      (fun _ : Fin 1 => i))

/-- If all nine basic operations are simple, every finite rudimentary term is
simple.  This is the composition step needed independently of reification. -/
theorem RudimentaryTerm.isSimple_eval
    (hop : ∀ i : Fin 9,
      IsSimpleSetFunction
        (fun s : Tuple ZFSet.{u} 2 => op i (s 0) (s 1)))
    {n : Nat} (t : RudimentaryTerm (Fin n)) :
    IsSimpleSetFunction
      (fun args : Tuple ZFSet.{u} n => RudimentaryTerm.eval args t) := by
  induction t with
  | var i =>
      exact isSimpleSetFunction_projection i
  | app i left right hleft hright =>
      have h := (hop i).compBinary hleft hright
      have hOne : (1 : Fin 2) = Fin.succ 0 := by rfl
      simpa only [RudimentaryTerm.eval, binaryTuple, hOne,
        Fin.cases_zero, Fin.cases_succ] using h

/-- Replace every occurrence of the universe generator by coordinate zero and
every genuine set parameter by its corresponding following coordinate. -/
def reificationIndex {U : ZFSet.{u}} {n : Nat}
    (labels : Tuple (Option (ZFCarrier U)) n) : Fin n → Fin (n + 1) :=
  fun i => match labels i with
    | none => 0
    | some _ => i.succ

/-- Fill the otherwise-unused parameter slots of universe occurrences by a
fixed genuine member of `U`. -/
def reificationParams {U : ZFSet.{u}} {n : Nat}
    (default : ZFCarrier U)
    (labels : Tuple (Option (ZFCarrier U)) n) :
    Tuple (ZFCarrier U) n :=
  fun i => match labels i with
    | none => default
    | some x => x

theorem tupleCons_reificationIndex {U : ZFSet.{u}} {n : Nat}
    (default : ZFCarrier U)
    (labels : Tuple (Option (ZFCarrier U)) n) :
    (fun i =>
      tupleCons U (Delta0Formula.val (reificationParams default labels))
        (reificationIndex labels i)) =
      rudimentaryGenerator U ∘ labels := by
  funext i
  simp only [Function.comp_apply]
  cases hlabel : labels i with
  | none =>
      simp [reificationIndex, hlabel, rudimentaryGenerator]
  | some x =>
      simp [reificationIndex, reificationParams, hlabel,
        rudimentaryGenerator]

/-- A finitely reified term over `U ∪ {U}` can be applied to `U` and genuine
parameters from `U` through the strong simplicity bridge. -/
theorem finiteReification_mem_DefZF
    (hop : ∀ i : Fin 9,
      IsSimpleSetFunction
        (fun s : Tuple ZFSet.{u} 2 => op i (s 0) (s 1)))
    {U z : ZFSet.{u}} (hU : U.IsTransitive)
    (default : ZFCarrier U) (hzU : z ⊆ U)
    (t : RudimentaryClosureTerm U) (ht : t.eval = z) :
    z ∈ Constructible.DefZF U := by
  rcases RudimentaryTerm.exists_finiteReification t with
    ⟨n, labels, body, hbody⟩
  let params : Tuple (ZFCarrier U) n :=
    reificationParams default labels
  let renamed : RudimentaryTerm (Fin (n + 1)) :=
    body.rename (reificationIndex labels)
  let f : Tuple ZFSet.{u} (n + 1) → ZFSet.{u} :=
    fun args => RudimentaryTerm.eval args renamed
  have hf : IsSimpleSetFunction f := by
    exact RudimentaryTerm.isSimple_eval hop renamed
  have heval :
      f (tupleCons U (Delta0Formula.val params)) = z := by
    simp only [f, renamed, RudimentaryTerm.eval_rename]
    have hassign :
        tupleCons U (Delta0Formula.val params) ∘
            reificationIndex labels =
          rudimentaryGenerator U ∘ labels := by
      change
        (fun i => tupleCons U (Delta0Formula.val params)
          (reificationIndex labels i)) = rudimentaryGenerator U ∘ labels
      simpa only [params] using
        (tupleCons_reificationIndex default labels)
    rw [hassign]
    rw [hbody (rudimentaryGenerator U)]
    exact ht
  have hsub : f (tupleCons U (Delta0Formula.val params)) ⊆ U := by
    simpa only [heval] using hzU
  have hmem := hf.mem_DefZF_withUniverse hU params hsub
  simpa only [heval] using hmem

/-- The hard inclusion, conditional only on the nine primitive simplicity
lemmas.  The empty carrier is discharged by the previously proved exact base
case; a nonempty carrier supplies the harmless filler used by reification. -/
theorem godelDef_subset_DefZF_of_simpleOps
    (hop : ∀ i : Fin 9,
      IsSimpleSetFunction
        (fun s : Tuple ZFSet.{u} 2 => op i (s 0) (s 1)))
    {U : ZFSet.{u}} (hU : U.IsTransitive) :
    godelDef U ⊆ Constructible.DefZF U := by
  rcases ZFSet.eq_empty_or_nonempty U with rfl | hnonempty
  · rw [← DefZF_eq_godelDef_empty]
  · rcases hnonempty with ⟨default, hdefault⟩
    intro z hz
    rcases mem_godelDef_iff_exists_rudimentaryTerm.mp hz with
      ⟨hzU, t, ht⟩
    exact finiteReification_mem_DefZF hop hU
      ⟨default, hdefault⟩ hzU t ht

end Constructible.Godel
end CUAdapterModule20



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleCompiler -/
section CUAdapterModule21
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Compiling simple set functions

This file packages the data needed to eliminate a binary set-valued operation from bounded
formulas and proves the generic correctness lemmas for that elimination procedure.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n m k : Nat}

/-- Data sufficient to eliminate one binary set-valued operation from every
bounded context.  `boundAt` is the only operation-specific higher-order
clause; membership and graph formulas handle all atomic occurrences. -/
structure SimpleValueSpec where
  /-- The binary set operation represented by this specification. -/
  eval : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  /-- A bounded formula for membership in the operation's value. -/
  memAt : {n : Nat} → Fin n → Fin n → Fin n → Delta0Formula n
  /-- A bounded formula for equality with the operation's value. -/
  eqAt : {n : Nat} → Fin n → Fin n → Fin n → Delta0Formula n
  /-- Eliminate a bounded quantifier over the operation's value. -/
  boundAt : {n : Nat} → Fin n → Fin n →
    Delta0Formula (n + 1) → Delta0Formula n
  satisfies_memAt : ∀ {n : Nat} (q x y : Fin n)
    (s : Tuple ZFSet.{u} n),
    Satisfies ZFMem (memAt q x y) s ↔ s q ∈ eval (s x) (s y)
  satisfies_eqAt : ∀ {n : Nat} (out x y : Fin n)
    (s : Tuple ZFSet.{u} n),
    Satisfies ZFMem (eqAt out x y) s ↔ s out = eval (s x) (s y)
  satisfies_boundAt : ∀ {n : Nat} (x y : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n),
    Satisfies ZFMem (boundAt x y body) s ↔
      ∃ z ∈ eval (s x) (s y), Satisfies ZFMem body (snoc s z)

/-- An expression is either a target variable or the one distinguished value
described by a `SimpleValueSpec`. -/
inductive ValueExpr (n : Nat)
  | var (i : Fin n)
  | value (left right : Fin n)

namespace ValueExpr

/-- Evaluate a value expression in an assignment. -/
def eval (spec : SimpleValueSpec.{u}) (s : Tuple ZFSet.{u} n) :
    ValueExpr n → ZFSet.{u}
  | .var i => s i
  | .value i j => spec.eval (s i) (s j)

/-- Rename the variables in a value expression. -/
def rename (ρ : Fin n → Fin m) : ValueExpr n → ValueExpr m
  | .var i => .var (ρ i)
  | .value i j => .value (ρ i) (ρ j)

@[simp]
theorem eval_rename (spec : SimpleValueSpec.{u})
    (ρ : Fin n → Fin m) (s : Tuple ZFSet.{u} m) (e : ValueExpr n) :
    (e.rename ρ).eval spec s = e.eval spec (fun i => s (ρ i)) := by
  cases e <;> rfl

/-- Any two structured expressions in a valid substitution are the same
distinguished value. -/
def Compatible : ValueExpr n → ValueExpr n → Prop
  | .value x y, .value x' y' => x = x' ∧ y = y'
  | _, _ => True

theorem compatible_rename (ρ : Fin n → Fin m)
    {left right : ValueExpr n} (h : left.Compatible right) :
    (left.rename ρ).Compatible (right.rename ρ) := by
  cases left <;> cases right
  · trivial
  · trivial
  · trivial
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end ValueExpr

/-- Compatibility of all value expressions in a simultaneous substitution. -/
def ValueSubstCompatible {m n : Nat} (σ : Fin m → ValueExpr n) : Prop :=
  ∀ i j, (σ i).Compatible (σ j)

/-- Compile membership between two compatible value expressions. -/
def memValueExpr (spec : SimpleValueSpec.{u}) {n : Nat} :
    ValueExpr n → ValueExpr n → Delta0Formula n
  | .var a, .var b => .mem a b
  | .var a, .value x y => spec.memAt a x y
  | .value x y, .var a =>
      .boundedEx a (spec.eqAt (Fin.last n) x.castSucc y.castSucc)
  | .value x _, .value _ _ => .neg (.eq x x)

/-- Compile equality between two compatible value expressions. -/
def eqValueExpr (spec : SimpleValueSpec.{u}) {n : Nat} :
    ValueExpr n → ValueExpr n → Delta0Formula n
  | .var a, .var b => .eq a b
  | .var a, .value x y => spec.eqAt a x y
  | .value x y, .var a => spec.eqAt a x y
  | .value x _, .value _ _ => .eq x x

@[simp]
theorem satisfies_memValueExpr (spec : SimpleValueSpec.{u}) {n : Nat}
    (left right : ValueExpr n) (h : left.Compatible right)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memValueExpr spec left right) s ↔
      left.eval spec s ∈ right.eval spec s := by
  cases left with
  | var a =>
      cases right with
      | var b => rfl
      | value x y => exact spec.satisfies_memAt a x y s
  | value x y =>
      cases right with
      | var a =>
          simp only [memValueExpr, Satisfies, spec.satisfies_eqAt,
            ValueExpr.eval, snoc_last, snoc_castSucc]
          constructor
          · rintro ⟨z, hz, heq⟩
            simpa [heq] using hz
          · intro hmem
            exact ⟨spec.eval (s x) (s y), hmem, rfl⟩
      | value x' y' =>
          rcases h with ⟨rfl, rfl⟩
          simp [memValueExpr, ValueExpr.eval, ZFSet.mem_irrefl]

@[simp]
theorem satisfies_eqValueExpr (spec : SimpleValueSpec.{u}) {n : Nat}
    (left right : ValueExpr n) (h : left.Compatible right)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eqValueExpr spec left right) s ↔
      left.eval spec s = right.eval spec s := by
  cases left <;> cases right
  · rfl
  · exact spec.satisfies_eqAt _ _ _ s
  · exact (spec.satisfies_eqAt _ _ _ s).trans eq_comm
  · rcases h with ⟨rfl, rfl⟩
    simp [eqValueExpr, ValueExpr.eval]

/-- Lift a value-expression substitution through one binder. -/
def liftValueSubst {m n : Nat} (σ : Fin m → ValueExpr n) :
    Fin (m + 1) → ValueExpr (n + 1) :=
  Fin.lastCases (.var (Fin.last n))
    (fun i => (σ i).rename Fin.castSucc)

theorem eval_liftValueSubst (spec : SimpleValueSpec.{u}) {m n : Nat}
    (σ : Fin m → ValueExpr n) (s : Tuple ZFSet.{u} n)
    (z : ZFSet.{u}) :
    (fun i => (liftValueSubst σ i).eval spec (snoc s z)) =
      snoc (fun i => (σ i).eval spec s) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftValueSubst, ValueExpr.eval]
  · cases h : σ j <;>
      simp [liftValueSubst, ValueExpr.eval, ValueExpr.rename, h]

theorem valueSubstCompatible_lift {m n : Nat}
    {σ : Fin m → ValueExpr n} (hσ : ValueSubstCompatible σ) :
    ValueSubstCompatible (liftValueSubst σ) := by
  intro i j
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [liftValueSubst, ValueExpr.Compatible]
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [liftValueSubst, ValueExpr.Compatible]
    · simpa [liftValueSubst] using
        (ValueExpr.compatible_rename Fin.castSucc (hσ i' j'))

/-- Uniform arbitrary-context compiler from a `SimpleValueSpec`. -/
def compileValueSubst (spec : SimpleValueSpec.{u}) {m n : Nat}
    (σ : Fin m → ValueExpr n) : Delta0Formula m → Delta0Formula n
  | .mem i j => memValueExpr spec (σ i) (σ j)
  | .eq i j => eqValueExpr spec (σ i) (σ j)
  | .neg φ => .neg (compileValueSubst spec σ φ)
  | .conj φ ψ =>
      .conj (compileValueSubst spec σ φ) (compileValueSubst spec σ ψ)
  | .boundedEx i φ =>
      match σ i with
      | .var bound =>
          .boundedEx bound
            (compileValueSubst spec (liftValueSubst σ) φ)
      | .value left right =>
          spec.boundAt left right
            (compileValueSubst spec (liftValueSubst σ) φ)

@[simp]
theorem satisfies_compileValueSubst (spec : SimpleValueSpec.{u})
    {m n : Nat} (σ : Fin m → ValueExpr n)
    (hσ : ValueSubstCompatible σ) (φ : Delta0Formula m)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (compileValueSubst spec σ φ) s ↔
      Satisfies ZFMem φ (fun i => (σ i).eval spec s) := by
  induction φ generalizing n with
  | mem i j =>
      exact satisfies_memValueExpr spec (σ i) (σ j) (hσ i j) s
  | eq i j =>
      exact satisfies_eqValueExpr spec (σ i) (σ j) (hσ i j) s
  | neg φ ih => simp [compileValueSubst, ih σ hσ]
  | conj φ ψ ihφ ihψ =>
      simp [compileValueSubst, ihφ σ hσ, ihψ σ hσ]
  | boundedEx i φ ih =>
      cases hbound : σ i with
      | var bound =>
          simp only [compileValueSubst, hbound, Satisfies]
          constructor
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [ValueExpr.eval, hbound] using hz
            · rw [ih (liftValueSubst σ)
                (valueSubstCompatible_lift hσ)] at hφ
              simpa only [eval_liftValueSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [ValueExpr.eval, hbound] using hz
            · rw [ih (liftValueSubst σ)
                (valueSubstCompatible_lift hσ)]
              simpa only [eval_liftValueSubst] using hφ
      | value left right =>
          rw [compileValueSubst, hbound, spec.satisfies_boundAt]
          constructor
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [ValueExpr.eval, hbound] using hz
            · rw [ih (liftValueSubst σ)
                (valueSubstCompatible_lift hσ)] at hφ
              simpa only [eval_liftValueSubst] using hφ
          · rintro ⟨z, hz, hφ⟩
            refine ⟨z, ?_, ?_⟩
            · simpa [ValueExpr.eval, hbound] using hz
            · rw [ih (liftValueSubst σ)
                (valueSubstCompatible_lift hσ)]
              simpa only [eval_liftValueSubst] using hφ

/-- The substitution placing one binary value before the remaining context. -/
def valueContextSubst (k : Nat) : Fin (1 + k) → ValueExpr (2 + k) :=
  Fin.addCases
    (fun _ => .value
      (Fin.castAdd k (0 : Fin 2)) (Fin.castAdd k (1 : Fin 2)))
    (fun i => .var (Fin.natAdd 2 i))

theorem valueContextSubst_compatible (k : Nat) :
    ValueSubstCompatible (valueContextSubst k) := by
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    fin_cases a
    refine Fin.addCases ?_ ?_ j
    · intro b
      fin_cases b
      exact ⟨rfl, rfl⟩
    · intro b
      simp [valueContextSubst, ValueExpr.Compatible]
  · intro a
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp [valueContextSubst, ValueExpr.Compatible]
    · intro b
      simp [valueContextSubst, ValueExpr.Compatible]

theorem eval_valueContextSubst (spec : SimpleValueSpec.{u})
    (x y : ZFSet.{u}) (extra : Tuple ZFSet.{u} k) :
    (fun i => (valueContextSubst k i).eval spec
      (Fin.addCases ![x, y] extra)) =
      Fin.addCases (fun _ : Fin 1 => spec.eval x y) extra := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    rfl
  · intro j
    simp [valueContextSubst, ValueExpr.eval]

theorem SimpleValueSpec.isSimple (spec : SimpleValueSpec.{u}) :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => spec.eval (s 0) (s 1)) := by
  intro k φ
  refine ⟨compileValueSubst spec (valueContextSubst k) φ, ?_⟩
  intro args extra
  rw [satisfies_compileValueSubst spec _
    (valueContextSubst_compatible k)]
  have hargs : args = ![args 0, args 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hargs, eval_valueContextSubst]
  simp

end Constructible.Godel
end CUAdapterModule21



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleGenerated -/
section CUAdapterModule22
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Generated bounded formulas for simple set functions

This file derives reusable elimination formulas from `SimpleValueSpec` and proves the resulting
strong-simplicity theorem for ternary membership descriptions.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}

/-- Place the uniform graph formula for an operation at arbitrary
coordinates. -/
def opEqAt (i : Fin 9) {n : Nat} (out x y : Fin n) :
    Delta0Formula n :=
  Delta0Formula.rename ![out, x, y] (opGraphFormula i)

@[simp]
theorem satisfies_opEqAt (i : Fin 9) {n : Nat}
    (out x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (opEqAt i out x y) s ↔
      s out = op i (s x) (s y) := by
  rw [opEqAt, Delta0Formula.satisfies_rename]
  have hassign : (fun j => s (![out, x, y] j)) =
      ![s out, s x, s y] := by
    funext j
    fin_cases j <;> rfl
  rw [hassign]
  exact satisfies_opGraphFormula i (s out) (s x) (s y)

/-- A strong-simple function can replace the final coordinate of any bounded
formula, while its arguments are placed before the untouched context. -/
theorem exists_eliminateSimpleLast {r n : Nat}
    {f : Tuple ZFSet.{u} r → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) (φ : Delta0Formula (n + 1)) :
    ∃ ψ : Delta0Formula (r + n),
      ∀ (args : Tuple ZFSet.{u} r) (s : Tuple ZFSet.{u} n),
        Satisfies ZFMem ψ (Fin.addCases args s) ↔
          Satisfies ZFMem φ (snoc s (f args)) := by
  rcases hf n (Delta0Formula.rename (lastToFirst n) φ) with
    ⟨ψ, hψ⟩
  refine ⟨ψ, ?_⟩
  intro args s
  rw [hψ args s, Delta0Formula.satisfies_rename]
  have hassign :
      (fun i => Fin.addCases (fun _ : Fin 1 => f args) s
        (lastToFirst n i)) = snoc s (f args) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [snoc_last]
      have hlast : lastToFirst n (Fin.last n) =
          (0 : Fin (1 + n)) := by simp [lastToFirst]
      rw [hlast]
      rfl
    · simp [lastToFirst]
  rw [hassign]

/-- Choose a bounded formula eliminating the final simple-function coordinate. -/
noncomputable def eliminateSimpleLast {r n : Nat}
    {f : Tuple ZFSet.{u} r → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) (φ : Delta0Formula (n + 1)) :
    Delta0Formula (r + n) :=
  Classical.choose (exists_eliminateSimpleLast hf φ)

@[simp]
theorem satisfies_eliminateSimpleLast {r n : Nat}
    {f : Tuple ZFSet.{u} r → ZFSet.{u}}
    (hf : IsSimpleSetFunction f) (φ : Delta0Formula (n + 1))
    (args : Tuple ZFSet.{u} r) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (eliminateSimpleLast hf φ) (Fin.addCases args s) ↔
      Satisfies ZFMem φ (snoc s (f args)) :=
  Classical.choose_spec (exists_eliminateSimpleLast hf φ) args s

/-- The right-associated triple operation is strong-simple. -/
theorem isSimpleSetFunction_triple :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 3 => triple (s 0) (s 1) (s 2)) := by
  have hright : IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 3 => ZFSet.pair (s 1) (s 2)) := by
    have h := isSimpleSetFunction_orderedPair.compBinary
      (isSimpleSetFunction_projection.{u} (1 : Fin 3))
      (isSimpleSetFunction_projection.{u} (2 : Fin 3))
    have hOne : (1 : Fin 2) = Fin.succ 0 := by rfl
    simpa only [binaryTuple, hOne, Fin.cases_zero, Fin.cases_succ] using h
  have h := isSimpleSetFunction_orderedPair.compBinary
    (isSimpleSetFunction_projection.{u} (0 : Fin 3)) hright
  have hOne : (1 : Fin 2) = Fin.succ 0 := by rfl
  simpa only [binaryTuple, triple, hOne, Fin.cases_zero,
    Fin.cases_succ] using h





end Constructible.Godel
end CUAdapterModule22



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleF3F4 -/
section CUAdapterModule23
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Simplicity of the Gödel operations F3 and F4

This file instantiates the generic simple-function compiler for the two operations that extract
triple components from Kuratowski-pair encodings.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}

/-- The two rudimentary operations whose values are sets of triples. -/
inductive TripleSetKind
  | f3
  | f4

namespace TripleSetKind

/-- The rudimentary-operation index of a triple-set operation. -/
def index : TripleSetKind → Fin 9
  | .f3 => 3
  | .f4 => 4

/-- Evaluate a triple-set operation. -/
noncomputable def eval (kind : TripleSetKind)
    (x y : ZFSet.{u}) : ZFSet.{u} :=
  op kind.index x y

@[simp] theorem eval_f3 (x y : ZFSet.{u}) :
    eval .f3 x y = F3 x y := by rfl

@[simp] theorem eval_f4 (x y : ZFSet.{u}) :
    eval .f4 x y = F4 x y := by rfl

end TripleSetKind

/-- The generated-element coordinate in the common F3/F4 layout. -/
def f34ZIndex (n : Nat) : Fin (n + 6) :=
  (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc

/-- The generated-pair coordinate in the common F3/F4 layout. -/
def f34PairIndex (n : Nat) : Fin (n + 6) :=
  (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc

/-- The left-component coordinate in the common F3/F4 layout. -/
def f34LeftIndex (n : Nat) : Fin (n + 6) :=
  (Fin.last (n + 3)).castSucc.castSucc

/-- The right-component coordinate in the common F3/F4 layout. -/
def f34RightIndex (n : Nat) : Fin (n + 6) :=
  Fin.last (n + 5)

/-- Send `[u,z,v]` (F3) or `[u,v,z]` (F4), followed by the old context,
into the six-coordinate bounded pair-component context. -/
def f34ElimRename (kind : TripleSetKind) (n : Nat) :
    Fin (3 + n) → Fin (n + 6) :=
  Fin.addCases
    (fun i : Fin 3 => Fin.cases (f34LeftIndex n)
      (fun j : Fin 2 =>
        match kind with
        | .f3 => Fin.cases (f34ZIndex n)
            (fun _ : Fin 1 => f34RightIndex n) j
        | .f4 => Fin.cases (f34RightIndex n)
            (fun _ : Fin 1 => f34ZIndex n) j) i)
    (fun i : Fin n =>
      i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem f34ElimRename_assignment (kind : TripleSetKind)
    (s : Tuple ZFSet.{u} n) (z p leftBox u rightBox v : ZFSet.{u}) :
    let extended :=
      snoc (snoc (snoc (snoc (snoc (snoc s z) p) leftBox) u)
        rightBox) v
    (fun i => extended (f34ElimRename kind n i)) =
      match kind with
      | .f3 => Fin.addCases ![u, z, v] s
      | .f4 => Fin.addCases ![u, v, z] s := by
  dsimp only
  cases kind with
  | f3 =>
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        fin_cases j
        · simp [f34ElimRename, f34LeftIndex]
        · change snoc (snoc (snoc (snoc (snoc (snoc s z) p)
            leftBox) u) rightBox) v (f34ZIndex n) = z
          simp [f34ZIndex]
        · change snoc (snoc (snoc (snoc (snoc (snoc s z) p)
            leftBox) u) rightBox) v (f34RightIndex n) = v
          simp [f34RightIndex]
      · intro j
        simp [f34ElimRename]
  | f4 =>
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        fin_cases j
        · simp [f34ElimRename, f34LeftIndex]
        · change snoc (snoc (snoc (snoc (snoc (snoc s z) p)
            leftBox) u) rightBox) v (f34RightIndex n) = v
          simp [f34RightIndex]
        · change snoc (snoc (snoc (snoc (snoc (snoc s z) p)
            leftBox) u) rightBox) v (f34ZIndex n) = z
          simp [f34ZIndex]
      · intro j
        simp [f34ElimRename]

/-- The bounded body describing one generated F3/F4 element. -/
noncomputable def f34GeneratedBody (kind : TripleSetKind) {n : Nat}
    (body : Delta0Formula (n + 1)) : Delta0Formula (n + 6) :=
  .conj
    (kuratowskiPairEqAt (f34PairIndex n)
      (f34LeftIndex n) (f34RightIndex n))
    (Delta0Formula.rename (f34ElimRename kind n)
      (eliminateSimpleLast.{u} isSimpleSetFunction_triple body))

theorem satisfies_f34GeneratedBody (kind : TripleSetKind)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n)
    (z p leftBox u rightBox v : ZFSet.{u}) :
    Satisfies ZFMem (f34GeneratedBody.{u} kind body)
        (snoc (snoc (snoc (snoc (snoc (snoc s z) p) leftBox) u)
          rightBox) v) ↔
      p = ZFSet.pair u v ∧
        match kind with
        | .f3 => Satisfies ZFMem body (snoc s (triple u z v))
        | .f4 => Satisfies ZFMem body (snoc s (triple u v z)) := by
  simp only [f34GeneratedBody, Satisfies,
    satisfies_kuratowskiPairEqAt, Delta0Formula.satisfies_rename,
    f34PairIndex, f34LeftIndex, f34RightIndex,
    snoc_last, snoc_castSucc]
  rw [f34ElimRename_assignment]
  cases kind
  · simp
  · simp

/-- Eliminate a bounded quantifier over an F3/F4 value. -/
noncomputable def f34BoundAt (kind : TripleSetKind) {n : Nat}
    (x y : Fin n) (body : Delta0Formula (n + 1)) :
    Delta0Formula n :=
  .boundedEx x
    (withBoundedPairComponents y.castSucc
      (f34GeneratedBody.{u} kind body))

@[simp]
theorem satisfies_f34BoundAt (kind : TripleSetKind) {n : Nat}
    (x y : Fin n) (body : Delta0Formula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f34BoundAt.{u} kind x y body) s ↔
      ∃ q ∈ kind.eval (s x) (s y),
        Satisfies ZFMem body (snoc s q) := by
  cases kind with
  | f3 =>
      simp only [f34BoundAt, Satisfies,
        satisfies_withBoundedPairComponents, snoc_castSucc,
        satisfies_f34GeneratedBody, TripleSetKind.eval_f3]
      constructor
      · rintro ⟨z, hz, p, hp, leftBox, hleftBox, u, hu,
          rightBox, hrightBox, v, hv, hpEq, hbody⟩
        refine ⟨triple u z v, ?_, hbody⟩
        exact mem_F3_iff.mpr ⟨u, z, v, hz, by simpa [hpEq] using hp, rfl⟩
      · rintro ⟨q, hq, hbody⟩
        rcases mem_F3_iff.mp hq with ⟨u, z, v, hz, huv, rfl⟩
        refine ⟨z, hz, ZFSet.pair u v, huv,
          ({u} : ZFSet.{u}), ?_, u, ?_, ({u, v} : ZFSet.{u}), ?_,
          v, ?_, rfl, hbody⟩
        · simp [ZFSet.pair]
        · simp
        · simp [ZFSet.pair]
        · simp
  | f4 =>
      simp only [f34BoundAt, Satisfies,
        satisfies_withBoundedPairComponents, snoc_castSucc,
        satisfies_f34GeneratedBody, TripleSetKind.eval_f4]
      constructor
      · rintro ⟨z, hz, p, hp, leftBox, hleftBox, u, hu,
          rightBox, hrightBox, v, hv, hpEq, hbody⟩
        refine ⟨triple u v z, ?_, hbody⟩
        exact mem_F4_iff.mpr ⟨u, v, z, hz, by simpa [hpEq] using hp, rfl⟩
      · rintro ⟨q, hq, hbody⟩
        rcases mem_F4_iff.mp hq with ⟨u, v, z, hz, huv, rfl⟩
        refine ⟨z, hz, ZFSet.pair u v, huv,
          ({u} : ZFSet.{u}), ?_, u, ?_, ({u, v} : ZFSet.{u}), ?_,
          v, ?_, rfl, hbody⟩
        · simp [ZFSet.pair]
        · simp
        · simp [ZFSet.pair]
        · simp

/-- The simple-value specification for an F3/F4 operation. -/
noncomputable def f34Spec (kind : TripleSetKind) :
    SimpleValueSpec.{u} where
  eval := kind.eval
  memAt := memOpAt kind.index
  eqAt := opEqAt kind.index
  boundAt := f34BoundAt.{u} kind
  satisfies_memAt := by
    intro n q x y s
    exact satisfies_memOpAt kind.index q x y s
  satisfies_eqAt := by
    intro n out x y s
    exact satisfies_opEqAt kind.index out x y s
  satisfies_boundAt := by
    intro n x y body s
    exact satisfies_f34BoundAt kind x y body s

theorem isSimpleSetFunction_F3 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F3 (s 0) (s 1)) := by
  simpa only [f34Spec, TripleSetKind.eval_f3] using
    (f34Spec.{u} .f3).isSimple

theorem isSimpleSetFunction_F4 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F4 (s 0) (s 1)) := by
  simpa only [f34Spec, TripleSetKind.eval_f4] using
    (f34Spec.{u} .f4).isSimple

end Constructible.Godel
end CUAdapterModule23



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SimpleF6F8 -/
section CUAdapterModule24
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Simplicity of the Gödel operations F6 and F8

This file instantiates the generic simple-function compiler for component extraction, fibers, and
the remaining bounded pair-component operation represented here by F6 and F8.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

variable {n : Nat}

/-- The pair coordinate in the component-witness layout. -/
def componentPairIndex (n : Nat) : Fin (n + 5) :=
  (Fin.last n).castSucc.castSucc.castSucc.castSucc

/-- The left-component coordinate in the component-witness layout. -/
def componentLeftIndex (n : Nat) : Fin (n + 5) :=
  (Fin.last (n + 2)).castSucc.castSucc

/-- The right-component coordinate in the component-witness layout. -/
def componentRightIndex (n : Nat) : Fin (n + 5) :=
  Fin.last (n + 4)

/-- Select one component and the final witness coordinate. -/
def componentLastRename (useRight : Bool) (n : Nat) :
    Fin (n + 1) → Fin (n + 5) :=
  Fin.lastCases
    (if useRight then componentRightIndex n else componentLeftIndex n)
    (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem componentLastRename_assignment (useRight : Bool)
    (s : Tuple ZFSet.{u} n) (p leftBox left rightBox right : ZFSet.{u}) :
    let extended := snoc (snoc (snoc (snoc (snoc s p) leftBox) left)
      rightBox) right
    (fun i => extended (componentLastRename useRight n i)) =
      snoc s (if useRight then right else left) := by
  dsimp only
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snoc_last]
    cases useRight
    · simp [componentLastRename, componentLeftIndex]
    · simp [componentLastRename, componentRightIndex]
  · simp [componentLastRename]

/-- A candidate member of F6 is the right component of a pair in `x`. -/
def f6GeneratedBody {n : Nat} (body : Delta0Formula (n + 1)) :
    Delta0Formula (n + 5) :=
  .conj
    (kuratowskiPairEqAt (componentPairIndex n)
      (componentLeftIndex n) (componentRightIndex n))
    (Delta0Formula.rename (componentLastRename true n) body)

theorem satisfies_f6GeneratedBody (body : Delta0Formula (n + 1))
    (s : Tuple ZFSet.{u} n)
    (p leftBox left rightBox right : ZFSet.{u}) :
    Satisfies ZFMem (f6GeneratedBody body)
        (snoc (snoc (snoc (snoc (snoc s p) leftBox) left)
          rightBox) right) ↔
      p = ZFSet.pair left right ∧
        Satisfies ZFMem body (snoc s right) := by
  simp only [f6GeneratedBody, Satisfies, satisfies_kuratowskiPairEqAt,
    componentPairIndex, componentLeftIndex, componentRightIndex,
    snoc_last, snoc_castSucc, Delta0Formula.satisfies_rename]
  rw [componentLastRename_assignment]
  rfl

/-- Eliminate a bounded quantifier over an F6 value. -/
def f6BoundAt {n : Nat} (x _y : Fin n)
    (body : Delta0Formula (n + 1)) : Delta0Formula n :=
  withBoundedPairComponents x (f6GeneratedBody body)

@[simp]
theorem satisfies_f6BoundAt {n : Nat} (x y : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f6BoundAt x y body) s ↔
      ∃ q ∈ F6 (s x) (s y), Satisfies ZFMem body (snoc s q) := by
  simp only [f6BoundAt, satisfies_withBoundedPairComponents,
    satisfies_f6GeneratedBody]
  constructor
  · rintro ⟨p, hp, leftBox, hleftBox, left, hleft,
      rightBox, hrightBox, right, hright, hpEq, hbody⟩
    refine ⟨right, ?_, hbody⟩
    exact mem_F6_iff.mpr ⟨left, by simpa [hpEq] using hp⟩
  · rintro ⟨right, hrightF6, hbody⟩
    rcases mem_F6_iff.mp hrightF6 with ⟨left, hp⟩
    refine ⟨ZFSet.pair left right, hp, ({left} : ZFSet.{u}), ?_,
      left, ?_, ({left, right} : ZFSet.{u}), ?_, right, ?_, rfl, hbody⟩
    · simp [ZFSet.pair]
    · simp
    · simp [ZFSet.pair]
    · simp

/-- The simple-value specification for F6. -/
noncomputable def f6Spec : SimpleValueSpec.{u} where
  eval := F6
  memAt := memOpAt 6
  eqAt := opEqAt 6
  boundAt := f6BoundAt
  satisfies_memAt := by
    intro n q x y s
    exact satisfies_memOpAt (6 : Fin 9) q x y s
  satisfies_eqAt := by
    intro n out x y s
    exact satisfies_opEqAt (6 : Fin 9) out x y s
  satisfies_boundAt := by
    intro n x y body s
    exact satisfies_f6BoundAt x y body s

theorem isSimpleSetFunction_F6 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F6 (s 0) (s 1)) := by
  simpa only [f6Spec] using f6Spec.{u}.isSimple

/-! ## Fibers are simple -/

/-- A bounded formula for membership in a fiber. -/
def fiberMemAt {n : Nat} (q x z : Fin n) : Delta0Formula n :=
  .boundedEx x
    (kuratowskiPairEqAt (Fin.last n) q.castSucc z.castSucc)

@[simp]
theorem satisfies_fiberMemAt {n : Nat} (q x z : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (fiberMemAt q x z) s ↔
      s q ∈ fiber (s x) (s z) := by
  simp only [fiberMemAt, Satisfies, satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc, mem_fiber_iff]
  constructor
  · rintro ⟨p, hp, hpEq⟩
    simpa [hpEq] using hp
  · intro hp
    exact ⟨ZFSet.pair (s q) (s z), hp, rfl⟩

/-- The bounded body describing membership in a generated fiber. -/
def fiberGeneratedBody {n : Nat} (z : Fin n)
    (body : Delta0Formula (n + 1)) : Delta0Formula (n + 5) :=
  .conj
    (kuratowskiPairEqAt (componentPairIndex n)
      (componentLeftIndex n) (componentRightIndex n))
    (.conj
      (.eq (componentRightIndex n)
        z.castSucc.castSucc.castSucc.castSucc.castSucc)
      (Delta0Formula.rename (componentLastRename false n) body))

theorem satisfies_fiberGeneratedBody (z : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n)
    (p leftBox left rightBox right : ZFSet.{u}) :
    Satisfies ZFMem (fiberGeneratedBody z body)
        (snoc (snoc (snoc (snoc (snoc s p) leftBox) left)
          rightBox) right) ↔
      p = ZFSet.pair left right ∧ right = s z ∧
        Satisfies ZFMem body (snoc s left) := by
  simp only [fiberGeneratedBody, Satisfies, satisfies_kuratowskiPairEqAt,
    componentPairIndex, componentLeftIndex, componentRightIndex,
    snoc_last, snoc_castSucc, Delta0Formula.satisfies_rename]
  rw [componentLastRename_assignment]
  rfl

/-- Eliminate a bounded quantifier over a fiber. -/
def fiberBoundAt {n : Nat} (x z : Fin n)
    (body : Delta0Formula (n + 1)) : Delta0Formula n :=
  withBoundedPairComponents x (fiberGeneratedBody z body)

@[simp]
theorem satisfies_fiberBoundAt {n : Nat} (x z : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (fiberBoundAt x z body) s ↔
      ∃ q ∈ fiber (s x) (s z), Satisfies ZFMem body (snoc s q) := by
  simp only [fiberBoundAt, satisfies_withBoundedPairComponents,
    satisfies_fiberGeneratedBody]
  constructor
  · rintro ⟨p, hp, leftBox, hleftBox, left, hleft,
      rightBox, hrightBox, right, hright, hpEq, hrightEq, hbody⟩
    refine ⟨left, ?_, hbody⟩
    rw [mem_fiber_iff]
    simpa [hpEq, hrightEq] using hp
  · rintro ⟨left, hleftFiber, hbody⟩
    rw [mem_fiber_iff] at hleftFiber
    refine ⟨ZFSet.pair left (s z), hleftFiber,
      ({left} : ZFSet.{u}), ?_, left, ?_,
      ({left, s z} : ZFSet.{u}), ?_, s z, ?_, rfl, rfl, hbody⟩
    · simp [ZFSet.pair]
    · simp
    · simp [ZFSet.pair]
    · simp

/-- The simple-value specification for fibers. -/
noncomputable def fiberSpec : SimpleValueSpec.{u} where
  eval := fiber
  memAt := fiberMemAt
  eqAt := fiberEqAt
  boundAt := fiberBoundAt
  satisfies_memAt := by
    intro n q x z s
    exact satisfies_fiberMemAt q x z s
  satisfies_eqAt := by
    intro n out x z s
    exact satisfies_fiberEqAt out x z s
  satisfies_boundAt := by
    intro n x z body s
    exact satisfies_fiberBoundAt x z body s

theorem isSimpleSetFunction_fiber :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => fiber (s 0) (s 1)) := by
  simpa only [fiberSpec] using fiberSpec.{u}.isSimple

/-! ## F8 is a bounded image by the simple fiber operation -/

/-- Rename the coordinates used when eliminating a fiber witness. -/
def fiberElimRename {n : Nat} (x : Fin n) :
    Fin (2 + n) → Fin (n + 1) :=
  Fin.addCases
    (fun i : Fin 2 => Fin.cases x.castSucc
      (fun _ : Fin 1 => Fin.last n) i)
    (fun i : Fin n => i.castSucc)

theorem fiberElimRename_assignment (x : Fin n)
    (s : Tuple ZFSet.{u} n) (z : ZFSet.{u}) :
    (fun i => snoc s z (fiberElimRename x i)) =
      Fin.addCases ![s x, z] s := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    fin_cases j
    · simp [fiberElimRename]
    · change snoc s z (Fin.last n) = z
      simp
  · intro j
    simp [fiberElimRename]

/-- Eliminate a bounded quantifier over an F8 value. -/
noncomputable def f8BoundAt {n : Nat} (x y : Fin n)
    (body : Delta0Formula (n + 1)) : Delta0Formula n :=
  .boundedEx y
    (Delta0Formula.rename (fiberElimRename x)
      (eliminateSimpleLast.{u} isSimpleSetFunction_fiber body))

@[simp]
theorem satisfies_f8BoundAt {n : Nat} (x y : Fin n)
    (body : Delta0Formula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f8BoundAt.{u} x y body) s ↔
      ∃ q ∈ F8 (s x) (s y), Satisfies ZFMem body (snoc s q) := by
  simp only [f8BoundAt, Satisfies, Delta0Formula.satisfies_rename]
  constructor
  · rintro ⟨z, hz, hbody⟩
    rw [fiberElimRename_assignment,
      satisfies_eliminateSimpleLast.{u}] at hbody
    refine ⟨fiber (s x) z, ?_, hbody⟩
    exact mem_F8_iff.mpr ⟨z, hz, rfl⟩
  · rintro ⟨q, hq, hbody⟩
    rcases mem_F8_iff.mp hq with ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [fiberElimRename_assignment,
      satisfies_eliminateSimpleLast.{u}]
    exact hbody

/-- The simple-value specification for F8. -/
noncomputable def f8Spec : SimpleValueSpec.{u} where
  eval := F8
  memAt := memOpAt 8
  eqAt := opEqAt 8
  boundAt := f8BoundAt.{u}
  satisfies_memAt := by
    intro n q x y s
    exact satisfies_memOpAt (8 : Fin 9) q x y s
  satisfies_eqAt := by
    intro n out x y s
    exact satisfies_opEqAt (8 : Fin 9) out x y s
  satisfies_boundAt := by
    intro n x y body s
    exact satisfies_f8BoundAt x y body s

theorem isSimpleSetFunction_F8 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F8 (s 0) (s 1)) := by
  simpa only [f8Spec] using f8Spec.{u}.isSimple

end Constructible.Godel
end CUAdapterModule24



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Equivalence -/
section CUAdapterModule25
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Equivalence of formula and rudimentary definability

This file proves Jensen's equivalence between first-order definable subsets of a transitive set
and the powerset-bounded closure under the nine basic Gödel operations.
-/


open Set

universe u

namespace Constructible.Godel

theorem isSimpleSetFunction_F0 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F0 (s 0) (s 1)) := by
  simpa [F0] using isSimpleSetFunction_pair.{u}

theorem isSimpleSetFunction_F1 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F1 (s 0) (s 1)) := by
  simpa [F1] using isSimpleSetFunction_sdiff.{u}

theorem isSimpleSetFunction_F5 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F5 (s 0) (s 1)) := by
  have h := isSimpleSetFunction_sUnion.compUnary
    (isSimpleSetFunction_projection.{u} (0 : Fin 2))
  simpa [F5] using h

theorem isSimpleSetFunction_op (i : Fin 9) :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => op i (s 0) (s 1)) := by
  fin_cases i
  · simpa [op] using isSimpleSetFunction_F0.{u}
  · simpa [op] using isSimpleSetFunction_F1.{u}
  · simpa [op] using isSimpleSetFunction_F2.{u}
  · simpa [op] using isSimpleSetFunction_F3.{u}
  · simpa [op] using isSimpleSetFunction_F4.{u}
  · simpa [op] using isSimpleSetFunction_F5.{u}
  · simpa [op] using isSimpleSetFunction_F6.{u}
  · simpa [op] using isSimpleSetFunction_F7.{u}
  · simpa [op] using isSimpleSetFunction_F8.{u}

theorem godelDef_subset_DefZF {U : ZFSet.{u}}
    (hU : U.IsTransitive) :
    godelDef U ⊆ Constructible.DefZF U :=
  godelDef_subset_DefZF_of_simpleOps isSimpleSetFunction_op hU

/-- Jensen's final equivalence: formula definability over a transitive set is
exactly membership in the powerset-bounded rudimentary closure. -/
theorem DefZF_eq_godelDef {U : ZFSet.{u}} (hU : U.IsTransitive) :
    Constructible.DefZF U = godelDef U := by
  apply le_antisymm
  · exact DefZF_subset_godelDef hU
  · exact godelDef_subset_DefZF hU

end Constructible.Godel
end CUAdapterModule25



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryConstructible -/
section CUAdapterModule26
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Constructibility of rudimentary term values

Every primitive Gödel operation preserves constructibility. The proof first
shows that all members of an operation value are constructible, bounds those
members together with the two operands in one constructible stage, and then
uses the existing bounded definition of the operation to place its value in
the next stage.

It follows by structural induction that a rudimentary term whose generators
belong to `L` also evaluates to an element of `L`.
-/


open Set

universe u v

namespace Constructible

namespace Godel

/-- The field of a constructible relation is constructible. -/
theorem pairField_mem_L {r : ZFSet.{u}} (hr : r ∈ L) : pairField r ∈ L := by
  simpa only [pairField] using sUnion_mem_L (sUnion_mem_L hr)

/-- A bounded membership definition for a fiber over a fixed pair of parameters. -/
def fiberDelta0Section {U x z : ZFSet.{u}} (hx : x ∈ U) (hz : z ∈ U) :
    Delta0Section U (fiber x z) where
  arity := 2
  params := ![⟨x, hx⟩, ⟨z, hz⟩]
  formula := fiberMemAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
  correct := by
    intro q
    have hassign :
        snoc (Delta0Formula.val ![⟨x, hx⟩, ⟨z, hz⟩]) q.1 =
          ![x, z, q.1] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    exact satisfies_fiberMemAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
      ![x, z, q.1]

/-- Fibers of constructible relations at constructible parameters belong to `L`. -/
theorem fiber_mem_L {x z : ZFSet.{u}} (hx : x ∈ L) (hz : z ∈ L) :
    fiber x z ∈ L := by
  have hmembers : ∀ q ∈ fiber x z, q ∈ L := by
    intro q hq
    have hpair : ZFSet.pair q z ∈ x := mem_fiber_iff.mp hq
    exact mem_L_of_mem (pair_left_mem_pairField hpair) (pairField_mem_L hx)
  rcases exists_LStage_for_tuple ![x, z] (by
      intro i
      fin_cases i
      · exact hx
      · exact hz) with ⟨alpha, hparams⟩
  rcases exists_LStage_for_members hmembers with ⟨beta, hmembersBeta⟩
  let gamma : Ordinal.{u} := max alpha beta
  have hxGamma : x ∈ LStageZF gamma :=
    LStageZF_mono (le_max_left alpha beta) (hparams 0)
  have hzGamma : z ∈ LStageZF gamma :=
    LStageZF_mono (le_max_left alpha beta) (hparams 1)
  have hfiberGamma : fiber x z ⊆ LStageZF gamma := by
    intro q hq
    exact LStageZF_mono (le_max_right alpha beta) (hmembersBeta q hq)
  refine ⟨Order.succ gamma, ?_⟩
  rw [LStageZF_succ]
  exact (fiberDelta0Section hxGamma hzGamma).mem_DefZF
    (LStageZF_isTransitive gamma) hfiberGamma

/-- Every member of a primitive operation value is constructible. -/
theorem mem_L_of_mem_op {i : Fin 9} {x y q : ZFSet.{u}}
    (hx : x ∈ L) (hy : y ∈ L) (hq : q ∈ op i x y) : q ∈ L := by
  fin_cases i
  · rcases mem_F0_iff.mp hq with rfl | rfl
    · exact hx
    · exact hy
  · exact mem_L_of_mem (mem_F1_iff.mp hq).1 hx
  · rcases mem_F2_iff.mp hq with ⟨a, ha, b, hb, rfl⟩
    exact orderedPair_mem_L (mem_L_of_mem ha hx) (mem_L_of_mem hb hy)
  · rcases mem_F3_iff.mp hq with ⟨a, z, b, hz, hab, rfl⟩
    have haL : a ∈ L :=
      mem_L_of_mem (pair_left_mem_pairField hab) (pairField_mem_L hy)
    have hbL : b ∈ L :=
      mem_L_of_mem (pair_right_mem_pairField hab) (pairField_mem_L hy)
    have hzL : z ∈ L := mem_L_of_mem hz hx
    simpa only [triple] using
      orderedPair_mem_L haL (orderedPair_mem_L hzL hbL)
  · rcases mem_F4_iff.mp hq with ⟨a, b, z, hz, hab, rfl⟩
    have haL : a ∈ L :=
      mem_L_of_mem (pair_left_mem_pairField hab) (pairField_mem_L hy)
    have hbL : b ∈ L :=
      mem_L_of_mem (pair_right_mem_pairField hab) (pairField_mem_L hy)
    have hzL : z ∈ L := mem_L_of_mem hz hx
    simpa only [triple] using
      orderedPair_mem_L haL (orderedPair_mem_L hbL hzL)
  · rcases (mem_F5_iff (x := x) (y := y) (z := q)).mp hq with
      ⟨a, ha, hqa⟩
    exact mem_L_of_mem hqa (mem_L_of_mem ha hx)
  · rcases (mem_F6_iff (x := x) (y := y) (z := q)).mp hq with ⟨a, ha⟩
    exact mem_L_of_mem (pair_right_mem_pairField ha) (pairField_mem_L hx)
  · rcases (mem_F7_iff (x := x) (y := y) (q := q)).mp hq with
      ⟨a, ha, b, hb, rfl, _hab⟩
    exact orderedPair_mem_L (mem_L_of_mem ha hx) (mem_L_of_mem hb hx)
  · rcases mem_F8_iff.mp hq with ⟨z, hz, rfl⟩
    exact fiber_mem_L hx (mem_L_of_mem hz hy)

/-- Every primitive Gödel operation sends constructible inputs to a constructible output. -/
theorem op_mem_L {i : Fin 9} {x y : ZFSet.{u}}
    (hx : x ∈ L) (hy : y ∈ L) : op i x y ∈ L := by
  have hmembers : ∀ q ∈ op i x y, q ∈ L :=
    fun q hq => mem_L_of_mem_op hx hy hq
  rcases exists_LStage_for_tuple ![x, y] (by
      intro j
      fin_cases j
      · exact hx
      · exact hy) with ⟨alpha, hparams⟩
  rcases exists_LStage_for_members hmembers with ⟨beta, hmembersBeta⟩
  let gamma : Ordinal.{u} := max alpha beta
  have hxGamma : x ∈ LStageZF gamma :=
    LStageZF_mono (le_max_left alpha beta) (hparams 0)
  have hyGamma : y ∈ LStageZF gamma :=
    LStageZF_mono (le_max_left alpha beta) (hparams 1)
  have hopGamma : op i x y ⊆ LStageZF gamma := by
    intro q hq
    exact LStageZF_mono (le_max_right alpha beta) (hmembersBeta q hq)
  refine ⟨Order.succ gamma, ?_⟩
  rw [LStageZF_succ]
  exact op_mem_DefZF_of_subset
    (LStageZF_isTransitive gamma) hxGamma hyGamma hopGamma

namespace RudimentaryTerm

/-- A rudimentary term over constructible generators evaluates to a constructible set. -/
theorem eval_mem_L {alpha : Type u} {rho : alpha -> ZFSet.{v}}
    (hrho : ∀ a, rho a ∈ L) (term : RudimentaryTerm alpha) :
    eval rho term ∈ L := by
  induction term with
  | var a => exact hrho a
  | app i left right hleft hright =>
      exact op_mem_L hleft hright

end RudimentaryTerm

/-- Every canonical generator over a constructible set belongs to `L`. -/
theorem rudimentaryGenerator_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (a : Option (Constructible.ZFCarrier U)) : rudimentaryGenerator U a ∈ L := by
  cases a with
  | none => exact hU
  | some x => exact mem_L_of_mem x.2 hU

/-- A term over `U ∪ {U}` is constructible whenever `U` is constructible. -/
theorem RudimentaryClosureTerm.eval_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (term : RudimentaryClosureTerm U) : term.eval ∈ L :=
  RudimentaryTerm.eval_mem_L (rudimentaryGenerator_mem_L hU) term

end Godel

end Constructible
end CUAdapterModule26



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgram -/
section CUAdapterModule27
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Postfix stack programs for rudimentary evaluation

Prefix tree codes are useful for structural arguments, but a uniform
first-order evaluator would have to parse arbitrary subtree boundaries.  A
postfix stack program has a local transition semantics instead:

* a variable token pushes its generator value;
* an operation token pops the right and left operands and pushes their value.

The token lists still carry a Shortlex well-order. Hence every value in one
Gödel-definability step has a least evaluating program, and these least
programs give a well-order of that step. The local transition semantics admits
internalization by a finite set-coded execution trace.
-/


universe u v

namespace Constructible.Godel

namespace RudimentaryTerm

/-- Tokens of a postfix rudimentary stack program. -/
abbrev StackToken (α : Type u) := α ⊕ Fin 9

/-- Compile a term to postfix stack-machine instructions. -/
def stackProgram {α : Type u} :
    RudimentaryTerm α → List (StackToken α)
  | .var a => [.inl a]
  | .app i left right =>
      stackProgram left ++ stackProgram right ++ [.inr i]

/-- Execute one stack instruction.  The head of the list is the stack top. -/
noncomputable def runStackToken {α : Type u}
    (rho : α → ZFSet.{v}) :
    StackToken α → List ZFSet.{v} → Option (List ZFSet.{v})
  | .inl a, stack => some (rho a :: stack)
  | .inr i, right :: left :: rest =>
      some (op i left right :: rest)
  | .inr _, _ => none

/-- Execute a list of postfix instructions from left to right. -/
noncomputable def runStackProgram {α : Type u}
    (rho : α → ZFSet.{v}) :
    List (StackToken α) → List ZFSet.{v} → Option (List ZFSet.{v})
  | [], stack => some stack
  | token :: program, stack =>
      (runStackToken rho token stack).bind
        (runStackProgram rho program)

@[simp]
theorem runStackProgram_nil {α : Type u} (rho : α → ZFSet.{v})
    (stack : List ZFSet.{v}) :
    runStackProgram rho [] stack = some stack :=
  rfl

@[simp]
theorem runStackProgram_append {α : Type u} (rho : α → ZFSet.{v})
    (first second : List (StackToken α)) (stack : List ZFSet.{v}) :
    runStackProgram rho (first ++ second) stack =
      (runStackProgram rho first stack).bind
        (runStackProgram rho second) := by
  induction first generalizing stack with
  | nil => rfl
  | cons token first ih =>
      simp only [List.cons_append, runStackProgram]
      cases hstep : runStackToken rho token stack with
      | none => rfl
      | some next =>
          simp only [Option.bind_some]
          exact ih next

/-- Compiled programs push exactly the value of their source term. -/
@[simp]
theorem run_stackProgram {α : Type u} (rho : α → ZFSet.{v})
    (term : RudimentaryTerm α) (stack : List ZFSet.{v}) :
    runStackProgram rho (stackProgram term) stack =
      some (eval rho term :: stack) := by
  induction term generalizing stack with
  | var a =>
      rfl
  | app i left right ihLeft ihRight =>
      rw [stackProgram, runStackProgram_append,
        runStackProgram_append, ihLeft,
        Option.bind_some, ihRight,
        Option.bind_some]
      rfl

/-! ## The structural program well-order -/

/-- Variables precede operation tokens. -/
def stackTokenRel {α : Type u} (r : α → α → Prop) :
    StackToken α → StackToken α → Prop :=
  Sum.Lex r (fun i j : Fin 9 => i < j)

theorem stackTokenRel_isWellOrder {α : Type u}
    (r : α → α → Prop) [IsWellOrder α r] :
    IsWellOrder (StackToken α) (stackTokenRel r) := by
  unfold stackTokenRel
  infer_instance

/-- Shortlex comparison of postfix instruction lists. -/
def stackProgramRel {α : Type u} (r : α → α → Prop) :
    List (StackToken α) → List (StackToken α) → Prop :=
  List.Shortlex (stackTokenRel r)

theorem stackProgramRel_isWellOrder {α : Type u}
    (r : α → α → Prop) [IsWellOrder α r] :
    IsWellOrder (List (StackToken α)) (stackProgramRel r) := by
  letI : IsWellOrder (StackToken α) (stackTokenRel r) :=
    stackTokenRel_isWellOrder r
  letI : Std.Trichotomous (stackTokenRel r) :=
    { trichotomous :=
        (stackTokenRel_isWellOrder r).trichotomous }
  exact
    { wf := List.Shortlex.wf
        (IsWellFounded.wf : WellFounded (stackTokenRel r))
      trichotomous := fun first second =>
        (inferInstance :
          Std.Trichotomous (List.Shortlex (stackTokenRel r))).trichotomous
            first second }

/-! ## Least programs representing definable values -/

/-- Postfix programs which evaluate from the empty stack to the singleton `z`. -/
def representingStackPrograms (U z : ZFSet.{u}) :
    Set (List (StackToken (Option (Constructible.ZFCarrier U)))) :=
  {program |
    runStackProgram (rudimentaryGenerator U) program [] = some [z]}

theorem representingStackPrograms_nonempty {U z : ZFSet.{u}}
    (hz : z ∈ godelDef U) :
    (representingStackPrograms U z).Nonempty := by
  rcases (mem_godelDef_iff_exists_rudimentaryTerm.mp hz).2 with
    ⟨term, hterm⟩
  refine ⟨stackProgram term, ?_⟩
  simp only [representingStackPrograms, Set.mem_ofPred_eq,
    run_stackProgram]
  change eval (rudimentaryGenerator U) term = z at hterm
  simp only [hterm]

/-- The Shortlex-least postfix program evaluating to `z`. -/
noncomputable def leastStackProgram (U z : ZFSet.{u})
    (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    List (StackToken (Option (Constructible.ZFCarrier U))) :=
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  (IsWellFounded.wf : WellFounded (stackProgramRel r)).min
    (representingStackPrograms U z)
    (representingStackPrograms_nonempty hz)

@[simp]
theorem run_leastStackProgram (U z : ZFSet.{u})
    (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    runStackProgram (rudimentaryGenerator U)
      (leastStackProgram U z hz r) [] = some [z] := by
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  exact (IsWellFounded.wf : WellFounded (stackProgramRel r)).min_mem
    (representingStackPrograms U z)
    (representingStackPrograms_nonempty hz)

/-- The least-program map from one definability step to instruction lists. -/
noncomputable def leastStackProgramMap (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    DefCarrier U →
      List (StackToken (Option (Constructible.ZFCarrier U))) :=
  fun z => leastStackProgram U z.1 z.2 r

/-- Distinct definable values have distinct least evaluating programs. -/
theorem leastStackProgramMap_injective (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    Function.Injective (leastStackProgramMap U r) := by
  intro x y hxy
  apply Subtype.ext
  have hrun := congrArg
    (fun program =>
      runStackProgram (rudimentaryGenerator U) program []) hxy
  change
    runStackProgram (rudimentaryGenerator U)
        (leastStackProgram U x.1 x.2 r) [] =
      runStackProgram (rudimentaryGenerator U)
        (leastStackProgram U y.1 y.2 r) [] at hrun
  rw [run_leastStackProgram, run_leastStackProgram] at hrun
  exact (List.cons.inj (Option.some.inj hrun)).1

/-- Compare definable values by their least postfix programs. -/
noncomputable def defCarrierStackRel (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    DefCarrier U → DefCarrier U → Prop :=
  InvImage (stackProgramRel r) (leastStackProgramMap U r)

/-- The least postfix-program order well-orders one Gödel-definability step. -/
theorem defCarrierStackRel_isWellOrder (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    IsWellOrder (DefCarrier U) (defCarrierStackRel U r) := by
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  exact
    { wf := InvImage.wf (leastStackProgramMap U r)
        (IsWellFounded.wf : WellFounded (stackProgramRel r))
      trichotomous :=
        (InvImage.trichotomous (r := stackProgramRel r)
          (leastStackProgramMap_injective U r)).trichotomous }

end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule27


