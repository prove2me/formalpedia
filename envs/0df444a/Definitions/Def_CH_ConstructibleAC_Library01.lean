-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library01
-- name    : CH_ConstructibleAC_Library01
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T00:54:22.208885+00:00
-- url     : https://prove2.me/theorems/e411f5d0-69a8-48d0-905d-53d02b170a78
-- title:
--   Finite formulas and parameter definability
-- statement:
--   For a structure with one binary membership relation, finite-variable formulas describe relations on finite tuples. The definable-power-set operation selects subsets obtained from these formulas by fixing finitely many parameters. This library supplies the tuple operations, relation-algebra syntax, bounded formulas, and the corresponding first-order definability interfaces used in constructing the stages of the constructible universe.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Def.lean#L1-L1108; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Delta0.lean#L1-L333; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Godel.lean#L1-L414

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


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Def -/
section CUAdapterModule0
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The relation-algebra definition of `Def`

This file formalizes the relation-algebra presentation of first-order
definability:

* `D 0 A n` consists of the atomic membership and equality relations;
* `D (k+1) A n` is closed under complement, intersection, and existential
  projection, using relations from stage `k`;
* `Df A n` is the union of all finite stages;
* `definablePowerset A` consists of the sections of relations in `Df` obtained
  by fixing finitely many parameters.

Here the underlying set `a` is represented by a Lean type `A`, equipped with
the binary relation which plays the role of membership.  Thus `Tuple A n` is
the type-theoretic counterpart of `a^n`.
-/


open Set

universe u

namespace Constructible

/-- An ordered `n`-tuple of elements of `A`. -/
abbrev Tuple (A : Type u) (n : Nat) := Fin n → A

/-- An `n`-ary relation on `A`. -/
abbrev Rel (A : Type u) (n : Nat) := Set (Tuple A n)

/-- Append one element as the last coordinate of a tuple. -/
def snoc {A : Type u} {n : Nat} (s : Tuple A n) (x : A) : Tuple A (n + 1) :=
  Fin.lastCases x s

@[simp]
theorem snoc_castSucc {A : Type u} {n : Nat} (s : Tuple A n) (x : A)
    (i : Fin n) : snoc s x i.castSucc = s i := by
  simp [snoc]

@[simp]
theorem snoc_last {A : Type u} {n : Nat} (s : Tuple A n) (x : A) :
    snoc s x (Fin.last n) = x := by
  simp [snoc]

/-! ## An independent syntax and satisfaction relation -/

/--
Intrinsically scoped first-order formulas in the language of set theory.

`FOFormula n` is scoped in a context of `n` available variables.  The
existential quantifier binds the new last coordinate, so its body has `n + 1`
available variables.  Negation,
conjunction, and existential quantification form a functionally complete basis
for classical first-order logic.
-/
inductive FOFormula : Nat → Type
  | mem {n : Nat} (i j : Fin n) : FOFormula n
  | eq {n : Nat} (i j : Fin n) : FOFormula n
  | neg {n : Nat} (φ : FOFormula n) : FOFormula n
  | conj {n : Nat} (φ ψ : FOFormula n) : FOFormula n
  | ex {n : Nat} (φ : FOFormula (n + 1)) : FOFormula n

namespace FOFormula

/-- Tarskian satisfaction for a tuple assignment in a structure `(A, E)`. -/
@[simp]
def Satisfies {A : Type u} (E : A → A → Prop) :
    {n : Nat} → FOFormula n → Tuple A n → Prop
  | _, .mem i j, s => E (s i) (s j)
  | _, .eq i j, s => s i = s j
  | _, .neg φ, s => ¬Satisfies E φ s
  | _, .conj φ ψ, s => Satisfies E φ s ∧ Satisfies E ψ s
  | _, .ex φ, s => ∃ x : A, Satisfies E φ (snoc s x)

/-- The relation denoted by a formula in `(A, E)`. -/
def semanticRel {A : Type u} (E : A → A → Prop) {n : Nat}
    (φ : FOFormula n) : Rel A n :=
  {s | Satisfies E φ s}

@[simp]
theorem mem_semanticRel_iff {A : Type u} {E : A → A → Prop}
    {n : Nat} {φ : FOFormula n} {s : Tuple A n} :
    s ∈ semanticRel E φ ↔ Satisfies E φ s :=
  Iff.rfl

/-- Disjunction as a derived connective. -/
def disj {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  .neg (.conj (.neg φ) (.neg ψ))

/-- Material implication as a derived connective. -/
def imp {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  disj (.neg φ) ψ

/-- Logical equivalence as a derived connective. -/
def biimp {n : Nat} (φ ψ : FOFormula n) : FOFormula n :=
  .conj (imp φ ψ) (imp ψ φ)

/-- Universal quantification as a derived connective. -/
def all {n : Nat} (φ : FOFormula (n + 1)) : FOFormula n :=
  .neg (.ex (.neg φ))

@[simp]
theorem satisfies_disj {A : Type u} {E : A → A → Prop} {n : Nat}
    {φ ψ : FOFormula n} {s : Tuple A n} :
    Satisfies E (disj φ ψ) s ↔ Satisfies E φ s ∨ Satisfies E ψ s := by
  classical
  change
    (¬(¬Satisfies E φ s ∧ ¬Satisfies E ψ s)) ↔
      Satisfies E φ s ∨ Satisfies E ψ s
  constructor
  · intro h
    by_cases hφ : Satisfies E φ s
    · exact Or.inl hφ
    · exact Or.inr (Classical.byContradiction fun hψ => h ⟨hφ, hψ⟩)
  · rintro (hφ | hψ) h
    · exact h.1 hφ
    · exact h.2 hψ

@[simp]
theorem satisfies_imp {A : Type u} {E : A → A → Prop} {n : Nat}
    {φ ψ : FOFormula n} {s : Tuple A n} :
    Satisfies E (imp φ ψ) s ↔
      (Satisfies E φ s → Satisfies E ψ s) := by
  classical
  simp only [imp, satisfies_disj, Satisfies]
  tauto

@[simp]
theorem satisfies_biimp {A : Type u} {E : A → A → Prop} {n : Nat}
    {φ ψ : FOFormula n} {s : Tuple A n} :
    Satisfies E (biimp φ ψ) s ↔
      (Satisfies E φ s ↔ Satisfies E ψ s) := by
  classical
  simp only [biimp, Satisfies, satisfies_imp]
  tauto

@[simp]
theorem satisfies_all {A : Type u} {E : A → A → Prop} {n : Nat}
    {φ : FOFormula (n + 1)} {s : Tuple A n} :
    Satisfies E (all φ) s ↔ ∀ x : A, Satisfies E φ (snoc s x) := by
  classical
  change
    (¬∃ x : A, ¬Satisfies E φ (snoc s x)) ↔
      ∀ x : A, Satisfies E φ (snoc s x)
  constructor
  · intro h x
    exact Classical.byContradiction fun hx => h ⟨x, hx⟩
  · intro h hex
    rcases hex with ⟨x, hx⟩
    exact hx (h x)

/-! ### Variable management -/

/-- Extend a renaming across the new last variable bound by `ex`. -/
def liftRename {n m : Nat} (ρ : Fin n → Fin m) :
    Fin (n + 1) → Fin (m + 1) :=
  Fin.lastCases (Fin.last m) (fun i => (ρ i).castSucc)

@[simp]
theorem liftRename_castSucc {n m : Nat} (ρ : Fin n → Fin m) (i : Fin n) :
    liftRename ρ i.castSucc = (ρ i).castSucc := by
  simp [liftRename]

@[simp]
theorem liftRename_last {n m : Nat} (ρ : Fin n → Fin m) :
    liftRename ρ (Fin.last n) = Fin.last m := by
  simp [liftRename]

/-- Rename all available variables, preserving variables bound by `ex`. -/
def rename {n m : Nat} (ρ : Fin n → Fin m) : FOFormula n → FOFormula m
  | .mem i j => .mem (ρ i) (ρ j)
  | .eq i j => .eq (ρ i) (ρ j)
  | .neg φ => .neg (rename ρ φ)
  | .conj φ ψ => .conj (rename ρ φ) (rename ρ ψ)
  | .ex φ => .ex (rename (liftRename ρ) φ)

theorem snoc_comp_liftRename {A : Type u} {n m : Nat}
    (ρ : Fin n → Fin m) (s : Tuple A m) (x : A) :
    (fun i => snoc s x (liftRename ρ i)) = snoc (fun i => s (ρ i)) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Renaming a formula is semantically composition of its assignment. -/
@[simp]
theorem satisfies_rename {A : Type u} (E : A → A → Prop)
    {n m : Nat} (φ : FOFormula n) (ρ : Fin n → Fin m)
    (s : Tuple A m) :
    Satisfies E (rename ρ φ) s ↔
      Satisfies E φ (fun i => s (ρ i)) := by
  induction φ generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => simp [rename, ih]
  | conj φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | ex φ ih =>
      simp only [rename, Satisfies, ih]
      constructor
      · rintro ⟨x, hx⟩
        have hassign :
            (fun i => snoc s x (liftRename ρ i)) =
              snoc (fun i => s (ρ i)) x :=
          snoc_comp_liftRename ρ s x
        exact ⟨x, by simpa only [hassign] using hx⟩
      · rintro ⟨x, hx⟩
        have hassign :
            (fun i => snoc s x (liftRename ρ i)) =
              snoc (fun i => s (ρ i)) x :=
          snoc_comp_liftRename ρ s x
        exact ⟨x, by simpa only [hassign] using hx⟩

/-- Add one unused last variable to the context of a formula. -/
def weaken {n : Nat} (φ : FOFormula n) : FOFormula (n + 1) :=
  rename Fin.castSucc φ

@[simp]
theorem satisfies_weaken {A : Type u} (E : A → A → Prop)
    {n : Nat} (φ : FOFormula n) (s : Tuple A n) (x : A) :
    Satisfies E (weaken φ) (snoc s x) ↔ Satisfies E φ s := by
  rw [weaken, satisfies_rename]
  have hassign : (fun i => snoc s x i.castSucc) = s := by
    funext i
    exact snoc_castSucc s x i
  simp only [hassign]

/-! ### Bounded quantifiers -/

/-- `∃ x ∈ s i, φ`, with the witness bound as the new last variable. -/
def boundedEx {n : Nat} (i : Fin n) (φ : FOFormula (n + 1)) : FOFormula n :=
  .ex (.conj (.mem (Fin.last n) i.castSucc) φ)

@[simp]
theorem satisfies_boundedEx {A : Type u} {E : A → A → Prop}
    {n : Nat} {i : Fin n} {φ : FOFormula (n + 1)} {s : Tuple A n} :
    Satisfies E (boundedEx i φ) s ↔
      ∃ x : A, E x (s i) ∧ Satisfies E φ (snoc s x) := by
  simp [boundedEx]

/-- `∀ x ∈ s i, φ`, with the witness bound as the new last variable. -/
def boundedAll {n : Nat} (i : Fin n) (φ : FOFormula (n + 1)) : FOFormula n :=
  .neg (boundedEx i (.neg φ))

@[simp]
theorem satisfies_boundedAll {A : Type u} {E : A → A → Prop}
    {n : Nat} {i : Fin n} {φ : FOFormula (n + 1)} {s : Tuple A n} :
    Satisfies E (boundedAll i φ) s ↔
      ∀ x : A, E x (s i) → Satisfies E φ (snoc s x) := by
  classical
  simp [boundedAll]

end FOFormula

section Atomic

variable {A : Type u} (E : A → A → Prop)

/-- The atomic relation `x_i ∈ x_j`, with `E` interpreting membership. -/
def memRel (n : Nat) (i j : Fin n) : Rel A n :=
  {s | E (s i) (s j)}

/-- The atomic relation `x_i = x_j`. -/
def eqRel (n : Nat) (i j : Fin n) : Rel A n :=
  {s | s i = s j}

/-- Existential projection deleting the last coordinate. -/
def existsProj {n : Nat} (r : Rel A (n + 1)) : Rel A n :=
  {s | ∃ x : A, snoc s x ∈ r}

@[simp]
theorem mem_existsProj {n : Nat} (r : Rel A (n + 1)) (s : Tuple A n) :
    s ∈ existsProj r ↔ ∃ x : A, snoc s x ∈ r :=
  Iff.rfl

/-- Stage zero: precisely the atomic membership and equality relations. -/
def DZero (n : Nat) : Set (Rel A n) :=
  {r |
    (∃ i j : Fin n, r = memRel E n i j) ∨
      ∃ i j : Fin n, r = eqRel n i j}

/--
`D k n`, the relations of arity `n` generated in at most `k` closure stages.

The recursive call in the projection clause has arity `n+1`, but its stage is
`k`; hence recursion is structural on the first argument.
-/
def D : (k n : Nat) → Set (Rel A n)
  | 0, n => DZero E n
  | k + 1, n =>
      {r |
        r ∈ D k n ∨
        (∃ t, t ∈ D k n ∧ r = tᶜ) ∨
        (∃ t v, t ∈ D k n ∧ v ∈ D k n ∧ r = t ∩ v) ∨
        (∃ t, t ∈ D k (n + 1) ∧ r = existsProj t)}

@[simp]
theorem mem_D_zero_iff {n : Nat} {r : Rel A n} :
    r ∈ D E 0 n ↔
      (∃ i j : Fin n, r = memRel E n i j) ∨
        ∃ i j : Fin n, r = eqRel n i j :=
  Iff.rfl

@[simp]
theorem mem_D_succ_iff {k n : Nat} {r : Rel A n} :
    r ∈ D E (k + 1) n ↔
      r ∈ D E k n ∨
      (∃ t, t ∈ D E k n ∧ r = tᶜ) ∨
      (∃ t v, t ∈ D E k n ∧ v ∈ D E k n ∧ r = t ∩ v) ∨
      (∃ t, t ∈ D E k (n + 1) ∧ r = existsProj t) :=
  Iff.rfl

/-- `Df A n = ⋃ k, D k A n`. -/
def Df (n : Nat) : Set (Rel A n) :=
  {r | ∃ k : Nat, r ∈ D E k n}

@[simp]
theorem mem_Df_iff {n : Nat} {r : Rel A n} :
    r ∈ Df E n ↔ ∃ k : Nat, r ∈ D E k n :=
  Iff.rfl

theorem D_subset_succ (k n : Nat) : D E k n ⊆ D E (k + 1) n := by
  intro r hr
  exact Or.inl hr

theorem D_mono_stage {k l n : Nat} (hkl : k ≤ l) : D E k n ⊆ D E l n := by
  induction l, hkl using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ l hkl ih => exact Set.Subset.trans ih (D_subset_succ E l n)

theorem D_subset_Df (k n : Nat) : D E k n ⊆ Df E n := by
  intro r hr
  exact ⟨k, hr⟩

theorem Df_compl {n : Nat} {r : Rel A n} (hr : r ∈ Df E n) : rᶜ ∈ Df E n := by
  rcases hr with ⟨k, hk⟩
  exact ⟨k + 1, Or.inr (Or.inl ⟨r, hk, rfl⟩)⟩

theorem Df_inter {n : Nat} {r t : Rel A n}
    (hr : r ∈ Df E n) (ht : t ∈ Df E n) : r ∩ t ∈ Df E n := by
  rcases hr with ⟨k, hk⟩
  rcases ht with ⟨l, hl⟩
  let m := max k l
  have hkm : r ∈ D E m n := D_mono_stage E (Nat.le_max_left k l) hk
  have hlm : t ∈ D E m n := D_mono_stage E (Nat.le_max_right k l) hl
  exact ⟨m + 1, Or.inr (Or.inr (Or.inl ⟨r, t, hkm, hlm, rfl⟩))⟩

theorem Df_existsProj {n : Nat} {r : Rel A (n + 1)}
    (hr : r ∈ Df E (n + 1)) : existsProj r ∈ Df E n := by
  rcases hr with ⟨k, hk⟩
  exact ⟨k + 1, Or.inr (Or.inr (Or.inr ⟨r, hk, rfl⟩))⟩

/-! ### Equivalence with first-order formula semantics -/

@[simp]
theorem semanticRel_mem {n : Nat} (i j : Fin n) :
    FOFormula.semanticRel E (.mem i j) = memRel E n i j :=
  rfl

@[simp]
theorem semanticRel_eq {n : Nat} (i j : Fin n) :
    FOFormula.semanticRel E (.eq i j) = eqRel n i j :=
  rfl

@[simp]
theorem semanticRel_neg {n : Nat} (φ : FOFormula n) :
    FOFormula.semanticRel E (.neg φ) = (FOFormula.semanticRel E φ)ᶜ :=
  rfl

@[simp]
theorem semanticRel_conj {n : Nat} (φ ψ : FOFormula n) :
    FOFormula.semanticRel E (.conj φ ψ) =
      FOFormula.semanticRel E φ ∩ FOFormula.semanticRel E ψ :=
  rfl

@[simp]
theorem semanticRel_ex {n : Nat} (φ : FOFormula (n + 1)) :
    FOFormula.semanticRel E (.ex φ) =
      existsProj (FOFormula.semanticRel E φ) :=
  rfl

/-- Soundness: the semantics of every formula belongs to `Df`. -/
theorem semanticRel_mem_Df {n : Nat} (φ : FOFormula n) :
    FOFormula.semanticRel E φ ∈ Df E n := by
  induction φ with
  | mem i j =>
      exact D_subset_Df E 0 _ (Or.inl ⟨i, j, rfl⟩)
  | eq i j =>
      exact D_subset_Df E 0 _ (Or.inr ⟨i, j, rfl⟩)
  | neg φ ih =>
      simpa using Df_compl E ih
  | conj φ ψ ihφ ihψ =>
      simpa using Df_inter E ihφ ihψ
  | ex φ ih =>
      simpa using Df_existsProj E ih

/--
Stagewise completeness: every relation produced at a finite stage is the
semantics of an intrinsically scoped first-order formula.
-/
theorem exists_formula_of_mem_D (k : Nat) {n : Nat} {r : Rel A n}
    (hr : r ∈ D E k n) :
    ∃ φ : FOFormula n, r = FOFormula.semanticRel E φ := by
  induction k generalizing n r with
  | zero =>
      rcases (mem_D_zero_iff (E := E)).mp hr with
        ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩
      · exact ⟨.mem i j, rfl⟩
      · exact ⟨.eq i j, rfl⟩
  | succ k ih =>
      rcases (mem_D_succ_iff (E := E)).mp hr with
        hr | ⟨t, ht, rfl⟩ | ⟨t, v, ht, hv, rfl⟩ | ⟨t, ht, rfl⟩
      · exact ih hr
      · rcases ih ht with ⟨φ, rfl⟩
        exact ⟨.neg φ, by simp⟩
      · rcases ih ht with ⟨φ, rfl⟩
        rcases ih hv with ⟨ψ, rfl⟩
        exact ⟨.conj φ ψ, by simp⟩
      · rcases ih ht with ⟨φ, rfl⟩
        exact ⟨.ex φ, by simp⟩

/--
Full semantic equivalence: `Df E n` consists exactly of the relations denoted
by `n`-variable first-order formulas in the language `{∈, =}`.
-/
theorem mem_Df_iff_exists_formula {n : Nat} {r : Rel A n} :
    r ∈ Df E n ↔
      ∃ φ : FOFormula n, r = FOFormula.semanticRel E φ := by
  constructor
  · rintro ⟨k, hk⟩
    exact exists_formula_of_mem_D E k hk
  · rintro ⟨φ, rfl⟩
    exact semanticRel_mem_Df E φ





/-- A section of an `(n+1)`-ary relation after fixing its first `n` entries. -/
def relSection {n : Nat} (r : Rel A (n + 1)) (s : Tuple A n) : Set A :=
  {x | snoc s x ∈ r}

/--
The definable-powerset operation associated to `Df`. Parameters are represented
by the tuple `s`; the defining relation itself is parameter-free and belongs to
`Df E (n+1)`.
-/
def definablePowerset : Set (Set A) :=
  {x |
    ∃ n : Nat, ∃ s : Tuple A n, ∃ r : Rel A (n + 1),
      r ∈ Df E (n + 1) ∧ x = relSection r s}

@[simp]
theorem mem_definablePowerset_iff {x : Set A} :
    x ∈ definablePowerset E ↔
      ∃ n : Nat, ∃ s : Tuple A n, ∃ r : Rel A (n + 1),
        r ∈ Df E (n + 1) ∧ x = relSection r s :=
  Iff.rfl

/--
Formula-and-satisfaction characterization of `definablePowerset`: a subset is
definable exactly when one formula, with a finite tuple of parameters, defines
membership in it.
-/
theorem mem_definablePowerset_iff_exists_satisfies {x : Set A} :
    x ∈ definablePowerset E ↔
      ∃ n : Nat, ∃ s : Tuple A n, ∃ φ : FOFormula (n + 1),
        ∀ y : A, y ∈ x ↔ FOFormula.Satisfies E φ (snoc s y) := by
  constructor
  · rintro ⟨n, s, r, hr, rfl⟩
    rcases (mem_Df_iff_exists_formula (E := E)).mp hr with ⟨φ, rfl⟩
    exact ⟨n, s, φ, fun _ => Iff.rfl⟩
  · rintro ⟨n, s, φ, hφ⟩
    refine ⟨n, s, FOFormula.semanticRel E φ, semanticRel_mem_Df E φ, ?_⟩
    ext y
    exact hφ y

end Atomic

/-! ## Specialization to Mathlib's ZFC universe -/

section ZFC

/-!
### An internal `ZFSet` version of the definable-powerset operation

The following construction uses the powerset and separation operations of
`ZFSet`.  Consequently `DefZF a` is itself a genuine ZFC set, not merely an
external Lean predicate on `ZFSet`.
-/

/-- The subtype consisting of the members of the ZFC set `a`. -/
abbrev ZFCarrier (a : ZFSet.{u}) := {x : ZFSet.{u} // x ∈ a}

/-- Membership in `a`, regarded as a relation on its subtype of elements. -/
def zfCarrierMem (a : ZFSet.{u}) : ZFCarrier a → ZFCarrier a → Prop :=
  fun x y => x.1 ∈ y.1

/-- Regard `z` as an external subset of the subtype `ZFCarrier a`. -/
def zfSubsetAsCarrier (a z : ZFSet.{u}) : Set (ZFCarrier a) :=
  {x | x.1 ∈ z}

/-- Represent a subset of the members of `a` by separation on `a`. -/
noncomputable def representZFSubset (a : ZFSet.{u})
    (s : Set (ZFCarrier a)) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ hx : x ∈ a, (⟨x, hx⟩ : ZFCarrier a) ∈ s) a

@[simp]
theorem mem_representZFSubset_iff (a : ZFSet.{u})
    (s : Set (ZFCarrier a)) (x : ZFSet.{u}) :
    x ∈ representZFSubset a s ↔
      ∃ hx : x ∈ a, (⟨x, hx⟩ : ZFCarrier a) ∈ s := by
  simp [representZFSubset]



@[simp]
theorem zfSubsetAsCarrier_representZFSubset (a : ZFSet.{u})
    (s : Set (ZFCarrier a)) :
    zfSubsetAsCarrier a (representZFSubset a s) = s := by
  ext x
  simp [zfSubsetAsCarrier]

/--
The genuine internal definable-powerset operation on Mathlib's ZFC sets.

An element `z` of `a.powerset` is retained exactly when the corresponding
subset of `(a, ∈)` belongs to the relation-algebraic `definablePowerset`.
-/
noncomputable def DefZF (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun z =>
      zfSubsetAsCarrier a z ∈ definablePowerset (zfCarrierMem a))
    a.powerset

@[simp]
theorem mem_DefZF_iff {a z : ZFSet.{u}} :
    z ∈ DefZF a ↔
      z ⊆ a ∧
        zfSubsetAsCarrier a z ∈ definablePowerset (zfCarrierMem a) := by
  simp [DefZF]

/--
`DefZF` stated entirely through formula satisfaction over the structure
`(a, ∈)`.  The condition `z ⊆ a` remains essential: the carrier semantics only
observes elements of `a`.
-/
theorem mem_DefZF_iff_exists_satisfies {a z : ZFSet.{u}} :
    z ∈ DefZF a ↔
      z ⊆ a ∧
        ∃ n : Nat, ∃ s : Tuple (ZFCarrier a) n,
          ∃ φ : FOFormula (n + 1),
            ∀ x : ZFCarrier a,
              x.1 ∈ z ↔
                FOFormula.Satisfies (zfCarrierMem a) φ (snoc s x) := by
  rw [mem_DefZF_iff]
  constructor
  · rintro ⟨hza, hdef⟩
    refine ⟨hza, ?_⟩
    simpa [zfSubsetAsCarrier] using
      (mem_definablePowerset_iff_exists_satisfies
        (E := zfCarrierMem a)).mp hdef
  · rintro ⟨hza, hdef⟩
    refine ⟨hza, ?_⟩
    apply (mem_definablePowerset_iff_exists_satisfies
      (E := zfCarrierMem a)).mpr
    simpa [zfSubsetAsCarrier] using hdef







/-! ### Basic structural properties of `DefZF` -/

/-- The whole carrier is definable over itself by the formula `x = x`. -/
theorem self_mem_DefZF (a : ZFSet.{u}) : a ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  refine ⟨Set.Subset.rfl, 0, (fun i => Fin.elim0 i),
    .eq (Fin.last 0) (Fin.last 0), ?_⟩
  intro x
  simp

/-- Pairing is available at the next definability stage. -/
theorem pair_mem_DefZF {a x y : ZFSet.{u}} (hx : x ∈ a) (hy : y ∈ a) :
    ({x, y} : ZFSet.{u}) ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier a := ⟨x, hx⟩
  let sy : ZFCarrier a := ⟨y, hy⟩
  let params : Tuple (ZFCarrier a) 2 := ![sx, sy]
  let φ : FOFormula 3 :=
    FOFormula.disj
      (.eq (Fin.last 2) (Fin.castSucc (0 : Fin 2)))
      (.eq (Fin.last 2) (Fin.castSucc (1 : Fin 2)))
  refine ⟨?_, 2, params, φ, ?_⟩
  · intro z hz
    rcases ZFSet.mem_pair.mp hz with rfl | rfl
    · exact hx
    · exact hy
  · intro z
    rw [ZFSet.mem_pair, FOFormula.satisfies_disj]
    change
      (z.1 = x ∨ z.1 = y) ↔
        (snoc params z (Fin.last 2) =
            snoc params z (Fin.castSucc (0 : Fin 2)) ∨
          snoc params z (Fin.last 2) =
            snoc params z (Fin.castSucc (1 : Fin 2)))
    simp only [snoc_last, snoc_castSucc]
    simp [params, sx, sy, Subtype.ext_iff]

/--
Internal union is definable over a transitive carrier.  Transitivity is used
both to show that `⋃₀ x` is a subset of the carrier and to regard the
bound witness in `∃ t, t ∈ x ∧ z ∈ t` as an element of `ZFCarrier a`.
-/
theorem sUnion_mem_DefZF {a x : ZFSet.{u}}
    (ha : a.IsTransitive) (hx : x ∈ a) :
    ZFSet.sUnion x ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier a := ⟨x, hx⟩
  let params : Tuple (ZFCarrier a) 1 := ![sx]
  let φ : FOFormula 2 :=
    .ex (.conj
      (.mem (2 : Fin 3) (0 : Fin 3))
      (.mem (1 : Fin 3) (2 : Fin 3)))
  refine ⟨?_, 1, params, φ, ?_⟩
  · intro z hz
    rcases ZFSet.mem_sUnion.mp hz with ⟨t, htx, hzt⟩
    exact ha.mem_trans hzt (ha.mem_trans htx hx)
  · intro z
    change
      z.1 ∈ ZFSet.sUnion x ↔
        ∃ t : ZFCarrier a, t.1 ∈ x ∧ z.1 ∈ t.1
    constructor
    · intro hz
      rcases ZFSet.mem_sUnion.mp hz with ⟨t, htx, hzt⟩
      exact ⟨⟨t, ha.mem_trans htx hx⟩, htx, hzt⟩
    · rintro ⟨t, htx, hzt⟩
      exact ZFSet.mem_sUnion.mpr ⟨t.1, htx, hzt⟩

/-- Binary intersection is definable over a transitive carrier. -/
theorem inter_mem_DefZF {a x y : ZFSet.{u}}
    (ha : a.IsTransitive) (hx : x ∈ a) (hy : y ∈ a) :
    x ∩ y ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier a := ⟨x, hx⟩
  let sy : ZFCarrier a := ⟨y, hy⟩
  let params : Tuple (ZFCarrier a) 2 := ![sx, sy]
  let φ : FOFormula 3 :=
    .conj
      (.mem (Fin.last 2) (Fin.castSucc (0 : Fin 2)))
      (.mem (Fin.last 2) (Fin.castSucc (1 : Fin 2)))
  refine ⟨?_, 2, params, φ, ?_⟩
  · intro z hz
    exact ha.mem_trans (ZFSet.mem_inter.mp hz).1 hx
  · intro z
    rw [ZFSet.mem_inter]
    change
      (z.1 ∈ x ∧ z.1 ∈ y) ↔
        ((snoc params z (Fin.last 2)).1 ∈
            (snoc params z (Fin.castSucc (0 : Fin 2))).1 ∧
          (snoc params z (Fin.last 2)).1 ∈
            (snoc params z (Fin.castSucc (1 : Fin 2))).1)
    simp only [snoc_last, snoc_castSucc]
    rfl



@[simp]
theorem DefZF_empty : DefZF (∅ : ZFSet.{u}) = {∅} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    have hz0 : z = ∅ := (ZFSet.eq_empty z).2 fun y hy =>
      ZFSet.notMem_empty y ((mem_DefZF_iff.mp hz).1 hy)
    simp [hz0]
  · intro hz
    have hz0 : z = ∅ := by simpa using hz
    simpa [hz0] using self_mem_DefZF (∅ : ZFSet.{u})

/--
Every element of a transitive set is a definable subset of that set, using the
element itself as a parameter in the formula `y ∈ p`.
-/
theorem mem_DefZF_of_mem {a x : ZFSet.{u}} (ha : a.IsTransitive)
    (hx : x ∈ a) : x ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  refine ⟨ha.subset_of_mem hx, 1, (fun _ => ⟨x, hx⟩),
    .mem (Fin.last 1) (Fin.castSucc (0 : Fin 1)), ?_⟩
  intro y
  change y.1 ∈ x ↔ y.1 ∈ x
  rfl

/-- A transitive set is contained in its definable powerset. -/
theorem ZFSet.IsTransitive.subset_DefZF {a : ZFSet.{u}}
    (ha : a.IsTransitive) : a ⊆ DefZF a := by
  intro x hx
  exact mem_DefZF_of_mem ha hx

/-- The definable powerset of a transitive set is again transitive. -/
theorem ZFSet.IsTransitive.defZF {a : ZFSet.{u}}
    (ha : a.IsTransitive) : (DefZF a).IsTransitive := by
  intro z hz x hx
  have hza : z ⊆ a := (mem_DefZF_iff.mp hz).1
  exact mem_DefZF_of_mem ha (hza hx)



/-!
### The internally represented constructible hierarchy

Every value of `LStageZF` is an actual `ZFSet`.  At a limit ordinal `l`, the
index type `Set.Iio l` is small in universe `u`; `replacementRangeZF` first
forms the range of the preceding levels as a ZFC set and `limitUnionZF` then
applies internal union.  This use of `ZFSet.image` is the ambient,
metatheoretic Replacement step in the standard external recursion defining
`L`.  Mathlib's class `ZFSet.Definable` means that a function lifts to `PSet`;
it does not assert object-language first-order definability in `L`.
-/

/--
The value used by replacement on an internal ordinal code.  On an element
`β.toZFSet ∈ l.toZFSet` this is exactly `Xs β`.
-/
noncomputable def replacementValueZF (l : Ordinal.{u})
    (Xs : ∀ β < l, ZFSet.{u}) (z : ZFSet.{u}) : ZFSet.{u} :=
  if hz : z.rank < l then Xs z.rank hz else ∅

/--
The ambient replacement image of the internal ordinal `l.toZFSet` under the
externally given family `Xs`.  Thus this is an actual `ZFSet` containing
exactly the preceding stages.  No claim is made here that `Xs` is represented
by a function graph inside `L`.
-/
noncomputable def replacementRangeZF (l : Ordinal.{u})
    (Xs : ∀ β < l, ZFSet.{u}) : ZFSet.{u} := by
  let f := replacementValueZF l Xs
  letI : ZFSet.Definable₁ f :=
    Classical.allZFSetDefinable (fun s => f (s 0))
  exact ZFSet.image f l.toZFSet

@[simp]
theorem mem_replacementRangeZF_iff {l : Ordinal.{u}}
    {Xs : ∀ β < l, ZFSet.{u}} {x : ZFSet.{u}} :
    x ∈ replacementRangeZF l Xs ↔
      ∃ β, ∃ hβ : β < l, Xs β hβ = x := by
  simp only [replacementRangeZF, ZFSet.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases Ordinal.mem_toZFSet_iff.mp hz with ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, by simp [replacementValueZF, hβ]⟩
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨β.toZFSet, ?_, ?_⟩
    · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ
    · simp [replacementValueZF, hβ]

/-- Internal union of the replacement range of all earlier stages. -/
noncomputable def limitUnionZF (l : Ordinal.{u})
    (Xs : ∀ β < l, ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (replacementRangeZF l Xs)

@[simp]
theorem mem_limitUnionZF_iff {l : Ordinal.{u}}
    {Xs : ∀ β < l, ZFSet.{u}} {x : ZFSet.{u}} :
    x ∈ limitUnionZF l Xs ↔
      ∃ β, ∃ hβ : β < l, x ∈ Xs β hβ := by
  simp [limitUnionZF]

/-- A union of a transitive family of stages is transitive. -/
theorem limitUnionZF_isTransitive {l : Ordinal.{u}}
    {Xs : ∀ β < l, ZFSet.{u}}
    (hXs : ∀ β hβ, (Xs β hβ).IsTransitive) :
    (limitUnionZF l Xs).IsTransitive := by
  intro y hy z hz
  rcases mem_limitUnionZF_iff.mp hy with ⟨β, hβ, hyβ⟩
  exact mem_limitUnionZF_iff.mpr
    ⟨β, hβ, (hXs β hβ).mem_trans hz hyβ⟩

/--
The internally represented constructible hierarchy:

* `LStageZF 0 = ∅`;
* `LStageZF (α + 1) = DefZF (LStageZF α)`;
* `LStageZF l = ⋃ β < l, LStageZF β` at a nonzero limit `l`.
-/
noncomputable def LStageZF (α : Ordinal.{u}) : ZFSet.{u} :=
  α.limitRecOn
    ∅
    (fun _ a => DefZF a)
    (fun l _ Ls => limitUnionZF l Ls)

@[simp]
theorem LStageZF_zero : LStageZF (0 : Ordinal.{u}) = ∅ := by
  simp [LStageZF]

theorem LStageZF_succ (α : Ordinal.{u}) :
    LStageZF (Order.succ α) = DefZF (LStageZF α) := by
  change
    Ordinal.limitRecOn (Order.succ α) ∅ (fun _ a => DefZF a)
        (fun l _ Ls => limitUnionZF l Ls) =
      DefZF
        (Ordinal.limitRecOn α ∅ (fun _ a => DefZF a)
          (fun l _ Ls => limitUnionZF l Ls))
  rw [Order.succ_eq_add_one, Ordinal.limitRecOn_add_one]

theorem LStageZF_limit {l : Ordinal.{u}} (hl : Order.IsSuccLimit l) :
    LStageZF l = limitUnionZF l (fun β _ => LStageZF β) := by
  simp only [LStageZF, Ordinal.limitRecOn_limit l _ _ _ hl]

@[simp]
theorem mem_LStageZF_limit_iff {l : Ordinal.{u}} (hl : Order.IsSuccLimit l)
    {x : ZFSet.{u}} :
    x ∈ LStageZF l ↔ ∃ β < l, x ∈ LStageZF β := by
  rw [LStageZF_limit hl]
  simp

/-- Every level of the constructible hierarchy is a transitive ZFC set. -/
theorem LStageZF_isTransitive (α : Ordinal.{u}) :
    (LStageZF α).IsTransitive := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      rw [LStageZF_zero]
      exact ZFSet.isTransitive_empty
  | add_one α ih =>
      rw [← Order.succ_eq_add_one, LStageZF_succ]
      exact ZFSet.IsTransitive.defZF ih
  | limit l hl ih =>
      rw [LStageZF_limit hl]
      exact limitUnionZF_isTransitive (fun β hβ => ih β hβ)

/-- Each constructible level is contained in its successor. -/
theorem LStageZF_subset_succ (α : Ordinal.{u}) :
    LStageZF α ⊆ LStageZF (Order.succ α) := by
  rw [LStageZF_succ]
  exact ZFSet.IsTransitive.subset_DefZF (LStageZF_isTransitive α)

/-- Each level itself occurs as an element of its successor level. -/
theorem LStageZF_mem_succ (α : Ordinal.{u}) :
    LStageZF α ∈ LStageZF (Order.succ α) := by
  rw [LStageZF_succ]
  exact self_mem_DefZF (LStageZF α)

/-- The constructible hierarchy is monotone in its ordinal index. -/
theorem LStageZF_mono :
    Monotone (LStageZF : Ordinal.{u} → ZFSet.{u}) := by
  intro α β hαβ
  induction β using Ordinal.limitRecOn generalizing α with
  | zero =>
      have hα : α = 0 := le_antisymm hαβ bot_le
      subst α
      exact le_rfl
  | add_one β ih =>
      rw [← Order.succ_eq_add_one] at hαβ ⊢
      rcases Order.le_succ_iff_eq_or_le.mp hαβ with h | h
      · subst α
        exact le_rfl
      · exact (ih h).trans (LStageZF_subset_succ β)
  | limit l hl ih =>
      rcases hαβ.eq_or_lt with h | h
      · subst α
        exact le_rfl
      · intro x hx
        exact (mem_LStageZF_limit_iff hl).mpr ⟨α, h, hx⟩







/-- The constructible universe `L`, represented externally because it is a proper class. -/
def ConstructibleUniverse : Set ZFSet.{u} :=
  {x | ∃ α : Ordinal.{u}, x ∈ LStageZF α}

/-- The constructible universe `L`, represented externally as a class. -/
abbrev L : Set ZFSet.{u} := ConstructibleUniverse

/-- A ZFC set is constructible when it occurs in some internal level. -/
def IsConstructible (x : ZFSet.{u}) : Prop :=
  x ∈ L



@[simp]
theorem mem_L_iff {x : ZFSet.{u}} :
    x ∈ L ↔ ∃ α : Ordinal.{u}, x ∈ LStageZF α :=
  Iff.rfl

@[simp]
theorem isConstructible_iff {x : ZFSet.{u}} :
    IsConstructible x ↔ ∃ α : Ordinal.{u}, x ∈ LStageZF α :=
  Iff.rfl

theorem LStageZF_subset_constructibleUniverse (α : Ordinal.{u}) :
    (LStageZF α : Set ZFSet.{u}) ⊆ ConstructibleUniverse := by
  intro x hx
  exact ⟨α, hx⟩

/-- Every internally represented level is itself constructible. -/
theorem LStageZF_mem_L (α : Ordinal.{u}) : LStageZF α ∈ L := by
  exact ⟨Order.succ α, LStageZF_mem_succ α⟩

/-- The empty set belongs to the constructible universe. -/
theorem empty_mem_L : (∅ : ZFSet.{u}) ∈ L := by
  simpa using LStageZF_mem_L (0 : Ordinal.{u})

/-- Any two constructible sets occur together in a common level. -/
theorem exists_common_LStage {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    ∃ α : Ordinal.{u}, x ∈ LStageZF α ∧ y ∈ LStageZF α := by
  rcases hx with ⟨α, hxα⟩
  rcases hy with ⟨β, hyβ⟩
  exact ⟨max α β,
    LStageZF_mono (le_max_left α β) hxα,
    LStageZF_mono (le_max_right α β) hyβ⟩

/-- Every finite tuple of constructible parameters occurs in one common level. -/
theorem exists_LStage_for_tuple {n : Nat}
    (s : Tuple ZFSet.{u} n) (hs : ∀ i, s i ∈ L) :
    ∃ α : Ordinal.{u}, ∀ i, s i ∈ LStageZF α := by
  induction n with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
      have hsInit : ∀ i : Fin n, s i.castSucc ∈ L :=
        fun i => hs i.castSucc
      rcases ih (fun i => s i.castSucc) hsInit with ⟨α, hα⟩
      rcases hs (Fin.last n) with ⟨β, hβ⟩
      refine ⟨max α β, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact LStageZF_mono (le_max_right α β) hβ
      · exact LStageZF_mono (le_max_left α β) (hα j)

/-- The constructible universe is closed under unordered pairing. -/
theorem pair_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    ({x, y} : ZFSet.{u}) ∈ L := by
  rcases exists_common_LStage hx hy with ⟨α, hxα, hyα⟩
  refine ⟨Order.succ α, ?_⟩
  rw [LStageZF_succ]
  exact pair_mem_DefZF hxα hyα

/-- The constructible universe is closed under singleton formation. -/
theorem singleton_mem_L {x : ZFSet.{u}} (hx : x ∈ L) :
    ({x} : ZFSet.{u}) ∈ L := by
  simpa using pair_mem_L hx hx

/-- The Kuratowski ordered pair of two constructible sets is constructible. -/
theorem orderedPair_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    ZFSet.pair x y ∈ L := by
  change ({{x}, {x, y}} : ZFSet.{u}) ∈ L
  exact pair_mem_L (singleton_mem_L hx) (pair_mem_L hx hy)

/-- The constructible universe is closed under internal union. -/
theorem sUnion_mem_L {x : ZFSet.{u}} (hx : x ∈ L) :
    ZFSet.sUnion x ∈ L := by
  rcases hx with ⟨α, hxα⟩
  refine ⟨Order.succ α, ?_⟩
  rw [LStageZF_succ]
  exact sUnion_mem_DefZF (LStageZF_isTransitive α) hxα

/-- The constructible universe is closed under binary union. -/
theorem union_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    x ∪ y ∈ L := by
  rw [← ZFSet.sUnion_pair]
  exact sUnion_mem_L (pair_mem_L hx hy)

/-- The constructible universe is closed under binary intersection. -/
theorem inter_mem_L {x y : ZFSet.{u}} (hx : x ∈ L) (hy : y ∈ L) :
    x ∩ y ∈ L := by
  rcases exists_common_LStage hx hy with ⟨α, hxα, hyα⟩
  refine ⟨Order.succ α, ?_⟩
  rw [LStageZF_succ]
  exact inter_mem_DefZF (LStageZF_isTransitive α) hxα hyα



/-- The constructible universe is transitive as an external class. -/
theorem mem_L_of_mem {x y : ZFSet.{u}} (hxy : x ∈ y) (hy : y ∈ L) : x ∈ L := by
  rcases hy with ⟨α, hyα⟩
  exact ⟨α, (LStageZF_isTransitive α).mem_trans hxy hyα⟩



end ZFC

end Constructible
end CUAdapterModule0



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0 -/
section CUAdapterModule1
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Bounded formulas for the constructible hierarchy

This file introduces an intrinsically scoped syntax for `Δ₀` formulas in the
language of set theory.  Quantifiers are bounded syntactically.  The syntax is
translated to `Constructible.FOFormula`, and its semantics is proved absolute
between a transitive `ZFSet` and the ambient `ZFSet` universe.
-/


universe u

namespace Constructible

/-- Prepend one coordinate to a tuple. -/
def tupleCons {A : Type u} {n : Nat} (x : A) (s : Tuple A n) :
    Tuple A (n + 1) :=
  Fin.cases x s

@[simp]
theorem tupleCons_zero {A : Type u} {n : Nat} (x : A) (s : Tuple A n) :
    tupleCons x s 0 = x := by
  simp [tupleCons]

@[simp]
theorem tupleCons_succ {A : Type u} {n : Nat} (x : A) (s : Tuple A n)
    (i : Fin n) : tupleCons x s i.succ = s i := by
  simp [tupleCons]

/-- Appending a final coordinate commutes with prepending a first one. -/
@[simp]
theorem snoc_tupleCons {A : Type u} {n : Nat}
    (head : A) (s : Tuple A n) (last : A) :
    snoc (tupleCons head s) last = tupleCons head (snoc s last) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snoc_last]
    change last = tupleCons head (snoc s last) (Fin.last n).succ
    rw [tupleCons_succ, snoc_last]
  · rw [snoc_castSucc]
    refine Fin.cases ?_ (fun k => ?_) j
    · change head = tupleCons head (snoc s last) 0
      rw [tupleCons_zero]
    · change
        tupleCons head s k.succ =
          tupleCons head (snoc s last) (k.castSucc).succ
      rw [tupleCons_succ, tupleCons_succ, snoc_castSucc]

/--
Intrinsically scoped bounded formulas.  In `boundedEx i φ`, the new witness is
the last variable of `φ` and is required to belong to the old variable `i`.
-/
inductive Delta0Formula : Nat → Type
  | mem {n : Nat} (i j : Fin n) : Delta0Formula n
  | eq {n : Nat} (i j : Fin n) : Delta0Formula n
  | neg {n : Nat} (φ : Delta0Formula n) : Delta0Formula n
  | conj {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n
  | boundedEx {n : Nat} (i : Fin n) (φ : Delta0Formula (n + 1)) :
      Delta0Formula n

namespace Delta0Formula

/-- Tarskian semantics for bounded formulas over a relation `E`. -/
@[simp]
def Satisfies {A : Type u} (E : A → A → Prop) :
    {n : Nat} → Delta0Formula n → Tuple A n → Prop
  | _, .mem i j, s => E (s i) (s j)
  | _, .eq i j, s => s i = s j
  | _, .neg φ, s => ¬Satisfies E φ s
  | _, .conj φ ψ, s => Satisfies E φ s ∧ Satisfies E ψ s
  | _, .boundedEx i φ, s =>
      ∃ x : A, E x (s i) ∧ Satisfies E φ (snoc s x)

/-- Forget boundedness annotations and regard a `Δ₀` formula as an `FOFormula`. -/
def toFO : {n : Nat} → Delta0Formula n → FOFormula n
  | _, .mem i j => .mem i j
  | _, .eq i j => .eq i j
  | _, .neg φ => .neg (toFO φ)
  | _, .conj φ ψ => .conj (toFO φ) (toFO ψ)
  | _, .boundedEx i φ => FOFormula.boundedEx i (toFO φ)

/--
Relativize every unbounded quantifier of an `FOFormula` to the set stored in
coordinate zero.  The original variable `i` is consequently moved to
coordinate `i.succ`.
-/
def relativize : {n : Nat} → FOFormula n → Delta0Formula (n + 1)
  | _, .mem i j => .mem i.succ j.succ
  | _, .eq i j => .eq i.succ j.succ
  | _, .neg φ => .neg (relativize φ)
  | _, .conj φ ψ => .conj (relativize φ) (relativize ψ)
  | _, .ex φ => .boundedEx 0 (relativize φ)

/-- The translation to unrestricted first-order syntax preserves semantics. -/
@[simp]
theorem satisfies_toFO {A : Type u} (E : A → A → Prop)
    {n : Nat} (φ : Delta0Formula n) (s : Tuple A n) :
    FOFormula.Satisfies E φ.toFO s ↔ Satisfies E φ s := by
  induction φ with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => simp [toFO, ih]
  | conj φ ψ ihφ ihψ => simp [toFO, ihφ, ihψ]
  | boundedEx i φ ih => simp [toFO, ih]

/-- Bounded disjunction. -/
def disj {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  .neg (.conj (.neg φ) (.neg ψ))

/-- Material implication as a derived bounded connective. -/
def imp {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  disj (.neg φ) ψ

/-- Logical equivalence as a derived bounded connective. -/
def biimp {n : Nat} (φ ψ : Delta0Formula n) : Delta0Formula n :=
  .conj (imp φ ψ) (imp ψ φ)

/-- Bounded universal quantification. -/
def boundedAll {n : Nat} (i : Fin n) (φ : Delta0Formula (n + 1)) :
    Delta0Formula n :=
  .neg (.boundedEx i (.neg φ))

@[simp]
theorem satisfies_disj {A : Type u} {E : A → A → Prop}
    {n : Nat} {φ ψ : Delta0Formula n} {s : Tuple A n} :
    Satisfies E (disj φ ψ) s ↔ Satisfies E φ s ∨ Satisfies E ψ s := by
  classical
  simp only [disj, Satisfies]
  tauto

@[simp]
theorem satisfies_imp {A : Type u} {E : A → A → Prop}
    {n : Nat} {φ ψ : Delta0Formula n} {s : Tuple A n} :
    Satisfies E (imp φ ψ) s ↔
      (Satisfies E φ s → Satisfies E ψ s) := by
  classical
  simp [imp]
  tauto

@[simp]
theorem satisfies_biimp {A : Type u} {E : A → A → Prop}
    {n : Nat} {φ ψ : Delta0Formula n} {s : Tuple A n} :
    Satisfies E (biimp φ ψ) s ↔
      (Satisfies E φ s ↔ Satisfies E ψ s) := by
  classical
  simp [biimp]
  tauto

@[simp]
theorem satisfies_boundedAll {A : Type u} {E : A → A → Prop}
    {n : Nat} {i : Fin n} {φ : Delta0Formula (n + 1)} {s : Tuple A n} :
    Satisfies E (boundedAll i φ) s ↔
      ∀ x : A, E x (s i) → Satisfies E φ (snoc s x) := by
  classical
  simp [boundedAll]

/-- Extend a variable renaming under a new last bounded variable. -/
abbrev liftRename {n m : Nat} (ρ : Fin n → Fin m) :
    Fin (n + 1) → Fin (m + 1) :=
  FOFormula.liftRename ρ

/-- Rename all free variables of a bounded formula. -/
def rename {n m : Nat} (ρ : Fin n → Fin m) :
    Delta0Formula n → Delta0Formula m
  | .mem i j => .mem (ρ i) (ρ j)
  | .eq i j => .eq (ρ i) (ρ j)
  | .neg φ => .neg (rename ρ φ)
  | .conj φ ψ => .conj (rename ρ φ) (rename ρ ψ)
  | .boundedEx i φ => .boundedEx (ρ i) (rename (liftRename ρ) φ)

/-- Renaming bounded formulas composes their assignments. -/
@[simp]
theorem satisfies_rename {A : Type u} (E : A → A → Prop)
    {n m : Nat} (φ : Delta0Formula n) (ρ : Fin n → Fin m)
    (s : Tuple A m) :
    Satisfies E (rename ρ φ) s ↔
      Satisfies E φ (fun i => s (ρ i)) := by
  induction φ generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => simp [rename, ih]
  | conj φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | boundedEx i φ ih =>
      simp only [rename, Satisfies, ih]
      constructor
      · rintro ⟨x, hx, hφ⟩
        rw [FOFormula.snoc_comp_liftRename] at hφ
        exact ⟨x, hx, hφ⟩
      · rintro ⟨x, hx, hφ⟩
        refine ⟨x, hx, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hφ

/-! ## Absoluteness -/

/-- Forget subtype proofs in an assignment into `ZFCarrier a`. -/
def val {a : ZFSet.{u}} {n : Nat} (s : Tuple (ZFCarrier a) n) :
    Tuple ZFSet.{u} n :=
  fun i => (s i).1

@[simp]
theorem val_apply {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i : Fin n) :
    val s i = (s i).1 :=
  rfl

/-- Taking underlying values commutes with appending one subtype element. -/
@[simp]
theorem val_snoc {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (x : ZFCarrier a) :
    val (snoc s x) = snoc (val s) x.1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp







/--
`Δ₀` formulas are absolute between a transitive set and the ambient ZFC
universe, for assignments whose entries lie in that set.
-/
theorem satisfies_absolute {a : ZFSet.{u}} (ha : a.IsTransitive)
    {n : Nat} (φ : Delta0Formula n) (s : Tuple (ZFCarrier a) n) :
    Satisfies (zfCarrierMem a) φ s ↔
      Satisfies (fun x y : ZFSet.{u} => x ∈ y) φ (val s) := by
  induction φ with
  | mem i j => rfl
  | eq i j => exact Subtype.ext_iff
  | neg φ ih => simp only [Satisfies, ih]
  | conj φ ψ ihφ ihψ => simp only [Satisfies, ihφ, ihψ]
  | boundedEx i φ ih =>
      constructor
      · rintro ⟨x, hx, hφ⟩
        refine ⟨x.1, hx, ?_⟩
        have habs := (ih (snoc s x)).mp hφ
        simpa only [val_snoc] using habs
      · rintro ⟨x, hx, hφ⟩
        have hxa : x ∈ a := ha.mem_trans hx (s i).2
        let xa : ZFCarrier a := ⟨x, hxa⟩
        refine ⟨xa, hx, ?_⟩
        apply (ih (snoc s xa)).mpr
        simpa only [val_snoc, xa] using hφ



end Delta0Formula

end Constructible
end CUAdapterModule1



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Godel -/
section CUAdapterModule2
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Gödel operations and rudimentary closure

This file implements the standard Jensen--Devlin basis `F₀, ..., F₈` of
rudimentary (Gödel) operations on Mathlib's internal `ZFSet` universe.  Tuples
are right-associated Kuratowski pairs:

`⟨x, y, z⟩ = ⟨x, ⟨y, z⟩⟩`.

The resulting `rudimentaryClosure U` starts from `U ∪ {U}`.  The candidate
Gödel presentation of the definable powerset is then

`powerset U ∩ rudimentaryClosure U`.

Its equality with `Constructible.DefZF U` for transitive `U` is deliberately
not built into the definition; it is a theorem to be established separately.
-/


open Set

universe u

namespace Constructible.Godel

/-- A right-associated Kuratowski triple. -/
def triple (x y z : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair x (ZFSet.pair y z)

/-- A set containing every possible component of a Kuratowski pair in `r`. -/
def pairField (r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.sUnion r)

theorem pair_left_mem_pairField {r x y : ZFSet.{u}}
    (h : ZFSet.pair x y ∈ r) : x ∈ pairField r := by
  rw [pairField, ZFSet.mem_sUnion]
  refine ⟨{x}, ?_, by simp⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨ZFSet.pair x y, h, by simp [ZFSet.pair]⟩

theorem pair_right_mem_pairField {r x y : ZFSet.{u}}
    (h : ZFSet.pair x y ∈ r) : y ∈ pairField r := by
  rw [pairField, ZFSet.mem_sUnion]
  refine ⟨{x, y}, ?_, by simp⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨ZFSet.pair x y, h, by simp [ZFSet.pair]⟩

/-- `F₀(x,y) = {x,y}`. -/
def F0 (x y : ZFSet.{u}) : ZFSet.{u} :=
  {x, y}

/-- `F₁(x,y) = x \ y`. -/
def F1 (x y : ZFSet.{u}) : ZFSet.{u} :=
  x \ y

/-- `F₂(x,y) = x × y`. -/
def F2 (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod x y

/--
`F₃(x,y) = {⟨u,z,v⟩ | z ∈ x ∧ ⟨u,v⟩ ∈ y}`.
-/
def F3 (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun t => ∃ u z v, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ t = triple u z v)
    (ZFSet.prod (pairField y) (ZFSet.prod x (pairField y)))

/--
`F₄(x,y) = {⟨u,v,z⟩ | z ∈ x ∧ ⟨u,v⟩ ∈ y}`.
-/
def F4 (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun t => ∃ u v z, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ t = triple u v z)
    (ZFSet.prod (pairField y) (ZFSet.prod (pairField y) x))

/-- `F₅(x,y) = ⋃x`; the second argument is intentionally unused. -/
def F5 (x _y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion x

/--
`F₆(x,y) = dom* x = {z | ∃ w, ⟨w,z⟩ ∈ x}`; the graph convention
places inputs in the second coordinate.
-/
def F6 (x _y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ w, ZFSet.pair w z ∈ x) (pairField x)

/-- `F₇(x,y) = {⟨z,w⟩ | z,w ∈ x ∧ z ∈ w}`. -/
def F7 (x _y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pairSep (fun z w => z ∈ w) x x

/-- The fiber `x * z = {w | ⟨w,z⟩ ∈ x}`. -/
def fiber (x z : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => ZFSet.pair w z ∈ x) (pairField x)

/-- `F₈(x,y) = {x * z | z ∈ y}`. -/
noncomputable def F8 (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun z : Constructible.ZFCarrier y => fiber x z.1)

@[simp]
theorem mem_F0_iff {x y z : ZFSet.{u}} : z ∈ F0 x y ↔ z = x ∨ z = y := by
  simp [F0]

@[simp]
theorem mem_F1_iff {x y z : ZFSet.{u}} : z ∈ F1 x y ↔ z ∈ x ∧ z ∉ y := by
  simp [F1]

@[simp]
theorem mem_F2_iff {x y z : ZFSet.{u}} :
    z ∈ F2 x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = ZFSet.pair a b := by
  simp [F2]

@[simp]
theorem mem_F3_iff {x y t : ZFSet.{u}} :
    t ∈ F3 x y ↔
      ∃ u z v, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ t = triple u z v := by
  constructor
  · exact fun h => (ZFSet.mem_sep.mp h).2
  · rintro ⟨u, z, v, hz, huv, rfl⟩
    apply ZFSet.mem_sep.mpr
    refine ⟨?_, ⟨u, z, v, hz, huv, rfl⟩⟩
    rw [triple, ZFSet.pair_mem_prod, ZFSet.pair_mem_prod]
    exact ⟨pair_left_mem_pairField huv, hz, pair_right_mem_pairField huv⟩

@[simp]
theorem mem_F4_iff {x y t : ZFSet.{u}} :
    t ∈ F4 x y ↔
      ∃ u v z, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ t = triple u v z := by
  constructor
  · exact fun h => (ZFSet.mem_sep.mp h).2
  · rintro ⟨u, v, z, hz, huv, rfl⟩
    apply ZFSet.mem_sep.mpr
    refine ⟨?_, ⟨u, v, z, hz, huv, rfl⟩⟩
    rw [triple, ZFSet.pair_mem_prod, ZFSet.pair_mem_prod]
    exact ⟨pair_left_mem_pairField huv, pair_right_mem_pairField huv, hz⟩

@[simp]
theorem mem_F5_iff {x y z : ZFSet.{u}} :
    z ∈ F5 x y ↔ ∃ w ∈ x, z ∈ w := by
  simp [F5]

@[simp]
theorem mem_F6_iff {x y z : ZFSet.{u}} :
    z ∈ F6 x y ↔ ∃ w, ZFSet.pair w z ∈ x := by
  constructor
  · exact fun h => (ZFSet.mem_sep.mp h).2
  · rintro ⟨w, hw⟩
    exact ZFSet.mem_sep.mpr ⟨pair_right_mem_pairField hw, ⟨w, hw⟩⟩

@[simp]
theorem mem_F7_iff {x y q : ZFSet.{u}} :
    q ∈ F7 x y ↔
      ∃ z ∈ x, ∃ w ∈ x, q = ZFSet.pair z w ∧ z ∈ w := by
  simp [F7]

@[simp]
theorem mem_fiber_iff {x z w : ZFSet.{u}} :
    w ∈ fiber x z ↔ ZFSet.pair w z ∈ x := by
  constructor
  · exact fun h => (ZFSet.mem_sep.mp h).2
  · intro h
    exact ZFSet.mem_sep.mpr ⟨pair_left_mem_pairField h, h⟩

@[simp]
theorem mem_F8_iff {x y q : ZFSet.{u}} :
    q ∈ F8 x y ↔ ∃ z ∈ y, q = fiber x z := by
  simp [F8, eq_comm]

/-- Uniform access to the nine Gödel operations. -/
noncomputable def op (i : Fin 9) (x y : ZFSet.{u}) : ZFSet.{u} :=
  match i.1 with
  | 0 => F0 x y
  | 1 => F1 x y
  | 2 => F2 x y
  | 3 => F3 x y
  | 4 => F4 x y
  | 5 => F5 x y
  | 6 => F6 x y
  | 7 => F7 x y
  | 8 => F8 x y
  | _ => ∅

/-- One closure step under all nine binary operations. -/
noncomputable def rudimentaryStep (a : ZFSet.{u}) : ZFSet.{u} :=
  a ∪ ZFSet.range
    (fun p : Fin 9 × (Constructible.ZFCarrier a × Constructible.ZFCarrier a) =>
      op p.1 p.2.1.1 p.2.2.1)

@[simp]
theorem mem_rudimentaryStep_iff {a z : ZFSet.{u}} :
    z ∈ rudimentaryStep a ↔
      z ∈ a ∨
        ∃ i : Fin 9, ∃ x ∈ a, ∃ y ∈ a, op i x y = z := by
  rw [rudimentaryStep, ZFSet.mem_union, ZFSet.mem_range]
  constructor
  · rintro (hz | ⟨p, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨p.1, p.2.1.1, p.2.1.2, p.2.2.1, p.2.2.2, rfl⟩
  · rintro (hz | ⟨i, x, hx, y, hy, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨⟨i, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩, rfl⟩

theorem subset_rudimentaryStep (a : ZFSet.{u}) : a ⊆ rudimentaryStep a := by
  intro z hz
  exact mem_rudimentaryStep_iff.mpr (Or.inl hz)



/-- The `n`-th finite closure stage. -/
noncomputable def rudimentaryIter (seed : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => seed
  | n + 1 => rudimentaryStep (rudimentaryIter seed n)

/-- Closure of a set under all nine Gödel operations. -/
noncomputable def closure (seed : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion (rudimentaryIter seed)

@[simp]
theorem mem_closure_iff {seed z : ZFSet.{u}} :
    z ∈ closure seed ↔ ∃ n : Nat, z ∈ rudimentaryIter seed n := by
  simp [closure]

theorem rudimentaryIter_subset_succ (seed : ZFSet.{u}) (n : Nat) :
    rudimentaryIter seed n ⊆ rudimentaryIter seed (n + 1) := by
  exact subset_rudimentaryStep _

theorem rudimentaryIter_mono (seed : ZFSet.{u}) {m n : Nat} (hmn : m ≤ n) :
    rudimentaryIter seed m ⊆ rudimentaryIter seed n := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih =>
      exact ih.trans (rudimentaryIter_subset_succ seed n)



theorem seed_subset_closure (seed : ZFSet.{u}) : seed ⊆ closure seed := by
  intro z hz
  exact mem_closure_iff.mpr ⟨0, hz⟩



/-- The finite closure really is closed under every operation in the basis. -/
theorem op_mem_closure {seed x y : ZFSet.{u}} {i : Fin 9}
    (hx : x ∈ closure seed) (hy : y ∈ closure seed) :
    op i x y ∈ closure seed := by
  rcases mem_closure_iff.mp hx with ⟨m, hm⟩
  rcases mem_closure_iff.mp hy with ⟨n, hn⟩
  let k := max m n
  have hxk : x ∈ rudimentaryIter seed k :=
    rudimentaryIter_mono seed (Nat.le_max_left m n) hm
  have hyk : y ∈ rudimentaryIter seed k :=
    rudimentaryIter_mono seed (Nat.le_max_right m n) hn
  apply mem_closure_iff.mpr
  refine ⟨k + 1, ?_⟩
  exact mem_rudimentaryStep_iff.mpr
    (Or.inr ⟨i, x, hxk, y, hyk, rfl⟩)

/-- A set is closed under the Jensen--Devlin basis of Gödel operations. -/
def ClosedUnderOps (a : ZFSet.{u}) : Prop :=
  ∀ (i : Fin 9) (x y : ZFSet.{u}), x ∈ a → y ∈ a → op i x y ∈ a

/-- Every `closure seed` is closed under all nine operations. -/
theorem closure_closedUnderOps (seed : ZFSet.{u}) :
    ClosedUnderOps (closure seed) := by
  intro i x y hx hy
  exact op_mem_closure hx hy

/--
`closure seed` is the least internally represented set containing `seed` and
closed under all nine operations.
-/
theorem closure_minimal {seed a : ZFSet.{u}} (hseed : seed ⊆ a)
    (ha : ClosedUnderOps a) : closure seed ⊆ a := by
  have hiter : ∀ n : Nat, rudimentaryIter seed n ⊆ a := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
        intro z hz
        rcases mem_rudimentaryStep_iff.mp hz with
          hz | ⟨i, x, hx, y, hy, rfl⟩
        · exact ih hz
        · exact ha i x y (ih hx) (ih hy)
  intro z hz
  rcases mem_closure_iff.mp hz with ⟨n, hn⟩
  exact hiter n hn

/-- Closing an already closed finite-operation closure adds no new sets. -/
@[simp]
theorem closure_idem (seed : ZFSet.{u}) :
    closure (closure seed) = closure seed := by
  apply le_antisymm
  · exact closure_minimal Set.Subset.rfl (closure_closedUnderOps seed)
  · exact seed_subset_closure (closure seed)

/-- The seed `U ∪ {U}` used in the Gödel presentation of `Def(U)`. -/
def rudimentarySeed (U : ZFSet.{u}) : ZFSet.{u} :=
  insert U U

@[simp]
theorem mem_rudimentarySeed_iff {U z : ZFSet.{u}} :
    z ∈ rudimentarySeed U ↔ z = U ∨ z ∈ U := by
  simp [rudimentarySeed]

/-- Rudimentary closure of `U ∪ {U}`. -/
noncomputable def rudimentaryClosure (U : ZFSet.{u}) : ZFSet.{u} :=
  closure (rudimentarySeed U)

theorem subset_rudimentaryClosure (U : ZFSet.{u}) :
    U ⊆ rudimentaryClosure U := by
  intro z hz
  exact seed_subset_closure _ (mem_rudimentarySeed_iff.mpr (Or.inr hz))

theorem self_mem_rudimentaryClosure (U : ZFSet.{u}) :
    U ∈ rudimentaryClosure U :=
  seed_subset_closure _ (mem_rudimentarySeed_iff.mpr (Or.inl rfl))

theorem op_mem_rudimentaryClosure {U x y : ZFSet.{u}} {i : Fin 9}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    op i x y ∈ rudimentaryClosure U :=
  op_mem_closure hx hy



/--
The Gödel-operations candidate for `Def(U)`.  For transitive `U`, the classical
Gödel theorem identifies this set with `Constructible.DefZF U`.
-/
noncomputable def godelDef (U : ZFSet.{u}) : ZFSet.{u} :=
  U.powerset ∩ rudimentaryClosure U

@[simp]
theorem mem_godelDef_iff {U z : ZFSet.{u}} :
    z ∈ godelDef U ↔ z ⊆ U ∧ z ∈ rudimentaryClosure U := by
  simp [godelDef]







@[simp]
theorem godelDef_empty : godelDef (∅ : ZFSet.{u}) = {∅} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    have hz0 : z = ∅ := (ZFSet.eq_empty z).2 fun y hy =>
      ZFSet.notMem_empty y ((mem_godelDef_iff.mp hz).1 hy)
    simp [hz0]
  · intro hz
    have hz0 : z = ∅ := by simpa using hz
    subst z
    exact mem_godelDef_iff.mpr
      ⟨Set.Subset.rfl, self_mem_rudimentaryClosure (∅ : ZFSet.{u})⟩

/-- The Gödel-operation and formula presentations agree at the empty stage. -/
theorem DefZF_eq_godelDef_empty :
    Constructible.DefZF (∅ : ZFSet.{u}) = godelDef ∅ := by
  rw [Constructible.DefZF_empty, godelDef_empty]

end Constructible.Godel
end CUAdapterModule2


