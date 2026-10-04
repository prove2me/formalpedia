-- Prove2me | Definitions.Def_MSKleene_Core
-- name    : MSKleene_Core
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:26:37.238979+00:00
-- url     : https://prove2.me/theorems/5f833d36-b92b-4929-bb8a-953a393c863f
-- title:
--   Many-sorted algebra: core layer
-- statement:
--   (updated) Many-sorted algebra: core layer. See the mission's other definition items for the surrounding development.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

/-
Many-sorted universal algebra: the core layer for the mission
"A Kleene Theorem for Free Many-Sorted Algebras"
(Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, 2026).

This file fixes the representation of:
  * S-sorted sets and S-sorted subsets                (paper, Section 2.1)
  * S-sorted signatures                                (Definition 2.25)
  * many-sorted Σ-algebras and Σ-homomorphisms         (Definition 2.26)
  * the free Σ-algebra T_Σ(X) as an inductive term type (Definitions 3.1, 3.2)
  * evaluation of terms into an algebra                (universal property, Prop. 3.5)
  * the power Σ-algebra A^℘                            (Proposition 2.32)

Conventions: the set of sorts `S` is a type; finiteness is required by later
results and is carried as an explicit `[Fintype S]` where needed.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

namespace MSKleene

universe u

/-- An `S`-sorted set is a family of types indexed by the sorts. -/
abbrev SSet (S : Type u) : Type (u + 1) := S → Type u

/-- An `S`-sorted map between `S`-sorted sets is a sortwise family of maps. -/
def SMap {S : Type u} (A B : SSet S) : Type u := (s : S) → A s → B s

/-- An `S`-sorted subset of `A`: a sortwise family of subsets. This is the
underlying `S`-sorted set of the power object `A^℘`. -/
def SSub {S : Type u} (A : SSet S) : Type u := (s : S) → Set (A s)

instance {S : Type u} (A : SSet S) : PartialOrder (SSub A) where
  le X Y := ∀ s, X s ⊆ Y s
  le_refl X s := le_refl _
  le_trans X Y Z hXY hYZ s := le_trans (hXY s) (hYZ s)
  le_antisymm X Y hXY hYX := funext fun s => le_antisymm (hXY s) (hYX s)

/-- Kronecker delta `δ^{t,U}`: the `S`-sorted subset that is `U` at sort `t`
and empty elsewhere (Definition 2.5). -/
def delta {S : Type u} [DecidableEq S] {A : SSet S} (t : S) (U : Set (A t)) : SSub A :=
  fun s => if h : s = t then h ▸ U else (∅ : Set (A s))

/-- An `S`-sorted set is finite when the disjoint union of its components is. -/
def SFinite {S : Type u} (A : SSet S) : Prop := Finite (Σ s, A s)

/-! ### Signatures -/

/-- An `S`-sorted signature assigns to an arity `w : List S` and a coarity
`s : S` the set of operation symbols of that rank (Definition 2.25). -/
def Signature (S : Type u) : Type (u + 1) := List S → S → Type u

/-- A signature is **finite** when it has only finitely many operation symbols
in total, across all ranks. -/
def SigFinite {S : Type u} (sig : Signature S) : Prop :=
  Finite ((w : List S) × (s : S) × sig w s)

/-- The argument tuple of arity `w` over an `S`-sorted set `A`: one element of
`A (w[i])` for each position `i`. -/
def Args {S : Type u} (A : SSet S) : List S → Type u
  | [] => PUnit
  | s :: w => A s × Args A w

/-- Map an `S`-sorted map over an argument tuple. -/
def Args.map {S : Type u} {A B : SSet S} (f : SMap A B) :
    {w : List S} → Args A w → Args B w
  | [], _ => PUnit.unit
  | _ :: _, (a, rest) => (f _ a, Args.map f rest)

/-- `Args.All P as` — every component of the argument tuple `as` satisfies `P`. -/
def Args.All {S : Type u} {A : SSet S} (P : (s : S) → A s → Prop) :
    {w : List S} → Args A w → Prop
  | [], _ => True
  | _ :: _, (a, rest) => P _ a ∧ Args.All P rest

@[simp] theorem Args.map_id {S : Type u} {A : SSet S} :
    ∀ {w : List S} (args : Args A w), Args.map (fun _ a => a) args = args
  | [], _ => rfl
  | _ :: _, (a, rest) => congrArg (Prod.mk a) (Args.map_id rest)

theorem Args.map_comp {S : Type u} {A B C : SSet S} (g : SMap B C) (f : SMap A B) :
    ∀ {w : List S} (args : Args A w),
      Args.map (fun s a => g s (f s a)) args = Args.map g (Args.map f args)
  | [], _ => rfl
  | _ :: _, (a, rest) => congrArg (Prod.mk (g _ (f _ a))) (Args.map_comp g f rest)

/-! ### Algebras and homomorphisms -/

/-- A many-sorted `Σ`-algebra: an `S`-sorted carrier together with an
interpretation of every operation symbol (Definition 2.26). -/
structure Algebra {S : Type u} (sig : Signature S) where
  carrier : SSet S
  op : {w : List S} → {s : S} → sig w s → Args carrier w → carrier s

/-- A `Σ`-homomorphism: a sortwise family of maps commuting with every
operation (Definition 2.26). -/
structure Hom {S : Type u} {sig : Signature S} (A B : Algebra sig) where
  toFun : SMap A.carrier B.carrier
  map_op : ∀ {w : List S} {s : S} (σ : sig w s) (args : Args A.carrier w),
    toFun s (A.op σ args) = B.op σ (Args.map toFun args)

/-- The identity homomorphism. -/
def Hom.id {S : Type u} {sig : Signature S} (A : Algebra sig) : Hom A A where
  toFun := fun _ a => a
  map_op := by intro w s σ args; simp

/-- Composition of homomorphisms. -/
def Hom.comp {S : Type u} {sig : Signature S} {A B C : Algebra sig}
    (g : Hom B C) (f : Hom A B) : Hom A C where
  toFun := fun s a => g.toFun s (f.toFun s a)
  map_op := by
    intro w s σ args
    rw [f.map_op, g.map_op, Args.map_comp]

end MSKleene


