-- Prove2me | Definitions.Def_LeanPool_Parikh_Counting
-- name    : LeanPool_Parikh_Counting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:47:26.657861+00:00
-- url     : https://prove2.me/theorems/4d5c44b4-a946-4976-9371-7045a9ab1a2f
-- title:
--   Counting
-- statement:
--   Definitions and structural lemmas for Counting, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped Pointwise
namespace Parikh
abbrev Vector (T : Type*) := T → ℕ
@[expose] def counts {T : Type*} [DecidableEq T] (w : List T) : Vector T := fun a => w.count a
@[expose] def image {T : Type*} [DecidableEq T] (L : Language T) : Set (Vector T) := counts '' L
structure Component (T : Type*) where
  /-- Initial count vector of the linear component. -/
  base : Vector T
  /-- Independently repeatable period vectors, retaining duplicates and zero vectors. -/
  periods : List (Vector T)
abbrev Witness (T : Type*) := List (Component T)
@[expose] def Component.denotation {T : Type*} (c : Component T) : Set (Vector T) :=
  {v | ∃ k : Fin c.periods.length → ℕ,
    v = c.base + ∑ i : Fin c.periods.length, k i • c.periods[i]}
@[expose] def Witness.denotation {T : Type*} (W : Witness T) : Set (Vector T) :=
  {v | ∃ c ∈ W, v ∈ c.denotation}
end Parikh


