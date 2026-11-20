-- Prove2me | Definitions.Def_ForbiddenMatrix_ExtremalFunction
-- name    : ForbiddenMatrix_ExtremalFunction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:58:06.445635+00:00
-- url     : https://prove2.me/theorems/6c9a24d2-abf9-42cc-9a43-3dda85799379
-- title:
--   Extremal Function
-- statement:
--   Definitions and structural lemmas for Extremal Function, from Yaël Dillies and the Forbidden Matrix contributors's pinned Forbidden-matrix containment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean

module
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}
open scoped Classical in
noncomputable def density (M : Fin m → Fin n → Prop) : ℕ := #{(i, j) : Fin m × Fin n | M i j}
open scoped Classical in
noncomputable def row_density {n : ℕ} (M : Fin n → Fin n → Prop) (i : Fin n) : ℕ := #{j | M i j}
open scoped Classical in
noncomputable def col_density {n : ℕ} (M : Fin n → Fin n → Prop) (j : Fin n) : ℕ := #{i | M i j}
open scoped Classical in
noncomputable def ex (P : α → β → Prop) (n : ℕ) : ℕ := sup {M : Fin n → Fin n → Prop | ¬ Contains P M} density
def rectPtset (n a₁ b₁ a₂ b₂ : ℕ) : Finset (Fin n × Fin n) :=
  ({a | ↑a ∈ Finset.Ico a₁ b₁} : Finset (Fin n)) ×ˢ ({a | ↑a ∈ Finset.Ico a₂ b₂} : Finset (Fin n))
open scoped Classical in
noncomputable def rectPtsetMatrix {n : ℕ} (M : Fin n → Fin n → Prop) (a₁ b₁ a₂ b₂ : ℕ) : Finset (Fin n × Fin n) :=
  {(a, b) | M a b ∧ (a, b) ∈ rectPtset n a₁ b₁ a₂ b₂}
open scoped Classical in
noncomputable def rectPtsetSubsetMatrix {n : ℕ} (M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) :
    Finset (Fin n × Fin n) := {(a, b) | M a b ∧ (a, b) ∈ R ×ˢ C}


