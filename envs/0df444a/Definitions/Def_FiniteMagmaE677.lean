-- Prove2me | Definitions.Def_FiniteMagmaE677
-- name    : FiniteMagmaE677
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-10T06:36:20.836912+00:00
-- url     : https://prove2.me/theorems/b73d92eb-3d59-4152-8899-914880d6ee06
-- title:
--   E677 and E255 for arbitrary binary operations
-- statement:
--   This package defines E677 and E255 for a universe-polymorphic type $A$ with arbitrary total binary operation $\diamond$. E677 means
--
--   $$\forall x,y\in A,\quad x=y\diamond\bigl(x\diamond((y\diamond x)\diamond y)\bigr),$$
--
--   while E255 means
--
--   $$\forall x\in A,\quad x=((x\diamond x)\diamond x)\diamond x.$$
--
--   It also names a fixer, the forward orbit under left multiplication, and the orbit right-collision condition used by Piece 1. None of these definitions assumes associativity, identity, commutativity, or cancellation.
-- source:
--   Equational Theories Project blueprint, Chapter 13, equations (1) and (2), https://teorth.github.io/equational_theories/blueprint/677-chapter.html

import Mathlib.Data.Fintype.Basic

/-! The operation is arbitrary: no associativity, identity, or cancellation is assumed. -/
namespace FiniteMagmaE677

universe u

def E677 {α : Type u} (op : α → α → α) : Prop :=
  ∀ x y : α, x = op y (op x (op (op y x) y))

def E255 {α : Type u} (op : α → α → α) : Prop :=
  ∀ x : α, x = op (op (op x x) x) x

/-- An element whose right product with `x` is `x`. -/
def HasFixerAt {α : Type u} (op : α → α → α) (x : α) : Prop :=
  ∃ y : α, op y x = x

/-- Membership in the forward orbit of `x` under left multiplication by `x`. -/
def InLeftOrbit {α : Type u} (op : α → α → α) (x a : α) : Prop :=
  ∃ i : ℕ, a = (op x)^[i] x

/-- A collision of right products on the left orbit of `x` either is trivial or yields a fixer. -/
def OrbitRightCollisionOrFixer {α : Type u} (op : α → α → α) (x : α) : Prop :=
  ∀ ⦃a b : α⦄,
    InLeftOrbit op x a →
    InLeftOrbit op x b →
    op a x = op b x →
    a = b ∨ HasFixerAt op x

end FiniteMagmaE677


