-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
-- name    : LeanPool_OrderClosures_BanLat_LLexpr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:11:46.437022+00:00
-- url     : https://prove2.me/theorems/8e1efc79-18d2-4331-9c74-0e3cdb3ab646
-- title:
--   LLexpr
-- statement:
--   Definitions and structural lemmas for LLexpr, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Theorems.Thm_nonneg_smul_sup

set_option autoImplicit true
@[expose] public section
@[expose] public section
inductive LLexpr (n : ℕ) where
  | zero : LLexpr n
  | var : Fin n → LLexpr n
  | add : LLexpr n → LLexpr n → LLexpr n
  | smul : ℝ → LLexpr n → LLexpr n
  | sup : LLexpr n → LLexpr n → LLexpr n
  | inf : LLexpr n → LLexpr n → LLexpr n
namespace LLexpr
open scoped BigOperators
variable {n : ℕ}
def eval {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (x : Fin n → X) : LLexpr n → X
  | .zero => 0
  | .var i => x i
  | .add e₁ e₂ => eval x e₁ + eval x e₂
  | .smul r e => r • eval x e
  | .sup e₁ e₂ => eval x e₁ ⊔ eval x e₂
  | .inf e₁ e₂ => eval x e₁ ⊓ eval x e₂
def reindexExpr {m n : ℕ} (f : Fin n → Fin m) : LLexpr n → LLexpr m
  | .zero => .zero
  | .var i => .var (f i)
  | .add e₁ e₂ => .add (reindexExpr f e₁) (reindexExpr f e₂)
  | .smul r e => .smul r (reindexExpr f e)
  | .sup e₁ e₂ => .sup (reindexExpr f e₁) (reindexExpr f e₂)
  | .inf e₁ e₂ => .inf (reindexExpr f e₁) (reindexExpr f e₂)
section Evaluation
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end Evaluation
section Combinations
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
def combinations (x : Fin n → X) : Set X :=
  Set.range (eval x)
end Combinations
def Vanishes (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (e : LLexpr n) : Prop :=
  ∀ x : Fin n → X, eval x e = 0
def smulSupHom {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (r : ℝ) (hr : 0 ≤ r) : SupHom X X where
  toFun := fun z => r • z
  map_sup' := fun a b => nonneg_smul_sup a b r hr
structure SupLinearCombination (n : ℕ) where
  /-- The finite set of coefficient vectors. -/
  coeffs : Finset (Fin n → ℝ)
  /-- Nonemptiness of the coefficient set, avoiding any ambient completeness assumption. -/
  nonempty : coeffs.Nonempty
namespace SupLinearCombination
noncomputable def eval {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (A : SupLinearCombination n)
    (x : Fin n → X) : X :=
  A.coeffs.sup' A.nonempty (Fintype.linearCombination ℝ x)
noncomputable def singleton (a : Fin n → ℝ) : SupLinearCombination n :=
  { coeffs := {a}
    nonempty := Finset.singleton_nonempty a }
noncomputable def add (A B : SupLinearCombination n) : SupLinearCombination n := by
  classical
  exact
    { coeffs := A.coeffs.image₂ (fun a b => a + b) B.coeffs
      nonempty := A.nonempty.image₂ B.nonempty }
noncomputable def sup (A B : SupLinearCombination n) : SupLinearCombination n :=
  { coeffs := A.coeffs ∪ B.coeffs
    nonempty := A.nonempty.mono Finset.subset_union_left }
noncomputable def smul (r : ℝ) (A : SupLinearCombination n) :
    SupLinearCombination n := by
  classical
  exact
    { coeffs := A.coeffs.image fun a => r • a
      nonempty := A.nonempty.image _ }
end SupLinearCombination
structure NormalForm (n : ℕ) where
  /-- The positive finite supremum in the signed representation. -/
  pos : SupLinearCombination n
  /-- The negative finite supremum in the signed representation. -/
  neg : SupLinearCombination n
namespace NormalForm
noncomputable def eval {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N : NormalForm n) (x : Fin n → X) : X :=
  N.pos.eval x - N.neg.eval x
noncomputable def zero : NormalForm n :=
  { pos := SupLinearCombination.singleton (fun _ : Fin n => 0)
    neg := SupLinearCombination.singleton (fun _ : Fin n => 0) }
noncomputable def var (i : Fin n) : NormalForm n :=
  { pos := SupLinearCombination.singleton (Pi.single i (1 : ℝ) : Fin n → ℝ)
    neg := SupLinearCombination.singleton (fun _ : Fin n => 0) }
noncomputable def add (N M : NormalForm n) : NormalForm n :=
  { pos := N.pos.add M.pos
    neg := N.neg.add M.neg }
noncomputable def negate (N : NormalForm n) : NormalForm n :=
  { pos := N.neg
    neg := N.pos }
noncomputable def smul (r : ℝ) (N : NormalForm n) : NormalForm n :=
  if 0 ≤ r then
    { pos := N.pos.smul r
      neg := N.neg.smul r }
  else
    { pos := N.neg.smul (-r)
      neg := N.pos.smul (-r) }
noncomputable def sup (N M : NormalForm n) : NormalForm n :=
  { pos := (N.pos.add M.neg).sup (M.pos.add N.neg)
    neg := N.neg.add M.neg }
noncomputable def inf (N M : NormalForm n) : NormalForm n :=
  negate (sup (negate N) (negate M))
end NormalForm
noncomputable def normalize : LLexpr n → NormalForm n
  | .zero => NormalForm.zero
  | .var i => NormalForm.var i
  | .add e₁ e₂ => NormalForm.add (normalize e₁) (normalize e₂)
  | .smul r e => NormalForm.smul r (normalize e)
  | .sup e₁ e₂ => NormalForm.sup (normalize e₁) (normalize e₂)
  | .inf e₁ e₂ => NormalForm.inf (normalize e₁) (normalize e₂)
end LLexpr


