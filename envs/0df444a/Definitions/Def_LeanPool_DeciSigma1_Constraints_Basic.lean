-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
-- name    : LeanPool_DeciSigma1_Constraints_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:36:08.534494+00:00
-- url     : https://prove2.me/theorems/f065d6f3-3ad4-4930-8195-cb9cf05c8158
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Basic.lean

module
public import Mathlib.Data.Fintype.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
public import Mathlib.Tactic.Bound.Init
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Constraints
open DeciSigma1.Semantics
variable {n : ℕ}
inductive LitT (n : ℕ) (V : Type*) where
  | le (u v : V)
  | fLe (a : Fin n → V) (u : V)
  | leF (u : V) (a : Fin n → V)
  | eqBot (u : V)
  | eqTop (u : V)
  deriving DecidableEq
def LitT.map {V W : Type*} (f : V → W) : LitT n V → LitT n W
  | .le u v => .le (f u) (f v)
  | .fLe a u => .fLe (f ∘ a) (f u)
  | .leF u a => .leF (f u) (f ∘ a)
  | .eqBot u => .eqBot (f u)
  | .eqTop u => .eqTop (f u)
def HoldsT {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n) : LitT n V → Prop
  | .le u v => Tree.Le c (ρ u) (ρ v)
  | .fLe a u => Tree.Le c (Semantics.Tree.node (ρ ∘ a)) (ρ u)
  | .leF u a => Tree.Le c (ρ u) (Semantics.Tree.node (ρ ∘ a))
  | .eqBot u => ρ u = Tree.bot
  | .eqTop u => ρ u = Tree.top
def SatT {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (Γ : List (LitT n V)) : Prop := ∀ l ∈ Γ, HoldsT c ρ l
def Covariant.Holds {V : Type*} (ρ : V → Semantics.Tree n) : LitT n V → Prop
  | .le x y => ρ x ≤ ρ y
  | .leF x a => ρ x ≤ Semantics.Tree.node (ρ ∘ a)
  | .fLe a x => Semantics.Tree.node (ρ ∘ a) ≤ ρ x
  | .eqBot x => ρ x = Tree.bot
  | .eqTop x => ρ x = Tree.top
def Covariant.Sat {V : Type*} (ρ : V → Semantics.Tree n) (Γ : List (LitT n V)) : Prop :=
  ∀ l ∈ Γ, Holds ρ l
end DeciSigma1.Constraints


