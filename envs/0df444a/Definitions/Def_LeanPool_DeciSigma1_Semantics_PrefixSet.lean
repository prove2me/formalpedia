-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
-- name    : LeanPool_DeciSigma1_Semantics_PrefixSet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:32:48.260666+00:00
-- url     : https://prove2.me/theorems/e120ced3-1d35-428e-b35b-9b943cdc3198
-- title:
--   Prefix Set
-- statement:
--   Definitions and structural lemmas for Prefix Set, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/PrefixSet.lean

module
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Nat.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Semantics
variable {n : ℕ}
@[ext] structure PrefixSet (n : ℕ) where
  /-- Paths forming the prefix-closed set. -/
  carrier : Set (List (Fin n))
  prefix_closed : ∀ u v, u ++ v ∈ carrier → u ∈ carrier
namespace PrefixSet
def bot : PrefixSet n := ⟨∅, by simp⟩
def node (a : Fin n → PrefixSet n) : PrefixSet n where
  carrier w := match w with
    | [] => True
    | i :: v => v ∈ (a i).carrier
  prefix_closed := by
    intro u v h
    cases u with
    | nil => trivial
    | cons i u => exact (a i).prefix_closed u v h
instance : PartialOrder (PrefixSet n) where
  le t u := t.carrier ⊆ u.carrier
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := PrefixSet.ext (Set.Subset.antisymm h₁ h₂)
@[simp] theorem mem_bot (w : List (Fin n)) : w ∉ bot.carrier := by simp [bot]
@[simp] theorem nil_mem_node (a : Fin n → PrefixSet n) : [] ∈ (node a).carrier := trivial
@[simp] theorem cons_mem_node (a : Fin n → PrefixSet n) (i : Fin n)
    (w : List (Fin n)) : i :: w ∈ (node a).carrier ↔ w ∈ (a i).carrier := Iff.rfl
@[simp] theorem node_le_node (a b : Fin n → PrefixSet n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w hw
    exact h (show i :: w ∈ (node a).carrier from hw)
  · intro h w hw
    cases w with
    | nil => trivial
    | cons i w => exact h i hw
def residual (t : PrefixSet n) (w : List (Fin n)) : PrefixSet n where
  carrier := {v | w ++ v ∈ t.carrier}
  prefix_closed := by
    intro u v h
    exact t.prefix_closed (w ++ u) v (by simpa [List.append_assoc] using h)
def subtree (t : PrefixSet n) (i : Fin n) : PrefixSet n := t.residual [i]
def univ : PrefixSet n := ⟨Set.univ, fun _ _ _ => trivial⟩
@[simp] theorem node_univ : (node fun _ => univ : PrefixSet n) = univ :=
  PrefixSet.ext (Set.ext fun π => by cases π <;> simp [univ])
@[simp] theorem mem_univ (w : List (Fin n)) : w ∈ (univ : PrefixSet n).carrier := trivial
def complete (d : ℕ) : PrefixSet n where
  carrier := {w | w.length < d}
  prefix_closed u v h := lt_of_le_of_lt (by simp) (show (u ++ v).length < d from h)
end PrefixSet
def IsRegularTree (t : PrefixSet n) : Prop :=
  (Set.range fun w => (t.residual w).carrier).Finite
def IsFiniteTree (t : PrefixSet n) : Prop := t.carrier.Finite
end DeciSigma1.Semantics


