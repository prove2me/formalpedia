-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
-- name    : LeanPool_DeciSigma1_Semantics_Order
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:34:45.454812+00:00
-- url     : https://prove2.me/theorems/d5166e96-fbee-4793-a17a-a017669420b2
-- title:
--   Order
-- statement:
--   Definitions and structural lemmas for Order, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Semantics
variable {n : ℕ}
def polarity (c : Fin n → Bool) : List (Fin n) → Bool
  | [] => false
  | i :: π => Bool.xor (c i) (polarity c π)
@[simp] theorem pol_nil (c : Fin n → Bool) : polarity c [] = false := rfl
@[simp] theorem pol_cons (c : Fin n → Bool) (i : Fin n) (π : List (Fin n)) :
    polarity c (i :: π) = Bool.xor (c i) (polarity c π) := rfl
@[simp] theorem pol_false (π : List (Fin n)) : polarity (fun _ => false) π = false := by
  induction π with
  | nil => rfl
  | cons i π ih => simp [polarity, ih]
end DeciSigma1.Semantics
namespace DeciSigma1.Semantics.Sym
open DeciSigma1.Semantics.Sym
def LeWithPolarity (p : Bool) (a b : Sym) : Prop := if p then b ≤ a else a ≤ b
def flip : Bool → Sym → Sym
  | false, a => a
  | true, bot => top
  | true, f => f
  | true, top => bot
@[simp] theorem flip_false (a : Sym) : flip false a = a := rfl
@[simp] theorem flip_f (p : Bool) : flip p f = f := by cases p <;> rfl
@[simp] theorem flip_involutive (p : Bool) (a : Sym) : flip p (flip p a) = a := by
  cases p <;> cases a <;> rfl
@[simp] theorem flip_eq_f (p : Bool) (a : Sym) : flip p a = f ↔ a = f := by
  cases p <;> cases a <;> decide
end DeciSigma1.Semantics.Sym
namespace DeciSigma1.Semantics
variable {n : ℕ}
def Tree.normalize (c : Fin n → Bool) (p : Bool) (t : Tree n) : Tree n where
  fn π := (t.fn π).map (Sym.flip (Bool.xor p (polarity c π)))
  wf := by
    constructor
    · simpa using t.wf.1
    · intro π i
      simpa only [Option.isSome_map, Option.map_eq_some_iff, Sym.flip_eq_f,
        exists_eq_right] using t.wf.2 π i
def Tree.dual : Tree n → Tree n := normalize (fun _ => false) true
def FTree.normalize (c : Fin n → Bool) : Bool → FTree n → FTree n
  | p, .bot => if p then .top else .bot
  | p, .top => if p then .bot else .top
  | p, .node a => .node fun i => normalize c (Bool.xor p (c i)) (a i)
def FTree.dual (t : FTree n) : FTree n := t.normalize (fun _ => false) true
end DeciSigma1.Semantics
namespace DeciSigma1.Semantics
variable {n : ℕ}
namespace Tree
def descend (t : Tree n) (i : Fin n) : Tree n :=
  if h : t.fn [] = some Sym.f then t.branch i h else t
def trace (t : Tree n) : List (Fin n) → Tree n
  | [] => t
  | i :: ν => trace (descend t i) ν
def HasLabel (t : Tree n) (ν : List (Fin n)) (s : Sym) : Prop :=
  ∃ τ, τ <+: ν ∧ t.fn τ = some s
end Tree
end DeciSigma1.Semantics
namespace DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
def Tree.Le (c : Fin n → Bool) (t u : Tree n) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → if polarity c π then b ≤ a else a ≤ b
end DeciSigma1.Semantics


