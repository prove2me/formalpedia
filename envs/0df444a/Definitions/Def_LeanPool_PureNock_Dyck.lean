-- Prove2me | Definitions.Def_LeanPool_PureNock_Dyck
-- name    : LeanPool_PureNock_Dyck
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:09.830001+00:00
-- url     : https://prove2.me/theorems/fdff378d-1b0a-4b4e-bf48-74b6646be12f
-- title:
--   Dyck
-- statement:
--   Definitions and structural lemmas for Dyck, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
inductive Dyck : List Bool → Prop
  | eps : Dyck []
  | cat {w₁ w₂ : List Bool} : Dyck w₁ → Dyck w₂ → Dyck (false :: w₁ ++ true :: w₂)
inductive BTree where
  | leaf : BTree
  | node : BTree → BTree → BTree
deriving Repr, DecidableEq, Inhabited
namespace BTree
def size : BTree → Nat
  | .leaf     => 1
  | .node l r => 1 + l.size + r.size
def encode : BTree → List Bool
  | .leaf     => []
  | .node l r => false :: encode l ++ true :: encode r
theorem encode_length_add_one (t : BTree) : (encode t).length + 1 = t.size := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      simp only [encode, size, List.length_cons, List.length_append]
      omega
def decode : Nat → List Bool → Option (BTree × List Bool)
  | 0,         _                => none
  | fuel + 1, (false :: rest) =>
      match decode fuel rest with
      | some (l, true :: rest₁) =>
          match decode fuel rest₁ with
          | some (r, rest₂) => some (.node l r, rest₂)
          | none            => none
      | _ => none
  | _ + 1,     rest            => some (.leaf, rest)
end BTree
end Nock
namespace Nock
namespace BTree
theorem decode_encode :
    ∀ (t : BTree) (fuel : Nat) (rest : List Bool),
      t.size ≤ fuel → (rest = [] ∨ rest.head? = some true) →
      decode fuel (encode t ++ rest) = some (t, rest) := by
  intro t
  induction t with
  | leaf =>
      intro fuel rest _ hrest
      cases fuel with
      | zero => simp [size] at *
      | succ f =>
          simp only [encode, List.nil_append]
          rcases hrest with h | h
          · subst h; rfl
          · cases rest with
            | nil => rfl
            | cons b rs =>
                simp only [List.head?_cons, Option.some.injEq] at h
                subst h; rfl
  | node l r ihl ihr =>
      intro fuel rest hsize hrest
      cases fuel with
      | zero => simp [size] at hsize
      | succ f =>
          -- fuel = f+1, f ≥ size l + size r ≥ size l, size r
          simp only [size] at hsize
          have hfl : l.size ≤ f := by omega
          have hfr : r.size ≤ f := by omega
          -- left subtree: continuation starts with `true`
          have hL := ihl f (true :: (encode r ++ rest)) hfl (Or.inr rfl)
          -- right subtree: continuation is the (open-free) `rest`
          have hR := ihr f rest hfr hrest
          simp only [encode, List.cons_append, List.append_assoc, decode, hL, hR]
theorem encode_injective {t₁ t₂ : BTree} (h : encode t₁ = encode t₂) : t₁ = t₂ := by
  have hlen : t₁.size = t₂.size := by
    have e₁ := encode_length_add_one t₁
    have e₂ := encode_length_add_one t₂
    rw [h] at e₁; omega
  have d₁ : decode t₁.size (encode t₁ ++ []) = some (t₁, []) :=
    decode_encode t₁ t₁.size [] (Nat.le_refl _) (Or.inl rfl)
  have d₂ : decode t₁.size (encode t₂ ++ []) = some (t₂, []) :=
    decode_encode t₂ t₁.size [] (by omega) (Or.inl rfl)
  rw [h] at d₁
  have := d₁.symm.trans d₂
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this.1
end BTree
namespace Noun
def shape : Noun → Nock.BTree
  | .atom _   => .leaf
  | .cell l r => .node l.shape r.shape
def dyckWord (n : Noun) : List Bool := n.shape.encode
def leafList : Noun → List Nat
  | .atom k   => [k]
  | .cell l r => l.leafList ++ r.leafList
@[simp] theorem leafList_length (n : Noun) : n.leafList.length = n.leaves := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp [leafList, leaves, ihl, ihr]
end Noun
namespace BTree
def toBin : BTree → BinaryTree Unit
  | .leaf     => .nil
  | .node l r => .node () (toBin l) (toBin r)
def ofBin : BinaryTree Unit → BTree
  | .nil        => .leaf
  | .node _ l r => .node (ofBin l) (ofBin r)
@[simp] theorem ofBin_toBin (t : BTree) : ofBin (toBin t) = t := by
  induction t <;> simp_all [toBin, ofBin]
@[simp] theorem toBin_ofBin (t : BinaryTree Unit) : toBin (ofBin t) = t := by
  induction t <;> simp_all [toBin, ofBin]
noncomputable def dyckWordsOfLen (lam : ℕ) : Finset (List Bool) :=
  (BinaryTree.treesOfNumNodesEq lam).map
    ⟨fun t => encode (ofBin t), by
      intro a b h
      have := encode_injective h
      have := congrArg toBin this
      simpa using this⟩
end BTree
end Nock


