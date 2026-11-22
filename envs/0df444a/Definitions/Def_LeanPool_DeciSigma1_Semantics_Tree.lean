-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
-- name    : LeanPool_DeciSigma1_Semantics_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:32:47.714073+00:00
-- url     : https://prove2.me/theorems/f37ade53-85c4-46fa-ad8c-ff501f321263
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Semantics
inductive Sym where
  | bot | f | top
  deriving DecidableEq, Repr
namespace Sym
def rank : Sym → Nat
  | bot => 0
  | f => 1
  | top => 2
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]
instance : LinearOrder Sym := LinearOrder.lift' rank rank_injective
@[simp] theorem bot_le (a : Sym) : bot ≤ a := by cases a <;> decide
@[simp] theorem le_top (a : Sym) : a ≤ top := by cases a <;> decide
@[simp] theorem le_bot_iff (a : Sym) : a ≤ bot ↔ a = bot := by
  cases a <;> decide
@[simp] theorem top_le_iff (a : Sym) : top ≤ a ↔ a = top := by
  cases a <;> decide
end Sym
section LivePrefix
variable {n : ℕ}
def IsLivePrefix (labels : List (Fin n) → Sym) (π : List (Fin n)) : Prop :=
  ∀ τ, τ <+: π → τ ≠ π → labels τ = .f
@[simp] theorem isLivePrefix_nil (labels : List (Fin n) → Sym) : IsLivePrefix labels [] := by
  intro τ hp hn
  exact False.elim (hn (List.prefix_nil.mp hp))
end LivePrefix
end DeciSigma1.Semantics
namespace DeciSigma1.Semantics
structure Tree (n : ℕ) where
  /-- Partial node labelling; absent nodes have value `none`. -/
  fn : List (Fin n) → Option Sym
  wf : fn [] ≠ none ∧ ∀ π i, (fn (π ++ [i])).isSome ↔ fn π = some Sym.f
namespace Tree
variable {n : ℕ}
@[ext] theorem ext {t u : Tree n} (h : t.fn = u.fn) : t = u := by
  cases t
  cases u
  cases h
  rfl
theorem root_isSome (t : Tree n) : (t.fn []).isSome :=
  Option.isSome_iff_ne_none.mpr t.wf.1
theorem child_isSome_iff (t : Tree n) (π : List (Fin n)) (i : Fin n) :
    (t.fn (π ++ [i])).isSome ↔ t.fn π = some Sym.f := t.wf.2 π i
theorem domain_append_left (t : Tree n) (π ρ : List (Fin n))
    (h : (t.fn (π ++ ρ)).isSome) : (t.fn π).isSome := by
  induction ρ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton ρ i ih =>
    have hf : t.fn (π ++ ρ) = some Sym.f :=
      (t.child_isSome_iff (π ++ ρ) i).mp (by simpa [List.append_assoc] using h)
    exact ih (by simp [hf])
def bot : Tree n where
  fn
    | [] => some Sym.bot
    | _ :: _ => none
  wf := by
    constructor
    · simp
    · intro π i; cases π <;> simp
def top : Tree n where
  fn
    | [] => some Sym.top
    | _ :: _ => none
  wf := by
    constructor
    · simp
    · intro π i; cases π <;> simp
def node (a : Fin n → Tree n) : Tree n where
  fn
    | [] => some Sym.f
    | i :: w => (a i).fn w
  wf := by
    constructor
    · simp
    · intro w i
      cases w with
      | nil => simpa using (a i).root_isSome
      | cons j w => exact (a j).child_isSome_iff w i
@[simp] theorem bot_fn_nil : (bot : Tree n).fn [] = some Sym.bot := rfl
@[simp] theorem bot_fn_cons (i : Fin n) (π : List (Fin n)) :
    (bot : Tree n).fn (i :: π) = none := rfl
@[simp] theorem top_fn_nil : (top : Tree n).fn [] = some Sym.top := rfl
@[simp] theorem top_fn_cons (i : Fin n) (π : List (Fin n)) :
    (top : Tree n).fn (i :: π) = none := rfl
@[simp] theorem node_fn_nil (a : Fin n → Tree n) : (node a).fn [] = some Sym.f := rfl
@[simp] theorem node_fn_cons (a : Fin n → Tree n) (i : Fin n) (w : List (Fin n)) :
    (node a).fn (i :: w) = (a i).fn w := rfl
def subtree (t : Tree n) (π : List (Fin n)) : Option (Tree n) :=
  if h : (t.fn π).isSome then
    some {
      fn := fun ρ => t.fn (π ++ ρ)
      wf := by
        constructor
        · simpa using Option.isSome_iff_ne_none.mp h
        · intro ρ i
          simpa [List.append_assoc] using t.child_isSome_iff (π ++ ρ) i
    }
  else none
@[simp] theorem subtree_isSome_iff (t : Tree n) (π : List (Fin n)) :
    (t.subtree π).isSome ↔ (t.fn π).isSome := by
  unfold subtree
  split <;> simp_all
theorem fn_cons_eq_none_of_root_ne_f (t : Tree n) (h : t.fn [] ≠ some Sym.f)
    (i : Fin n) (π : List (Fin n)) : t.fn (i :: π) = none := by
  by_contra hsome
  apply h
  apply (t.child_isSome_iff [] i).mp
  exact t.domain_append_left [i] π (Option.isSome_iff_ne_none.mpr hsome)
@[simp] theorem root_eq_bot_iff (t : Tree n) : t.fn [] = some Sym.bot ↔ t = bot := by
  constructor
  · intro h
    apply ext
    funext π
    cases π with
    | nil => exact h
    | cons i π =>
      exact t.fn_cons_eq_none_of_root_ne_f (by simp [h]) i π
  · rintro rfl
    rfl
@[simp] theorem root_eq_top_iff (t : Tree n) : t.fn [] = some Sym.top ↔ t = top := by
  constructor
  · intro h
    apply ext
    funext π
    cases π with
    | nil => exact h
    | cons i π =>
      exact t.fn_cons_eq_none_of_root_ne_f (by simp [h]) i π
  · rintro rfl
    rfl
def branch (t : Tree n) (i : Fin n) (h : t.fn [] = some Sym.f) : Tree n where
  fn := fun π => t.fn (i :: π)
  wf := by
    constructor
    · exact Option.isSome_iff_ne_none.mp ((t.child_isSome_iff [] i).mpr h)
    · intro π j
      exact t.child_isSome_iff (i :: π) j
@[simp] theorem node_eq_node_iff (a b : Fin n → Tree n) :
    node a = node b ↔ a = b := by
  constructor
  · intro h
    funext i
    apply ext
    funext w
    exact congrArg (fun t : Tree n => t.fn (i :: w)) h
  · rintro rfl; rfl
@[simp] theorem bot_ne_top : (bot : Tree n) ≠ top := by
  intro h
  have := congrArg (fun t : Tree n => t.fn []) h
  simp at this
@[simp] theorem node_ne_bot (a : Fin n → Tree n) : node a ≠ bot := by
  intro h
  have := congrArg (fun t : Tree n => t.fn []) h
  simp at this
@[simp] theorem node_ne_top (a : Fin n → Tree n) : node a ≠ top := by
  intro h
  have := congrArg (fun t : Tree n => t.fn []) h
  simp at this
@[simp] theorem top_ne_bot : (top : Tree n) ≠ bot := bot_ne_top.symm
@[simp] theorem bot_ne_node (a : Fin n → Tree n) : bot ≠ node a := (node_ne_bot a).symm
@[simp] theorem top_ne_node (a : Fin n → Tree n) : top ≠ node a := (node_ne_top a).symm
def CovLe (t u : Tree n) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → a ≤ b
instance : LE (Tree n) := ⟨Tree.CovLe⟩
theorem le_refl (t : Tree n) : t ≤ t := by
  intro π a b ha hb
  have : a = b := Option.some.inj (ha.symm.trans hb)
  exact this.le
theorem middle_isSome {t u v : Tree n} (htu : t ≤ u) (huv : u ≤ v)
    (π : List (Fin n)) (ht : (t.fn π).isSome) (hv : (v.fn π).isSome) :
    (u.fn π).isSome := by
  induction π using List.reverseRecOn with
  | nil => exact u.root_isSome
  | append_singleton π i ih =>
    have ht' := (t.child_isSome_iff π i).mp ht
    have hv' := (v.child_isSome_iff π i).mp hv
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ih (by simp [ht']) (by simp [hv']))
    have hb' : b = Sym.f := _root_.le_antisymm (huv π b Sym.f hb hv')
      (htu π Sym.f b ht' hb)
    exact (u.child_isSome_iff π i).mpr (by simpa [hb'] using hb)
theorem le_trans {t u v : Tree n} (htu : t ≤ u) (huv : u ≤ v) : t ≤ v := by
  intro π a c ha hc
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (middle_isSome htu huv π (by simp [ha]) (by simp [hc]))
  exact _root_.le_trans (htu π a b ha hb) (huv π b c hb hc)
theorem le_antisymm {t u : Tree n} (htu : t ≤ u) (hut : u ≤ t) : t = u := by
  have labels : ∀ π a b, t.fn π = some a → u.fn π = some b → a = b := by
    intro π a b ha hb
    exact _root_.le_antisymm (htu π a b ha hb) (hut π b a hb ha)
  apply ext
  funext π
  induction π using List.reverseRecOn with
  | nil =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp t.root_isSome
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp u.root_isSome
    rw [ha, hb, labels [] a b ha hb]
  | append_singleton π i ih =>
    have hd : (t.fn (π ++ [i])).isSome ↔ (u.fn (π ++ [i])).isSome := by
      rw [child_isSome_iff, child_isSome_iff, ih]
    cases ht : t.fn (π ++ [i]) <;> cases hu : u.fn (π ++ [i])
    · rfl
    · simp [ht, hu] at hd
    · simp [ht, hu] at hd
    · exact congrArg some (labels _ _ _ ht hu)
instance : PartialOrder (Tree n) where
  le := Tree.CovLe
  le_refl := Tree.le_refl
  le_trans := fun _ _ _ => Tree.le_trans
  le_antisymm := fun _ _ => Tree.le_antisymm
end Tree
end DeciSigma1.Semantics
namespace DeciSigma1.Semantics
inductive FTree (n : ℕ) where
  | bot
  | top
  | node (children : Fin n → FTree n)
namespace FTree
variable {n : ℕ}
def toTree : FTree n → Tree n
  | bot => Tree.bot
  | top => Tree.top
  | node a => Tree.node (fun i => toTree (a i))
end FTree
end DeciSigma1.Semantics


