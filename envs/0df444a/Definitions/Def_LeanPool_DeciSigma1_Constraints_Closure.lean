-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
-- name    : LeanPool_DeciSigma1_Constraints_Closure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:18:35.299218+00:00
-- url     : https://prove2.me/theorems/feed0c43-f534-41e5-9caf-c826d83bb3e0
-- title:
--   Closure
-- statement:
--   Definitions and structural lemmas for Closure, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_cons
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_top
public import Theorems.Thm_DeciSigma1_Semantics_bot_treeLe
public import Theorems.Thm_DeciSigma1_Semantics_dual_bot
public import Theorems.Thm_DeciSigma1_Semantics_dual_fn
public import Theorems.Thm_DeciSigma1_Semantics_dual_involutive
public import Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_dual_node
public import Theorems.Thm_DeciSigma1_Semantics_dual_top
public import Theorems.Thm_DeciSigma1_Semantics_node_treeLe_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_normalize_bot
public import Theorems.Thm_DeciSigma1_Semantics_normalize_false_variance
public import Theorems.Thm_DeciSigma1_Semantics_normalize_fn
public import Theorems.Thm_DeciSigma1_Semantics_normalize_involutive
public import Theorems.Thm_DeciSigma1_Semantics_normalize_node
public import Theorems.Thm_DeciSigma1_Semantics_normalize_top
public import Theorems.Thm_DeciSigma1_Semantics_normalize_true
public import Theorems.Thm_DeciSigma1_Semantics_top_treeLe_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_top
attribute [local simp] DeciSigma1.Constraints.holdsT_map
attribute [local simp] DeciSigma1.Constraints.holds_false
attribute [local simp] DeciSigma1.Constraints.sat_false
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.descend_bot
attribute [local simp] DeciSigma1.Semantics.Tree.descend_node
attribute [local simp] DeciSigma1.Semantics.Tree.descend_top
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_bot
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_nil
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.trace_bot
attribute [local simp] DeciSigma1.Semantics.Tree.trace_cons
attribute [local simp] DeciSigma1.Semantics.Tree.trace_nil
attribute [local simp] DeciSigma1.Semantics.Tree.trace_top
attribute [local simp] DeciSigma1.Semantics.bot_treeLe
attribute [local simp] DeciSigma1.Semantics.dual_bot
attribute [local simp] DeciSigma1.Semantics.dual_fn
attribute [local simp] DeciSigma1.Semantics.dual_involutive
attribute [local simp] DeciSigma1.Semantics.dual_le_iff
attribute [local simp] DeciSigma1.Semantics.dual_node
attribute [local simp] DeciSigma1.Semantics.dual_top
attribute [local simp] DeciSigma1.Semantics.node_treeLe_node_iff
attribute [local simp] DeciSigma1.Semantics.normalize_bot
attribute [local simp] DeciSigma1.Semantics.normalize_false_variance
attribute [local simp] DeciSigma1.Semantics.normalize_fn
attribute [local simp] DeciSigma1.Semantics.normalize_involutive
attribute [local simp] DeciSigma1.Semantics.normalize_node
attribute [local simp] DeciSigma1.Semantics.normalize_top
attribute [local simp] DeciSigma1.Semantics.normalize_true
attribute [local simp] DeciSigma1.Semantics.top_treeLe_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_bot_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_false_iff_le
attribute [local simp] DeciSigma1.Semantics.treeLe_top


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
inductive Derives (Γ : List (LitT n V)) : V → V → Prop where
  | refl (x : V) : Derives Γ x x
  | lit {x y : V} : LitT.le x y ∈ Γ → Derives Γ x y
  | trans {x y z : V} : Derives Γ x y → Derives Γ y z → Derives Γ x z
  | decomp {a b : Fin n → V} {u v : V} (i : Fin n) :
      LitT.fLe a u ∈ Γ → Derives Γ u v → LitT.leF v b ∈ Γ →
      Derives Γ (a i) (b i)
def LowerF (Γ : List (LitT n V)) (x : V) : Prop :=
  ∃ a u, LitT.fLe a u ∈ Γ ∧ Derives Γ u x
def LowerTop (Γ : List (LitT n V)) (x : V) : Prop :=
  ∃ u, LitT.eqTop u ∈ Γ ∧ Derives Γ u x
def UpperF (Γ : List (LitT n V)) (x : V) : Prop :=
  ∃ v b, LitT.leF v b ∈ Γ ∧ Derives Γ x v
def UpperBot (Γ : List (LitT n V)) (x : V) : Prop :=
  ∃ v, LitT.eqBot v ∈ Γ ∧ Derives Γ x v
def LabelClash (Γ : List (LitT n V)) : Prop :=
  ∃ x, (LowerTop Γ x ∧ UpperBot Γ x) ∨
    (LowerTop Γ x ∧ UpperF Γ x) ∨ (LowerF Γ x ∧ UpperBot Γ x)
@[simp] theorem covariant_holds_map {W : Type*} (r : V → W)
    (ρ : W → Semantics.Tree n) (l : LitT n V) :
    Covariant.Holds ρ (l.map r) ↔ Covariant.Holds (ρ ∘ r) l := by cases l <;> rfl
theorem Derives.map {W : Type*} {Γ : List (LitT n V)} {ψ : List (LitT n W)} (r : V → W)
    (hr : ∀ l ∈ Γ, l.map r ∈ ψ) {a b : V} (h : Derives Γ a b) :
    Derives ψ (r a) (r b) := by
  induction h with
  | refl a => exact .refl _
  | lit hl => exact .lit (hr _ hl)
  | trans _ _ ih ih' => exact .trans ih ih'
  | @decomp a b u v i hl _ hu ih =>
    exact Derives.decomp (a := r ∘ a) (b := r ∘ b) i (hr _ hl) ih (hr _ hu)
def lowerLits (Γ : List (LitT n V)) : List ((Fin n → V) × V) :=
  Γ.filterMap fun
    | .fLe a u => some (a, u)
    | _ => none
def upperLits (Γ : List (LitT n V)) : List (V × (Fin n → V)) :=
  Γ.filterMap fun
    | .leF v b => some (v, b)
    | _ => none
def topVars (Γ : List (LitT n V)) : List (V) :=
  Γ.filterMap fun
    | .eqTop u => some u
    | _ => none
def botVars (Γ : List (LitT n V)) : List (V) :=
  Γ.filterMap fun
    | .eqBot v => some v
    | _ => none
@[simp] theorem mem_lowerLits (Γ : List (LitT n V)) (a : Fin n → V) (u : V) :
    (a, u) ∈ lowerLits Γ ↔ LitT.fLe a u ∈ Γ := by
  simp only [lowerLits, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩
@[simp] theorem mem_upperLits (Γ : List (LitT n V)) (v : V) (b : Fin n → V) :
    (v, b) ∈ upperLits Γ ↔ LitT.leF v b ∈ Γ := by
  simp only [upperLits, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩
@[simp] theorem mem_topVars (Γ : List (LitT n V)) (u : V) :
    u ∈ topVars Γ ↔ LitT.eqTop u ∈ Γ := by
  simp only [topVars, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩
@[simp] theorem mem_botVars (Γ : List (LitT n V)) (v : V) :
    v ∈ botVars Γ ↔ LitT.eqBot v ∈ Γ := by
  simp only [botVars, List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩
section Computation
variable [Fintype V] [DecidableEq V]
namespace Closure
def DecompStep (Γ : List (LitT n V)) (s : Finset (V × V)) (x y : V) : Prop :=
  ∃ l ∈ lowerLits Γ, ∃ m ∈ upperLits Γ, (l.2, m.1) ∈ s ∧ ∃ i, l.1 i = x ∧ m.2 i = y
instance (Γ : List (LitT n V)) (s : Finset (V × V)) (x y : V) :
    Decidable (DecompStep Γ s x y) := by
  unfold DecompStep
  infer_instance
def expand (Γ : List (LitT n V)) (s : Finset (V × V)) : Finset (V × V) :=
  s ∪ Finset.univ.filter (fun p =>
    p.1 = p.2 ∨ LitT.le p.1 p.2 ∈ Γ ∨
    (∃ z, (p.1, z) ∈ s ∧ (z, p.2) ∈ s) ∨
    DecompStep Γ s p.1 p.2)
def close (Γ : List (LitT n V)) (s : Finset (V × V)) : Finset (V × V) :=
  if expand Γ s ⊆ s then s else close Γ (expand Γ s)
termination_by Fintype.card V * Fintype.card V - s.card
decreasing_by
  have hs : s ⊂ expand Γ s :=
    lt_of_le_not_ge Finset.subset_union_left (by assumption)
  have hlt := Finset.card_lt_card hs
  have hle := Finset.card_le_univ (s := expand Γ s)
  simp only [Fintype.card_prod] at hle
  omega
end Closure
def derivedPairs (Γ : List (LitT n V)) : Finset (V × V) := Closure.close Γ ∅
end Computation
variable [Fintype V] [DecidableEq V]
def labelClashB (Γ : List (LitT n V)) : Bool :=
  let s := derivedPairs Γ
  let lowerF := fun x => ∃ l ∈ lowerLits Γ, (l.2, x) ∈ s
  let lowerTop := fun x => ∃ u ∈ topVars Γ, (u, x) ∈ s
  let upperF := fun x => ∃ m ∈ upperLits Γ, (x, m.1) ∈ s
  let upperBot := fun x => ∃ v ∈ botVars Γ, (x, v) ∈ s
  decide (∃ x, (lowerTop x ∧ upperBot x) ∨
    (lowerTop x ∧ upperF x) ∨ (lowerF x ∧ upperBot x))
end DeciSigma1.Constraints
namespace DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
inductive LowerAt (Γ : List (LitT n V)) : List (Fin n) → V → V → Prop where
  | nil {x y : V} : Derives Γ x y → LowerAt Γ [] x y
  | cons {a : Fin n → V} {z y x : V} {π : List (Fin n)} {i : Fin n} :
      LitT.fLe a z ∈ Γ → Derives Γ z y → LowerAt Γ π x (a i) →
      LowerAt Γ (i :: π) x y
inductive UpperAt (Γ : List (LitT n V)) : List (Fin n) → V → V → Prop where
  | nil {x y : V} : Derives Γ x y → UpperAt Γ [] x y
  | cons {x z : V} {b : Fin n → V} {y : V} {π : List (Fin n)} {i : Fin n} :
      Derives Γ x z → LitT.leF z b ∈ Γ → UpperAt Γ π (b i) y →
      UpperAt Γ (i :: π) x y
theorem LowerAt.map {W : Type*} {ψ : List (LitT n W)} (r : V → W)
    (hr : ∀ l ∈ Γ, l.map r ∈ ψ) {π : List (Fin n)} {a b : V}
    (h : LowerAt Γ π a b) : LowerAt ψ π (r a) (r b) := by
  induction h with
  | nil hd => exact .nil (hd.map r hr)
  | @cons c z y x π i hl hd _ ih =>
    exact LowerAt.cons (a := r ∘ c) (hr _ hl) (hd.map r hr) ih
namespace PathBounds
def embed (filler : Semantics.Tree n) : List (Fin n) → Semantics.Tree n → Semantics.Tree n
  | [], t => t
  | i :: π, t => Semantics.Tree.node (fun j => if j = i then embed filler π t else filler)
end PathBounds
def PathChain {α : Type*} (R : List (Fin n) → α → α → Prop)
    (π : List (Fin n)) (z x : α) : Prop :=
  ∃ w : ℕ → α, w 0 = z ∧ w π.length = x ∧
    ∀ i j, i ≤ j → j ≤ π.length → R ((π.take j).drop i) (w i) (w j)
end DeciSigma1.Constraints


