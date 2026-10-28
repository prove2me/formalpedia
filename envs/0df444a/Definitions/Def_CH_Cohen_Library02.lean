-- Prove2me | Definitions.Def_CH_Cohen_Library02
-- name    : CH_Cohen_Library02
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T01:47:16.488363+00:00
-- url     : https://prove2.me/theorems/c6707fe3-a586-4b2f-9903-e1e50422aeb7
-- title:
--   Boolean-valued set theory: Bvm
-- statement:
--   This module provides Boolean-valued set names, equality, membership, and the basic set constructors. These objects form the language and model interfaces used in the forcing and completeness arguments.
--
--   **Formalization Note** The module retains the structural normalization facts needed by these definitions and their constructor proofs. The principal forcing and model-existence assertions are separate theorem nodes.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Bvm.lean

import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Card
import Mathlib.Topology.Clopen
import Mathlib.Topology.Constructions
import Mathlib.Data.PFun
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_CH_Cohen_Library01
/-
Physical source: Flypitch, Jesse Han and Floris van Doorn (Apache-2.0).
Lean 4 port: Ian Klatzco, with Claude.
Upstream commit ad649f89e9f3107b7e2ea97a58b2eafdfc80b815.
Original notices and source statements are retained.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/- Source module: Definitions.Flypitch4.Bvm -/
section CohenSource_Bvm
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bvm.lean lines 1-700 — Task 10a -/






set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch

/-! ## Namespace Lattice — natural deduction lemmas in BA -/

namespace Lattice

section natded
variable {𝔹 : Type*} [CompleteBooleanAlgebra 𝔹]

-- src/bvm.lean:21
lemma supr_imp_eq {ι : Type*} {s : ι → 𝔹} {b : 𝔹} :
    (⨆ (i : ι), s i) ⟹ b = ⨅ (i : ι), s i ⟹ b := by
  unfold imp; rw [compl_iSup, iInf_sup_eq']

-- src/bvm.lean:25


-- src/bvm.lean:29
lemma bv_Or_elim {ι : Type*} {s : ι → 𝔹} {c : 𝔹}
    (H : ∀ i : ι, s i ≤ c) : (⨆ (i : ι), s i) ≤ c :=
  iSup_le H

-- src/bvm.lean:33


-- src/bvm.lean:37


-- src/bvm.lean:40
lemma bv_or_elim_left {b₁ b₂ c d : 𝔹} (h₁ : b₁ ⊓ d ≤ c) (h₂ : b₂ ⊓ d ≤ c) :
    (b₁ ⊔ b₂) ⊓ d ≤ c := by
  rw [deduction]; apply sup_le <;> rw [← deduction] <;> assumption

-- src/bvm.lean:43
lemma bv_or_elim_right {b₁ b₂ c d : 𝔹} (h₁ : d ⊓ b₁ ≤ c) (h₂ : d ⊓ b₂ ≤ c) :
    d ⊓ (b₁ ⊔ b₂) ≤ c := by
  rw [inf_comm]; rw [inf_comm] at h₁ h₂; exact bv_or_elim_left h₁ h₂

-- src/bvm.lean:46


-- src/bvm.lean:49
lemma bv_cases_left {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (h : ∀ i : ι, s i ⊓ c ≤ b) :
    ((⨆ (i : ι), s i) ⊓ c) ≤ b := by
  rw [deduction]; apply iSup_le; intro i; rw [← deduction]; exact h i

-- src/bvm.lean:53
lemma bv_cases_right {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (h : ∀ i : ι, c ⊓ s i ≤ b) :
    (c ⊓ (⨆ (i : ι), s i)) ≤ b := by
  rw [inf_comm]; exact bv_cases_left (fun i => by rw [inf_comm]; exact h i)

-- src/bvm.lean:57
lemma bv_specialize {ι : Type*} {s : ι → 𝔹} (i : ι) {b : 𝔹} (h : s i ≤ b) :
    (⨅ (i : ι), s i) ≤ b :=
  iInf_le_of_le i h

-- src/bvm.lean:61


-- src/bvm.lean:68
lemma bv_specialize_left {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i : ι)
    (h : s i ⊓ c ≤ b) : (⨅ (i : ι), s i) ⊓ c ≤ b := by
  rw [deduction]; exact bv_specialize i (by rwa [← deduction])

-- src/bvm.lean:72


-- src/bvm.lean:78
lemma bv_specialize_right {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i : ι)
    (h : c ⊓ s i ≤ b) : c ⊓ (⨅ (i : ι), s i) ≤ b := by
  rw [inf_comm]; exact bv_specialize_left i (by rwa [inf_comm])

-- src/bvm.lean:82


-- src/bvm.lean:88
lemma bv_imp_elim {a b : 𝔹} : (a ⟹ b) ⊓ a ≤ b := imp_inf_le a b

-- src/bvm.lean:91


-- src/bvm.lean:94


-- src/bvm.lean:97


-- src/bvm.lean:107


-- src/bvm.lean:122


-- src/bvm.lean:124


-- src/bvm.lean:126


-- src/bvm.lean:128 (bv_and.left → bv_and_left)


-- src/bvm.lean:131 (bv_and.right → bv_and_right)


-- src/bvm.lean:134


-- src/bvm.lean:137


-- src/bvm.lean:140


-- src/bvm.lean:143


-- src/bvm.lean:146
lemma bv_use {ι} (i : ι) {s : ι → 𝔹} {b : 𝔹} (h : b ≤ s i) : b ≤ ⨆ (j : ι), s j :=
  le_trans h (le_iSup _ i)

-- src/bvm.lean:149


-- src/bvm.lean:152


-- src/bvm.lean:155


end natded
end Lattice

open Lattice

universe u

/-! ## pSet namespace — small additions -/

namespace PSet

-- src/bvm.lean:173-184
/-- If two pre-sets `x` and `y` are not equivalent, then either there exists a member of x
which is not equivalent to any member of y, or there exists a member of y which is not
equivalent to any member of x -/
lemma not_equiv {x y : PSet} (h_neq : ¬ PSet.Equiv x y) :
    (∃ a : x.Type, ∀ a' : y.Type, ¬ PSet.Equiv (x.Func a) (y.Func a')) ∨
    (∃ a' : y.Type, ∀ a : x.Type, ¬ PSet.Equiv (x.Func a) (y.Func a')) := by
  rw [PSet.equiv_iff] at h_neq
  by_cases hleft : ∀ i : x.Type, ∃ j : y.Type, PSet.Equiv (x.Func i) (y.Func j)
  · right
    have hright : ¬ ∀ j : y.Type, ∃ i : x.Type, PSet.Equiv (x.Func i) (y.Func j) := by
      intro hright; exact h_neq ⟨hleft, hright⟩
    simp only [not_forall, not_exists] at hright
    obtain ⟨a', ha'⟩ := hright
    exact ⟨a', ha'⟩
  · left
    simp only [not_forall, not_exists] at hleft
    obtain ⟨a, ha⟩ := hleft
    exact ⟨a, ha⟩

end PSet

/-! ## bSet — boolean-valued model of ZFC -/

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.
inductive bSet (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹] : Type (u + 1)
  | mk (α : Type u) (A : α → bSet 𝔹) (B : α → 𝔹) : bSet 𝔹

namespace bSet

open scoped Flypitch

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

noncomputable instance decidable_eq_𝔹 : DecidableEq 𝔹 :=
  fun _ _ => Classical.propDecidable _

-- src/bvm.lean:203
/-- The underlying type of a bSet -/
@[simp] def type : bSet 𝔹 → Type u
  | ⟨α, _, _⟩ => α

-- src/bvm.lean:206
@[simp] lemma type_iInf {α : Type u} {A : α → bSet 𝔹} {B : α → 𝔹} {C : α → 𝔹} :
    (⨅ (a : (mk α A B).type), C a) = ⨅ (a : α), C a := rfl

-- src/bvm.lean:208
@[simp] lemma type_iSup {α : Type u} {A : α → bSet 𝔹} {B : α → 𝔹} {C : α → 𝔹} :
    (⨆ (a : (mk α A B).type), C a) = ⨆ (a : α), C a := rfl

-- src/bvm.lean:211
/-- The indexing function of a bSet -/
@[simp] def func : ∀ x : bSet 𝔹, x.type → bSet 𝔹
  | ⟨_, A, _⟩ => A

-- src/bvm.lean:215
/-- The boolean truth-value function of a bSet -/
@[simp] def bval : ∀ x : bSet 𝔹, x.type → 𝔹
  | ⟨_, _, B⟩ => B

-- src/bvm.lean:218
@[simp] def mk_type_func_bval : ∀ x : bSet 𝔹, mk x.type x.func x.bval = x :=
  fun x => by cases x; rfl

-- src/bvm.lean:221
def empty : bSet 𝔹 :=
  ⟨PEmpty, PEmpty.elim, PEmpty.elim⟩

instance nonempty_bSet : Nonempty (@bSet 𝔹 _) := ⟨empty⟩

instance has_empty_bSet : EmptyCollection (bSet 𝔹) := ⟨empty⟩

-- src/bvm.lean:229
@[simp] lemma forall_over_empty (ϕ : (empty : bSet 𝔹).type → 𝔹) : (⨅ a, ϕ a) = ⊤ := by
  apply top_unique; apply le_iInf; intro a; exact a.elim

-- src/bvm.lean:232
@[simp] lemma exists_over_empty (ϕ : (empty : bSet 𝔹).type → 𝔹) : (⨆ a, ϕ a) = ⊥ := by
  apply bot_unique; apply iSup_le; intro i; exact i.elim

-- src/bvm.lean:238
/-- Two Boolean-valued pre-sets are extensionally equivalent if every
element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
def bv_eq : ∀ (x y : bSet 𝔹), 𝔹
  | ⟨α, A, B⟩, ⟨α', A', B'⟩ =>
    (⨅ a : α, B a ⟹ ⨆ a', B' a' ⊓ bv_eq (A a) (A' a')) ⊓
    (⨅ a' : α', B' a' ⟹ ⨆ a, B a ⊓ bv_eq (A a) (A' a'))

scoped infixl:79 " =ᴮ " => bv_eq



-- src/bvm.lean:255
@[simp] theorem bv_eq_refl : ∀ x : bSet 𝔹, x =ᴮ x = ⊤ := by
  intro x
  induction x with
  | mk α A B ih =>
    simp only [bv_eq, inf_eq_top_iff, iInf_eq_top]
    constructor
    all_goals intro i
    all_goals rw [imp_top_iff_le]
    all_goals exact le_iSup_of_le i (le_inf le_rfl (ih i ▸ le_top))

@[simp] lemma bv_refl {Γ : 𝔹} {x : bSet 𝔹} : Γ ≤ x =ᴮ x :=
  le_trans le_top (by simp)

@[simp] lemma bv_eq_top_of_eq {x y : bSet 𝔹} (h_eq : x = y) : x =ᴮ y = ⊤ := by
  subst h_eq; simp

-- src/bvm.lean:269


-- src/bvm.lean:278
/-- `x ∈ y` as Boolean-valued pre-sets if `x` is extensionally equivalent to a member
  of the family `y`. -/
def mem : bSet 𝔹 → bSet 𝔹 → 𝔹
  | a, ⟨α', A', B'⟩ => ⨆ a', B' a' ⊓ a =ᴮ A' a'

-- src/bvm.lean:281


scoped infixl:80 " ∈ᴮ " => mem

-- src/bvm.lean:286
lemma mem_unfold {u v : bSet 𝔹} : u ∈ᴮ v = ⨆ (i : v.type), v.bval i ⊓ u =ᴮ v.func i := by
  cases v; simp [mem, bv_eq]

-- src/bvm.lean:295
theorem mem_mk {α : Type u} (A : α → bSet 𝔹) (B : α → 𝔹) (a : α) :
    B a ≤ A a ∈ᴮ mk α A B :=
  le_iSup_of_le a (by simp)

-- src/bvm.lean:298
theorem mem_mk' (x : bSet 𝔹) (a : x.type) : x.bval a ≤ x.func a ∈ᴮ x := by
  cases x; exact mem_mk _ _ _

-- src/bvm.lean:302
@[simp] theorem mem_mk'' {x : bSet 𝔹} {a : x.type} {Γ : 𝔹} :
    Γ ≤ x.bval a → Γ ≤ x.func a ∈ᴮ x :=
  poset_yoneda_inv Γ (mem_mk' x a)

-- src/bvm.lean:305
@[reducible] protected def subset : bSet 𝔹 → bSet 𝔹 → 𝔹
  | ⟨α, A, B⟩, b => ⨅ a : α, B a ⟹ (A a ∈ᴮ b)

scoped infixl:80 " ⊆ᴮ " => bSet.subset

-- src/bvm.lean:310
lemma subset_unfold {x u : bSet 𝔹} :
    x ⊆ᴮ u = (⨅ (j : x.type), x.bval j ⟹ x.func j ∈ᴮ u) := by
  cases x; simp [bSet.subset]

-- src/bvm.lean:313
@[simp] protected def insert : bSet 𝔹 → 𝔹 → bSet 𝔹 → bSet 𝔹
  | u, b, ⟨α, A, B⟩ => ⟨Option α, fun o => Option.rec u A o, fun o => Option.rec b B o⟩

-- src/bvm.lean:316


-- src/bvm.lean:319
@[reducible] protected def insert1 : bSet 𝔹 → bSet 𝔹 → bSet 𝔹
  | u, v => bSet.insert u ⊤ v

-- src/bvm.lean:322


-- src/bvm.lean:328
instance insert_bSet : Insert (bSet 𝔹) (bSet 𝔹) :=
  ⟨fun u v => bSet.insert1 u v⟩

-- src/bvm.lean:331
@[simp] lemma insert_unfold {y z : bSet 𝔹} : insert y z = bSet.insert y ⊤ z := rfl

-- src/bvm.lean:334
@[simp] theorem mem_insert {x y z : bSet 𝔹} {b : 𝔹} :
    x ∈ᴮ bSet.insert y b z = (b ⊓ x =ᴮ y) ⊔ x ∈ᴮ z := by
  cases y; cases z
  simp only [bSet.insert, mem]
  rw [iSup_option]

-- src/bvm.lean:338
@[simp] theorem mem_insert1 {x y z : bSet 𝔹} : x ∈ᴮ insert y z = x =ᴮ y ⊔ x ∈ᴮ z := by
  rw [insert_unfold, mem_insert, top_inf_eq]

-- src/bvm.lean:341
@[simp] theorem mem_insert1' {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ insert y z ↔ Γ ≤ x =ᴮ y ⊔ x ∈ᴮ z := by
  rw [mem_insert1]

-- src/bvm.lean:354
 def bv_eq_symm_aux : ∀ (x y : bSet 𝔹), x =ᴮ y = y =ᴮ x
  | ⟨α, A, B⟩, ⟨α', A', B'⟩ => by
    have : ∀ a a', A' a' =ᴮ A a = A a =ᴮ A' a' := fun a a' => (bv_eq_symm_aux (A a) (A' a')).symm
    simp only [bv_eq, this, inf_comm]

theorem bv_eq_symm {x y : bSet 𝔹} : x =ᴮ y = y =ᴮ x := bv_eq_symm_aux x y

-- src/bvm.lean:361
theorem bv_eq_unfold (x y : bSet 𝔹) :
    x =ᴮ y = (⨅ (a : x.type), x.bval a ⟹ (x.func a ∈ᴮ y))
            ⊓ (⨅ (a' : y.type), (y.bval a' ⟹ (y.func a' ∈ᴮ x))) := by
  cases x; cases y; simp [mem, bv_eq, bv_eq_symm]

-- src/bvm.lean:366


-- src/bvm.lean:381
lemma eq_of_subset_subset (x y : bSet 𝔹) : x ⊆ᴮ y ⊓ y ⊆ᴮ x ≤ x =ᴮ y := by
  rw [bv_eq_unfold, subset_unfold, subset_unfold]

-- src/bvm.lean:387
lemma subset_subset_of_eq (x y : bSet 𝔹) : x =ᴮ y ≤ x ⊆ᴮ y ⊓ y ⊆ᴮ x := by
  rw [bv_eq_unfold, subset_unfold, subset_unfold]

-- src/bvm.lean:393
theorem eq_iff_subset_subset {x y : bSet 𝔹} : x =ᴮ y = x ⊆ᴮ y ⊓ y ⊆ᴮ x :=
  le_antisymm (subset_subset_of_eq x y) (eq_of_subset_subset x y)

-- src/bvm.lean:396


-- src/bvm.lean:399


-- src/bvm.lean:402
@[simp] lemma subset_self {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ x :=
  le_trans le_top (by rw [show ⊤ = x =ᴮ x by simp, eq_iff_subset_subset]; exact inf_le_left)

-- src/bvm.lean:406
theorem subset_ext {x y : bSet 𝔹} {Γ : 𝔹} (h₁ : Γ ≤ x ⊆ᴮ y) (h₂ : Γ ≤ y ⊆ᴮ x) :
    Γ ≤ x =ᴮ y := by
  rw [eq_iff_subset_subset]; exact le_inf h₁ h₂

-- src/bvm.lean:413
theorem bv_eq_trans {x y z : bSet 𝔹} : (x =ᴮ y ⊓ y =ᴮ z) ≤ x =ᴮ z := by
  induction x generalizing y z with
  | mk α A B ih =>
  induction y with
  | mk α' A' B' =>
  induction z with
  | mk α'' A'' B'' =>
  -- IH: for each a : α, the prop bv_eq_trans holds for A a as the "x"
  -- Core transitivity for elements: A a ≈ A' a' ≈ A'' a'' → A a ≈ A'' a''
  have trans_fwd : ∀ (a : α) (a' : α') (a'' : α''),
      A a =ᴮ A' a' ⊓ A' a' =ᴮ A'' a'' ≤ A a =ᴮ A'' a'' := by
    intro a a' a''
    exact @ih a (A' a') (A'' a'')
  -- Core transitivity for elements backwards: A'' ≈ A' ≈ A → A'' ≈ A
  have trans_bwd : ∀ (a'' : α'') (a' : α') (a : α),
      A'' a'' =ᴮ A' a' ⊓ A' a' =ᴮ A a ≤ A'' a'' =ᴮ A a := by
    intro a'' a' a
    have h := trans_fwd a a' a''
    -- h : A a =ᴮ A' a' ⊓ A' a' =ᴮ A'' a'' ≤ A a =ᴮ A'' a''
    have eq1 : A'' a'' =ᴮ A' a' = A' a' =ᴮ A'' a'' := bv_eq_symm
    have eq2 : A' a' =ᴮ A a = A a =ᴮ A' a' := bv_eq_symm
    have eq3 : A a =ᴮ A'' a'' = A'' a'' =ᴮ A a := bv_eq_symm
    calc A'' a'' =ᴮ A' a' ⊓ A' a' =ᴮ A a
        = A' a' =ᴮ A'' a'' ⊓ A a =ᴮ A' a' := by rw [eq1, eq2]
      _ = A a =ᴮ A' a' ⊓ A' a' =ᴮ A'' a'' := by rw [inf_comm]
      _ ≤ A a =ᴮ A'' a'' := h
      _ = A'' a'' =ᴮ A a := eq3
  simp only [bv_eq]
  apply le_inf
  · -- Forward direction: ⨅ a, B a ⟹ ⨆ a'', B'' a'' ⊓ A a =ᴮ A'' a''
    apply le_iInf; intro i
    rw [← deduction]
    -- Need: (xy_eq ⊓ yz_eq) ⊓ B i ≤ A i ∈ᴮ mk α'' A'' B''
    -- Step 1: xy_eq ⊓ B i ≤ A i ∈ᴮ mk α' A' B' (from left component of bv_eq)
    have mem_y : (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B i
        ≤ A i ∈ᴮ mk α' A' B' := by
      calc (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B i
          ≤ mk α A B =ᴮ mk α' A' B' ⊓ B i :=
            le_inf (inf_le_left.trans inf_le_left) inf_le_right
        _ ≤ A i ∈ᴮ mk α' A' B' := by
            rw [deduction]; exact inf_le_left.trans (iInf_le _ i)
    -- Step 2: yz_eq is also available
    have yz_eq_avail : (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B i
        ≤ mk α' A' B' =ᴮ mk α'' A'' B'' :=
      inf_le_left.trans inf_le_right
    -- Chain them: A i ∈ mk α' A' B' and yz_eq, then use each element of the sup
    -- A i ∈ mk α' A' B' = ⨆ a', B' a' ⊓ A i =ᴮ A' a'
    -- For each a', use B' a' ⟹ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'' (from yz_eq)
    -- Then for each a'', use trans_fwd i a' a'' to get A i =ᴮ A'' a''
    suffices h : A i ∈ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'' ≤ A i ∈ᴮ mk α'' A'' B'' by
      exact le_trans (le_inf mem_y yz_eq_avail) h
    simp only [mem, bv_eq, func]
    rw [iSup_inf_eq]
    apply iSup_le; intro a'
    -- Goal: B' a' ⊓ A i =ᴮ A' a' ⊓ ((⨅ ⟹ ⨆) ⊓ (⨅ ⟹ ⨆)) ≤ ⨆ a'', B'' a'' ⊓ A i =ᴮ A'' a''
    -- Use left ⨅ component to get B' a' ⟹ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a''
    have elim_a' : B' a' ⊓ A i =ᴮ A' a' ⊓
        ((⨅ a_1, B' a_1 ⟹ ⨆ a'', B'' a'' ⊓ A' a_1 =ᴮ A'' a'') ⊓
         (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''))
        ≤ A i =ᴮ A' a' ⊓ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'' := by
      apply le_inf (inf_le_left.trans inf_le_right)
      have h_imp : B' a' ⊓ A i =ᴮ A' a' ⊓
          ((⨅ a_1, B' a_1 ⟹ ⨆ a'', B'' a'' ⊓ A' a_1 =ᴮ A'' a'') ⊓
           (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''))
          ≤ (B' a' ⟹ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'') ⊓ B' a' :=
        le_inf (inf_le_right.trans inf_le_left |>.trans (iInf_le _ a'))
               (inf_le_left.trans inf_le_left)
      exact le_trans h_imp bv_imp_elim
    calc B' a' ⊓ A i =ᴮ A' a' ⊓
        ((⨅ a_1, B' a_1 ⟹ ⨆ a'', B'' a'' ⊓ A' a_1 =ᴮ A'' a'') ⊓
         (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''))
        ≤ A i =ᴮ A' a' ⊓ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'' := elim_a'
      _ ≤ ⨆ a'', B'' a'' ⊓ A i =ᴮ A'' a'' := by
          rw [inf_iSup_eq]
          apply iSup_le; intro a''
          apply le_iSup_of_le a''
          -- Goal: A i =ᴮ A' a' ⊓ (B'' a'' ⊓ A' a' =ᴮ A'' a'') ≤ B'' a'' ⊓ A i =ᴮ A'' a''
          apply le_inf (inf_le_right.trans inf_le_left)
          calc A i =ᴮ A' a' ⊓ (B'' a'' ⊓ A' a' =ᴮ A'' a'')
              ≤ A i =ᴮ A' a' ⊓ A' a' =ᴮ A'' a'' :=
                le_inf inf_le_left (inf_le_right.trans inf_le_right)
            _ ≤ A i =ᴮ A'' a'' := trans_fwd i a' a''
  · -- Backward direction: ⨅ a'', B'' a'' ⟹ ⨆ a, B a ⊓ A a =ᴮ A'' a''
    -- Goal (after simp [bv_eq]): (x=y ⊓ y=z) ≤ ⨅ a'', B'' a'' ⟹ ⨆ a, B a ⊓ A a =ᴮ A'' a''
    apply le_iInf; intro i''
    rw [← deduction]
    -- Goal: (x=y ⊓ y=z) ⊓ B'' i'' ≤ ⨆ a, B a ⊓ A a =ᴮ A'' i''
    -- Step 1: extract yz_eq ⊓ B'' i'' to get A'' i'' ∈ mk α' A' B' (= ⨆ a', B' a' ⊓ A'' i'' =ᴮ A' a')
    -- The second component of y=z: ⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''
    -- So B'' i'' ⊓ yz_eq ≤ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' i''
    -- Step 2: for each a', use xy_eq to chain A'' i'' ≈ A' a' ≈ A a to get A'' i'' ≈ A a
    -- and B' a' ⟹ ⨆ a, B a ⊓ A a =ᴮ A' a' to get B a
    -- Let's directly unfold and work with the raw forms
    -- The second component of yz_eq gives: B'' i'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' i''
    -- (by taking the second component and specializing at i'')
    have yz_step : (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B'' i''
        ≤ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' i'' := by
      -- From second component of y=z: ⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''
      -- specialized at i'', plus B'' i''
      simp only [bv_eq, func]
      calc (((⨅ a, B a ⟹ ⨆ a', B' a' ⊓ A a =ᴮ A' a') ⊓
             (⨅ a', B' a' ⟹ ⨆ a, B a ⊓ A a =ᴮ A' a')) ⊓
            ((⨅ a', B' a' ⟹ ⨆ a'', B'' a'' ⊓ A' a' =ᴮ A'' a'') ⊓
             (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a''))) ⊓ B'' i''
          ≤ (⨅ a'', B'' a'' ⟹ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' a'') ⊓ B'' i'' := by
            apply le_inf
            · exact inf_le_left.trans (inf_le_right.trans inf_le_right)
            · exact inf_le_right
        _ ≤ ⨆ a', B' a' ⊓ A' a' =ᴮ A'' i'' :=
            le_trans (inf_le_inf_right _ (iInf_le _ i'')) bv_imp_elim
    -- Now: ⨆ a', B' a' ⊓ A' a' =ᴮ A'' i'' ⊓ xy_eq ≤ ⨆ a, B a ⊓ A a =ᴮ A'' i''
    have xy_eq_avail : (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B'' i''
        ≤ mk α A B =ᴮ mk α' A' B' :=
      inf_le_left.trans inf_le_left
    -- Chain: yz_step ⊓ xy_eq_avail → for each a', use xy_eq to chain
    calc (mk α A B =ᴮ mk α' A' B' ⊓ mk α' A' B' =ᴮ mk α'' A'' B'') ⊓ B'' i''
        ≤ (⨆ a', B' a' ⊓ A' a' =ᴮ A'' i'') ⊓ mk α A B =ᴮ mk α' A' B' :=
          le_inf yz_step xy_eq_avail
      _ ≤ ⨆ a, B a ⊓ A a =ᴮ A'' i'' := by
          rw [iSup_inf_eq]
          apply iSup_le; intro a'
          -- Goal: B' a' ⊓ A' a' =ᴮ A'' i'' ⊓ xy_eq ≤ ⨆ a, B a ⊓ A a =ᴮ A'' i''
          -- From xy_eq, second component: B' a' ⟹ ⨆ a, B a ⊓ A a =ᴮ A' a'
          simp only [bv_eq, func]
          -- Extract ⨆ a, B a ⊓ A a =ᴮ A' a' using B' a' and xy_eq's second component
          have xy_step2 : B' a' ⊓ A' a' =ᴮ A'' i'' ⊓
              ((⨅ a, B a ⟹ ⨆ a', B' a' ⊓ A a =ᴮ A' a') ⊓
               (⨅ a', B' a' ⟹ ⨆ a, B a ⊓ A a =ᴮ A' a'))
              ≤ A' a' =ᴮ A'' i'' ⊓ ⨆ a, B a ⊓ A a =ᴮ A' a' := by
            refine le_inf (inf_le_left.trans inf_le_right) ?_
            exact le_trans
              (le_inf (inf_le_right.trans inf_le_right |>.trans (iInf_le _ a'))
                      (inf_le_left.trans inf_le_left))
              bv_imp_elim
          calc B' a' ⊓ A' a' =ᴮ A'' i'' ⊓
              ((⨅ a, B a ⟹ ⨆ a', B' a' ⊓ A a =ᴮ A' a') ⊓
               (⨅ a', B' a' ⟹ ⨆ a, B a ⊓ A a =ᴮ A' a'))
              ≤ A' a' =ᴮ A'' i'' ⊓ ⨆ a, B a ⊓ A a =ᴮ A' a' := xy_step2
            _ ≤ ⨆ a, B a ⊓ A a =ᴮ A'' i'' := by
                rw [inf_iSup_eq]
                apply iSup_le; intro a
                apply le_iSup_of_le a
                -- Goal: A' a' =ᴮ A'' i'' ⊓ (B a ⊓ A a =ᴮ A' a') ≤ B a ⊓ A a =ᴮ A'' i''
                apply le_inf (inf_le_right.trans inf_le_left)
                -- Need: A' a' =ᴮ A'' i'' ⊓ (B a ⊓ A a =ᴮ A' a') ≤ A a =ᴮ A'' i''
                -- A a =ᴮ A' a' ⊓ A' a' =ᴮ A'' i'' ≤ A a =ᴮ A'' i'' (trans_fwd a a' i'')
                calc A' a' =ᴮ A'' i'' ⊓ (B a ⊓ A a =ᴮ A' a')
                    ≤ A a =ᴮ A' a' ⊓ A' a' =ᴮ A'' i'' := by
                      apply le_inf
                      · exact (inf_le_right.trans inf_le_right)
                      · exact inf_le_left
                  _ ≤ A a =ᴮ A'' i'' := trans_fwd a a' i''

-- src/bvm.lean:472
lemma bv_trans {Γ : 𝔹} {a₁ a₂ a₃ : bSet 𝔹} (H₁ : Γ ≤ a₁ =ᴮ a₂) (H₂ : Γ ≤ a₂ =ᴮ a₃) :
    Γ ≤ a₁ =ᴮ a₃ :=
  le_trans (le_inf H₁ H₂) bv_eq_trans

-- src/bvm.lean:476
@[symm] lemma bv_symm {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) : Γ ≤ y =ᴮ x := by
  rwa [bv_eq_symm]

-- src/bvm.lean:478


-- src/bvm.lean:485
/-- If u = v and u ∈ w, then this implies that v ∈ w -/
lemma subst_congr_mem_left {u v w : bSet 𝔹} : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w := by
  simp only [mem_unfold]
  rw [inf_iSup_eq]
  apply iSup_le; intro i
  apply le_iSup_of_le i
  -- Goal: u =ᴮ v ⊓ (w.bval i ⊓ u =ᴮ w.func i) ≤ w.bval i ⊓ v =ᴮ w.func i
  apply le_inf (inf_le_right.trans inf_le_left)
  -- Need: u =ᴮ v ⊓ (w.bval i ⊓ u =ᴮ w.func i) ≤ v =ᴮ w.func i
  -- Use bv_eq_trans with v =ᴮ u ⊓ u =ᴮ w.func i ≤ v =ᴮ w.func i
  calc u =ᴮ v ⊓ (w.bval i ⊓ u =ᴮ w.func i)
      ≤ u =ᴮ v ⊓ u =ᴮ w.func i := le_inf inf_le_left (inf_le_right.trans inf_le_right)
    _ = v =ᴮ u ⊓ u =ᴮ w.func i := by rw [bv_eq_symm]
    _ ≤ v =ᴮ w.func i := bv_eq_trans

-- src/bvm.lean:493
@[simp] lemma subst_congr_mem_left' {Γ : 𝔹} {u v w : bSet 𝔹} :
    Γ ≤ u =ᴮ v → Γ ≤ u ∈ᴮ w → Γ ≤ v ∈ᴮ w :=
  fun h₁ h₂ => poset_yoneda_inv Γ subst_congr_mem_left (le_inf h₁ h₂)

-- src/bvm.lean:504
/-- If v = w and u ∈ v, then this implies that u ∈ w -/
lemma subst_congr_mem_right {u v w : bSet 𝔹} : (v =ᴮ w ⊓ u ∈ᴮ v) ≤ u ∈ᴮ w := by
  cases v with | mk vα vA vB =>
  rw [mem_unfold (v := mk vα vA vB)]
  rw [inf_iSup_eq]
  apply iSup_le; intro i
  -- Goal: mk vα vA vB =ᴮ w ⊓ (vB i ⊓ u =ᴮ vA i) ≤ u ∈ᴮ w
  -- Step 1: vA i ∈ᴮ w using v =ᴮ w ⊓ vB i
  have mem_w : mk vα vA vB =ᴮ w ⊓ vB i ≤ vA i ∈ᴮ w := by
    rw [deduction]
    -- Goal: mk vα vA vB =ᴮ w ≤ vB i ⟹ vA i ∈ᴮ w
    calc mk vα vA vB =ᴮ w
        ≤ ⨅ j, vB j ⟹ vA j ∈ᴮ w := by rw [bv_eq_unfold]; exact inf_le_left
      _ ≤ vB i ⟹ vA i ∈ᴮ w := iInf_le _ i
  -- Step 2: vA i =ᴮ u ⊓ vA i ∈ᴮ w ≤ u ∈ᴮ w (by subst_congr_mem_left)
  -- chain: mk vα vA vB =ᴮ w ⊓ (vB i ⊓ u =ᴮ vA i) ≤ vA i ∈ᴮ w ⊓ u =ᴮ vA i ≤ u ∈ᴮ w
  have step1 : mk vα vA vB =ᴮ w ⊓ (vB i ⊓ u =ᴮ vA i) ≤ vA i ∈ᴮ w ⊓ u =ᴮ vA i :=
    le_inf (le_trans (le_inf inf_le_left (inf_le_right.trans inf_le_left)) mem_w)
           (inf_le_right.trans inf_le_right)
  have step2 : vA i ∈ᴮ w ⊓ u =ᴮ vA i ≤ u ∈ᴮ w := by
    -- Use subst_congr_mem_left: vA i =ᴮ u ⊓ vA i ∈ᴮ w ≤ u ∈ᴮ w
    have h : vA i =ᴮ u ⊓ vA i ∈ᴮ w ≤ u ∈ᴮ w := subst_congr_mem_left
    have heq : vA i ∈ᴮ w ⊓ u =ᴮ vA i = vA i =ᴮ u ⊓ vA i ∈ᴮ w := by
      rw [inf_comm (a := vA i ∈ᴮ w)]
      congr 1
      exact bv_eq_symm
    rw [heq]; exact h
  exact le_trans step1 step2

-- src/bvm.lean:514
@[simp] lemma subst_congr_mem_right' {Γ : 𝔹} {u v w : bSet 𝔹} :
    Γ ≤ w =ᴮ v → Γ ≤ u ∈ᴮ w → Γ ≤ u ∈ᴮ v :=
  fun h₁ h₂ => poset_yoneda_inv Γ subst_congr_mem_right (le_inf h₁ h₂)

-- src/bvm.lean:518
lemma bounded_forall {v : bSet 𝔹} {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
    (⨅ (i_x : v.type), (v.bval i_x ⟹ ϕ (v.func i_x))) =
    (⨅ (x : bSet 𝔹), x ∈ᴮ v ⟹ ϕ x) := by
  apply le_antisymm
  · apply le_iInf; intro x
    cases v with | mk vα vA vB =>
    simp only [bval, func, mem]
    rw [supr_imp_eq]
    apply le_iInf; intro i_y
    apply iInf_le_of_le i_y
    rw [← deduction, ← inf_assoc]
    apply le_trans
    · exact inf_le_inf bv_imp_elim le_rfl
    rw [inf_comm, bv_eq_symm]
    exact h_congr _ _
  · apply le_iInf; intro i_x'
    apply iInf_le_of_le (func v i_x')
    apply imp_le_of_left_le
    cases v with | mk vα vA vB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i_x' (le_inf le_rfl (by simp))

-- src/bvm.lean:531
lemma bounded_exists {v : bSet 𝔹} {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
    (⨆ (i_x : v.type), (v.bval i_x ⊓ ϕ (v.func i_x))) =
    (⨆ (x : bSet 𝔹), x ∈ᴮ v ⊓ ϕ x) := by
  apply le_antisymm
  · apply iSup_le; intro i_x
    apply le_iSup_of_le (v.func i_x)
    exact le_inf (inf_le_left.trans (mem_mk' v i_x)) inf_le_right
  · apply iSup_le; intro x
    rw [mem_unfold]
    apply bv_cases_left (h := fun i_x => ?_)
    -- goal: v.bval i_x ⊓ x =ᴮ v.func i_x ⊓ ϕ x ≤ ⨆ i, v.bval i ⊓ ϕ (v.func i)
    apply le_iSup_of_le i_x
    -- goal: v.bval i_x ⊓ x =ᴮ v.func i_x ⊓ ϕ x ≤ v.bval i_x ⊓ ϕ (v.func i_x)
    apply le_inf
    · exact inf_le_left.trans inf_le_left
    · -- (v.bval i_x ⊓ x =ᴮ v.func i_x) ⊓ ϕ x ≤ ϕ (v.func i_x)
      -- via (x =ᴮ v.func i_x) ⊓ ϕ x ≤ ϕ (v.func i_x) = h_congr x (v.func i_x)
      have : (v.bval i_x ⊓ x =ᴮ v.func i_x) ⊓ ϕ x ≤ x =ᴮ v.func i_x ⊓ ϕ x :=
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
      exact le_trans this (h_congr x (v.func i_x))

-- src/bvm.lean:544


-- src/bvm.lean:549
lemma subset_unfold' {x u : bSet 𝔹} : x ⊆ᴮ u = ⨅ (w : bSet 𝔹), w ∈ᴮ x ⟹ w ∈ᴮ u := by
  simp only [subset_unfold]
  rw [bounded_forall (h_congr := fun a b => subst_congr_mem_left)]

-- src/bvm.lean:555
lemma bv_eq_unfold' {x y : bSet 𝔹} :
    x =ᴮ y = (⨅ z, z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (⨅ z, z ∈ᴮ y ⟹ z ∈ᴮ x) := by
  rw [eq_iff_subset_subset, subset_unfold', subset_unfold']

-- src/bvm.lean:560
theorem mem_ext {x y : bSet 𝔹} {Γ : 𝔹}
    (h₁ : Γ ≤ ⨅ z, z ∈ᴮ x ⟹ z ∈ᴮ y)
    (h₂ : Γ ≤ ⨅ z, z ∈ᴮ y ⟹ z ∈ᴮ x) : Γ ≤ x =ᴮ y := by
  rw [bv_eq_unfold']; exact le_inf h₁ h₂

-- src/bvm.lean:563
@[simp] lemma subset_self_eq_top {x : bSet 𝔹} : x ⊆ᴮ x = ⊤ :=
  top_unique subset_self

-- src/bvm.lean:566
lemma subset_trans {x y z : bSet 𝔹} : x ⊆ᴮ y ⊓ y ⊆ᴮ z ≤ x ⊆ᴮ z := by
  simp only [subset_unfold']
  apply le_iInf; intro w
  rw [← deduction]
  -- Goal: (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ⊓ (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ⊓ w ∈ᴮ x ≤ w ∈ᴮ z
  have hxy_spec : (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ≤ w ∈ᴮ x ⟹ w ∈ᴮ y := iInf_le _ w
  have hyz_spec : (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ≤ w ∈ᴮ y ⟹ w ∈ᴮ z := iInf_le _ w
  have hxy : (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ⊓ (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ⊓ w ∈ᴮ x
      ≤ w ∈ᴮ y :=
    le_trans (le_inf ((inf_le_left.trans inf_le_left).trans hxy_spec) inf_le_right) bv_imp_elim
  calc (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ⊓ (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ⊓ w ∈ᴮ x
      ≤ (w ∈ᴮ y ⟹ w ∈ᴮ z) ⊓ w ∈ᴮ y :=
        le_inf ((inf_le_left.trans inf_le_right).trans hyz_spec) hxy
    _ ≤ w ∈ᴮ z := bv_imp_elim

-- src/bvm.lean:576
lemma subset_trans' {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ x ⊆ᴮ y) (H₂ : Γ ≤ y ⊆ᴮ z) : Γ ≤ x ⊆ᴮ z :=
  poset_yoneda_inv Γ subset_trans (le_inf H₁ H₂)

-- src/bvm.lean:587
lemma mem_of_mem_subset {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₂ : Γ ≤ y ⊆ᴮ z) (H₁ : Γ ≤ x ∈ᴮ y) : Γ ≤ x ∈ᴮ z := by
  rw [subset_unfold'] at H₂
  exact context_imp_elim (context_specialize H₂ x) H₁

-- src/bvm.lean:603
lemma subst_congr_subset_left {x v u : bSet 𝔹} :
    ((v ⊆ᴮ u) ⊓ (x =ᴮ v) : 𝔹) ≤ (x ⊆ᴮ u) := by
  rw [subset_unfold' (x := x), subset_unfold' (x := v)]
  apply le_iInf; intro z
  rw [← deduction]
  -- Goal: (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ x =ᴮ v ⊓ z ∈ x ≤ z ∈ u
  have h_mem : (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ x =ᴮ v ⊓ z ∈ᴮ x ≤ z ∈ᴮ v := by
    calc (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ x =ᴮ v ⊓ z ∈ᴮ x
        ≤ x =ᴮ v ⊓ z ∈ᴮ x :=
          le_inf (inf_le_left.trans inf_le_right) inf_le_right
      _ ≤ z ∈ᴮ v := subst_congr_mem_right
  have h_sub : (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ z ∈ᴮ v ≤ z ∈ᴮ u := by
    have hspec : (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ≤ z ∈ᴮ v ⟹ z ∈ᴮ u := iInf_le _ z
    exact le_trans (le_inf (inf_le_left.trans hspec) inf_le_right) bv_imp_elim
  calc (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ x =ᴮ v ⊓ z ∈ᴮ x
      ≤ (⨅ w, w ∈ᴮ v ⟹ w ∈ᴮ u) ⊓ z ∈ᴮ v :=
        le_inf (inf_le_left.trans inf_le_left) h_mem
    _ ≤ z ∈ᴮ u := h_sub

-- src/bvm.lean:616
lemma subst_congr_subset_right {x v u : bSet 𝔹} :
    ((v ⊆ᴮ u) ⊓ (u =ᴮ x) : 𝔹) ≤ (v ⊆ᴮ x) := by
  rw [subset_unfold, subset_unfold]
  apply le_iInf; intro j
  rw [← deduction]
  -- Goal: (⨅ j', bval v j' ⟹ func v j' ∈ u) ⊓ u =ᴮ x ⊓ bval v j ≤ func v j ∈ x
  calc (⨅ j', v.bval j' ⟹ v.func j' ∈ᴮ u) ⊓ u =ᴮ x ⊓ v.bval j
      ≤ (v.bval j ⟹ v.func j ∈ᴮ u) ⊓ v.bval j ⊓ u =ᴮ x :=
        le_inf (le_inf ((inf_le_left.trans inf_le_left).trans (iInf_le _ j)) inf_le_right)
               (inf_le_left.trans inf_le_right)
    _ ≤ v.func j ∈ᴮ u ⊓ u =ᴮ x :=
        le_inf (le_trans inf_le_left bv_imp_elim) inf_le_right
    _ ≤ v.func j ∈ᴮ x := by
        rw [inf_comm]; exact subst_congr_mem_right

-- src/bvm.lean:626
lemma bv_rw'₀ {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {H_new : Γ ≤ ϕ y} : Γ ≤ ϕ x :=
  poset_yoneda_inv Γ (h_congr _ _) (le_inf (by rwa [bv_eq_symm]) H_new)

-- src/bvm.lean:634
@[reducible] def B_ext (ϕ : bSet 𝔹 → 𝔹) : Prop :=
  ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y

-- src/bvm.lean:639
lemma bv_rw' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : B_ext ϕ} {H_new : Γ ≤ ϕ y} : Γ ≤ ϕ x :=
  bv_rw'₀ H (h_congr := h_congr) (H_new := H_new)

-- src/bvm.lean:642
@[simp] lemma B_ext_bv_eq_left {y : bSet 𝔹} : B_ext (fun x => x =ᴮ y) :=
  fun _ _ => by rw [bv_eq_symm (x := _) (y := _)]; exact bv_eq_trans

-- src/bvm.lean:645
@[simp] lemma B_ext_bv_eq_right {x : bSet 𝔹} : B_ext (fun y => x =ᴮ y) :=
  fun _ _ => by rw [inf_comm]; exact bv_eq_trans

-- src/bvm.lean:648
@[simp] lemma B_ext_mem_left {y : bSet 𝔹} : B_ext (fun x => x ∈ᴮ y) :=
  fun _ _ => subst_congr_mem_left

-- src/bvm.lean:651
@[simp] lemma B_ext_mem_right {x : bSet 𝔹} : B_ext (fun y => x ∈ᴮ y) :=
  fun _ _ => subst_congr_mem_right

-- src/bvm.lean:654
@[simp] lemma B_ext_subset_left {y : bSet 𝔹} : B_ext (fun x => x ⊆ᴮ y) :=
  fun _ _ => by rw [inf_comm, bv_eq_symm]; exact subst_congr_subset_left

-- src/bvm.lean:657
@[simp] lemma B_ext_subset_right {x : bSet 𝔹} : B_ext (fun y => x ⊆ᴮ y) :=
  fun _ _ => by rw [inf_comm]; exact subst_congr_subset_right

-- src/bvm.lean:660
@[simp] lemma B_ext_sup {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} {h₁ : B_ext ϕ₁} {h₂ : B_ext ϕ₂} :
    B_ext (fun x => ϕ₁ x ⊔ ϕ₂ x) := by
  intros x y
  rw [inf_comm, deduction]
  apply sup_le
  · rw [← deduction]; exact le_trans (by rw [inf_comm]; exact h₁ x y) le_sup_left
  · rw [← deduction]; exact le_trans (by rw [inf_comm]; exact h₂ x y) le_sup_right

-- src/bvm.lean:668
@[simp] lemma B_ext_inf {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} (h₁ : B_ext ϕ₁) (h₂ : B_ext ϕ₂) :
    B_ext (fun x => ϕ₁ x ⊓ ϕ₂ x) := by
  intros x y
  apply le_inf
  · exact le_trans (inf_le_inf_left _ inf_le_left) (h₁ x y)
  · exact le_trans (inf_le_inf_left _ inf_le_right) (h₂ x y)

-- src/bvm.lean:676
@[simp] lemma B_ext_imp {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} {h₁ : B_ext ϕ₁} {h₂ : B_ext ϕ₂} :
    B_ext (fun x => ϕ₁ x ⟹ ϕ₂ x) := by
  intros x y
  rw [← deduction]
  -- x =ᴮ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ y ≤ ϕ₂ y
  -- Step: ϕ₁ y → ϕ₁ x (via h₁ with y =ᴮ x)
  -- Step: (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ x → ϕ₂ x (bv_imp_elim)
  -- Step: ϕ₂ x → ϕ₂ y (via h₂ with x =ᴮ y)
  have step1 : x =ᴮ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ y ≤ ϕ₁ x := by
    apply le_trans _ (h₁ y x)
    · exact le_inf (inf_le_left.trans (by rw [bv_eq_symm]; exact inf_le_left)) inf_le_right
  have step2 : x =ᴮ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ y ≤ ϕ₂ x :=
    le_trans (le_inf (inf_le_left.trans inf_le_right) step1) bv_imp_elim
  exact le_trans (le_inf (inf_le_left.trans inf_le_left) step2) (h₂ x y)

-- src/bvm.lean:684
@[simp] lemma B_ext_const {b : 𝔹} : B_ext (fun _ : bSet 𝔹 => b) :=
  fun _ _ => inf_le_right

-- src/bvm.lean:687
@[simp] lemma B_ext_neg {ϕ₁ : bSet 𝔹 → 𝔹} {h : B_ext ϕ₁} : B_ext (fun x => (ϕ₁ x)ᶜ) := by
  simp only [← imp_bot]
  exact B_ext_imp (h₁ := h) (h₂ := B_ext_const)

-- src/bvm.lean:690
@[simp] lemma B_ext_iInf {ι : Type*} {Ψ : ι → (bSet 𝔹 → 𝔹)} {h : ∀ i, B_ext (Ψ i)} :
    B_ext (fun x => ⨅ i, Ψ i x) := by
  intros x y
  apply le_iInf; intro i
  apply bv_specialize_right i
  exact h i x y

-- src/bvm.lean:693
@[simp] lemma B_ext_iSup {ι : Type*} {ψ : ι → (bSet 𝔹 → 𝔹)} {h : ∀ i, B_ext (ψ i)} :
    B_ext (fun x => ⨆ i, ψ i x) := by
  intros x y
  apply bv_cases_right; intro i
  apply bv_use i
  exact h i x y

-- src/bvm.lean:698
@[reducible] def B_congr (t : bSet 𝔹 → bSet 𝔹) : Prop :=
  ∀ {x₁ x₂ : bSet 𝔹} {Γ : 𝔹}, Γ ≤ x₁ =ᴮ x₂ → Γ ≤ t x₁ =ᴮ t x₂

-- src/bvm.lean:702 (dropping the meta-tactic autoParam on H and H')
@[simp] lemma B_ext_term (ϕ : bSet 𝔹 → 𝔹) (t : bSet 𝔹 → bSet 𝔹)
    (H : B_ext ϕ) (H' : B_congr t) :
    B_ext (fun z => ϕ (t z)) := by
  intros x y
  -- x =ᴮ y ⊓ ϕ (t x) ≤ ϕ (t y)
  calc x =ᴮ y ⊓ ϕ (t x)
      ≤ t x =ᴮ t y ⊓ ϕ (t x) :=
        le_inf (H' inf_le_left) inf_le_right
    _ ≤ ϕ (t y) := H (t x) (t y)

-- src/bvm.lean:712
lemma bv_rw'' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    (H_new : Γ ≤ ϕ x) (h_congr : B_ext ϕ) : Γ ≤ ϕ y :=
  poset_yoneda_inv Γ (h_congr x y) (le_inf H H_new)

-- src/bvm.lean:719
lemma mem_congr {Γ : 𝔹} {x₁ x₂ y₁ y₂ : bSet 𝔹}
    (H₁ : Γ ≤ x₁ =ᴮ y₁) (H₂ : Γ ≤ x₂ =ᴮ y₂) (H₃ : Γ ≤ x₁ ∈ᴮ x₂) :
    Γ ≤ y₁ ∈ᴮ y₂ := by
  apply bv_rw' (H := by rwa [bv_eq_symm]) (h_congr := B_ext_mem_left)
  apply bv_rw' (H := by rwa [bv_eq_symm]) (h_congr := B_ext_mem_right)
  exact H₃

-- src/bvm.lean:723


-- src/bvm.lean:727


-- src/bvm.lean:729


-- src/bvm.lean:732


-- src/bvm.lean:742


-- src/bvm.lean:746


-- ============================================================
-- Task 10b: src/bvm.lean lines 750-1400
-- is_definite, empty lemmas, insert1 congr, singletons,
-- mixture, mixing_lemma, smallness, well_ordering,
-- mixing_corollaries, smallness', cores
-- ============================================================

-- src/bvm.lean:817


-- src/bvm.lean:819
lemma eq_empty {u : bSet 𝔹} : u =ᴮ ∅ = (⨆ i, u.bval i)ᶜ := by
  apply le_antisymm
  · -- u =ᴮ ∅ ≤ (⨆ i, u.bval i)ᶜ = ⨅ i, (u.bval i)ᶜ
    rw [compl_iSup]
    apply le_iInf; intro i
    -- u =ᴮ ∅ ≤ (u.bval i)ᶜ, i.e., u =ᴮ ∅ ⊓ u.bval i ≤ ⊥
    rw [← imp_bot, ← deduction]
    -- u.func i ∈ᴮ ∅ = ⊥ (since ∅ has no elements)
    have h2 : u.func i ∈ᴮ ∅ = ⊥ := by
      rw [mem_unfold]; exact exists_over_empty _
    -- u =ᴮ ∅ ≤ u.bval i ⟹ u.func i ∈ᴮ ∅ = u.bval i ⟹ ⊥
    have h1 : u =ᴮ ∅ ≤ u.bval i ⟹ u.func i ∈ᴮ ∅ := by
      rw [bv_eq_unfold]; exact inf_le_left.trans (iInf_le _ i)
    rw [h2] at h1
    -- h1 : u =ᴮ ∅ ≤ u.bval i ⟹ ⊥ = (u.bval i)ᶜ
    rw [imp_bot] at h1
    exact le_trans (le_inf (inf_le_left.trans h1) inf_le_right) disjoint_compl_left.le_bot
  · -- (⨆ i, u.bval i)ᶜ ≤ u =ᴮ ∅
    rw [bv_eq_unfold]
    apply le_inf
    · apply le_iInf; intro j
      -- Goal: (⨆ i, u.bval i)ᶜ ≤ u.bval j ⟹ u.func j ∈ᴮ ∅
      have : u.func j ∈ᴮ ∅ = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
      rw [this, imp_bot]
      exact compl_le_compl (le_iSup _ j)
    · apply le_iInf; intro j; exact j.elim

-- src/bvm.lean:825
@[simp] lemma empty_subset {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ ∅ ⊆ᴮ x := by
  rw [subset_unfold]
  apply le_iInf; intro i
  exact i.elim

-- src/bvm.lean:828


-- src/bvm.lean:830
lemma bot_of_mem_empty {x : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ∈ᴮ ∅) : Γ ≤ ⊥ := by
  have hmem : x ∈ᴮ ∅ = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
  rw [hmem] at H; exact H

-- src/bvm.lean:833
@[simp] lemma subst_congr_insert1_left {u w v : bSet 𝔹} :
    u =ᴮ w ≤ bSet.insert1 u v =ᴮ bSet.insert1 w v := by
  cases v with | mk α A B =>
  simp only [bSet.insert1, bSet.insert, bv_eq, mem, iInf_option, iSup_option,
    top_inf_eq, inf_top_eq]
  apply le_inf
  · -- Forward
    apply le_inf
    · -- u =ᴮ w ≤ ⊤ ⟹ (u =ᴮ w ⊔ ⨆ b, B b ⊓ u =ᴮ A b)
      -- ⊤ ⟹ X = X (since ⊤ᶜ = ⊥, ⊥ ⊔ X = X)
      have : (⊤ : 𝔹) ⟹ (u =ᴮ w ⊔ ⨆ b, B b ⊓ u =ᴮ A b) = u =ᴮ w ⊔ ⨆ b, B b ⊓ u =ᴮ A b := by
        unfold imp; simp
      rw [this]; exact le_sup_left
    · apply le_iInf; intro i
      -- B i ⟹ (A i =ᴮ w ⊔ ⨆ b, B b ⊓ A i =ᴮ A b)
      -- Need: u =ᴮ w ≤ B i ⟹ (...)
      -- B i ≤ A i ∈ᴮ v ≤ A i ∈ᴮ v ⊔ (A i =ᴮ w) by le_sup_right
      -- Wait, we need: u =ᴮ w ⊓ B i ≤ A i =ᴮ w ⊔ ⨆ b, B b ⊓ A i =ᴮ A b
      rw [← deduction]
      exact le_trans inf_le_right (le_trans (mem_mk' (mk α A B) i) le_sup_right)
  · -- Backward: second component (⨅ j) of bv_eq
    apply le_inf
    · -- ⊤ component: u =ᴮ w ≤ ⊤ ⟹ X where X = u =ᴮ w ⊔ ... (after simp)
      -- ⊤ ⟹ X = X since ⊤ᶜ = ⊥, ⊥ ⊔ X = X
      -- So need u =ᴮ w ≤ X = u =ᴮ w ⊔ ... which is le_sup_left
      -- Use imp_self_eq_top or directly show ⊤ ⟹ X = X
      have : (⊤ : 𝔹) ⟹ (u =ᴮ w ⊔ ⨆ b, B b ⊓ A b =ᴮ w) = u =ᴮ w ⊔ ⨆ b, B b ⊓ A b =ᴮ w := by
        unfold imp; simp
      rw [this]; exact le_sup_left
    · apply le_iInf; intro i
      rw [← deduction]
      -- After simp, backward ⨅ i component:
      -- u =ᴮ w ⊓ B i ≤ u =ᴮ A i ⊔ ⨆ b, B b ⊓ A b =ᴮ A i  (approx)
      -- Use B i ≤ A i ∈ᴮ v = ⨆ b, B b ⊓ A i =ᴮ A b
      -- but simp might have reordered to A b =ᴮ A i
      -- Use inf_le_right to get B i, then mem_mk' to get the iSup
      -- Goal (after simp): u =ᴮ w ⊓ B i ≤ u =ᴮ A i ⊔ ⨆ b, B b ⊓ A b =ᴮ A i
      -- B i ≤ B i ⊓ (A i =ᴮ A i = ⊤) ≤ ⨆ b, B b ⊓ A b =ᴮ A i ≤ u =ᴮ A i ⊔ ...
      apply le_trans inf_le_right
      apply le_trans _ le_sup_right
      exact le_iSup_of_le i (by simp [bv_eq_refl])

-- src/bvm.lean:839
@[simp] lemma subst_congr_insert1_left' {u w v : bSet 𝔹} {c : 𝔹} (h : c ≤ u =ᴮ w) :
    c ≤ bSet.insert1 u v =ᴮ bSet.insert1 w v :=
  le_trans h subst_congr_insert1_left

-- src/bvm.lean:845
@[simp] lemma subst_congr_insert1_right {u w v : bSet 𝔹} :
    u =ᴮ w ≤ bSet.insert1 v u =ᴮ bSet.insert1 v w := by
  rw [eq_iff_subset_subset (x := bSet.insert1 v u) (y := bSet.insert1 v w)]
  apply le_inf
  · -- insert1 v u ⊆ insert1 v w
    rw [subset_unfold']
    apply le_iInf; intro z
    rw [← deduction, show z ∈ᴮ bSet.insert1 v u = z =ᴮ v ⊔ z ∈ᴮ u from mem_insert1,
        show z ∈ᴮ bSet.insert1 v w = z =ᴮ v ⊔ z ∈ᴮ w from mem_insert1]
    apply bv_or_elim_right
    · exact le_trans inf_le_right le_sup_left
    · apply le_trans _ le_sup_right; exact subst_congr_mem_right
  · -- insert1 v w ⊆ insert1 v u
    rw [subset_unfold']
    apply le_iInf; intro z
    rw [← deduction, show z ∈ᴮ bSet.insert1 v w = z =ᴮ v ⊔ z ∈ᴮ w from mem_insert1,
        show z ∈ᴮ bSet.insert1 v u = z =ᴮ v ⊔ z ∈ᴮ u from mem_insert1]
    apply bv_or_elim_right
    · exact le_trans inf_le_right le_sup_left
    · apply le_trans _ le_sup_right
      rw [bv_eq_symm]; exact subst_congr_mem_right

-- src/bvm.lean:852
@[simp] lemma subst_congr_insert1_right' {u w v : bSet 𝔹} {c : 𝔹} (h : c ≤ u =ᴮ w) :
    c ≤ bSet.insert1 v u =ᴮ bSet.insert1 v w :=
  le_trans h subst_congr_insert1_right

-- src/bvm.lean:842
@[simp] lemma subst_congr_insert1_left'' {u w v : bSet 𝔹} {c : 𝔹} (h : c ≤ u =ᴮ w) :
    c ≤ (bSet.insert1 v (bSet.insert1 u ∅)) =ᴮ (bSet.insert1 v (bSet.insert1 w ∅)) :=
  subst_congr_insert1_right' (subst_congr_insert1_left' h)

-- src/bvm.lean:855
@[simp] lemma subst_congr_insert1_right'' {u w v : bSet 𝔹} {c : 𝔹} (h : c ≤ u =ᴮ w) :
    c ≤ (bSet.insert1 u (bSet.insert1 v ∅)) =ᴮ (bSet.insert1 w (bSet.insert1 v ∅)) :=
  le_trans h subst_congr_insert1_left

/-! ### singleton lemmas -/

-- src/bvm.lean:860
@[simp] lemma eq_singleton_of_eq {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ x =ᴮ y) :
    c ≤ (bSet.insert1 x ∅) =ᴮ (bSet.insert1 y ∅) :=
  subst_congr_insert1_left' h

-- src/bvm.lean:863
lemma eq_of_eq_singleton {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ (bSet.insert1 x ∅) =ᴮ (bSet.insert1 y ∅)) :
    c ≤ x =ᴮ y := by
  -- {x} =ᴮ {y} ≤ x =ᴮ y via membership reasoning
  have mem_eq : x ∈ᴮ bSet.insert1 y ∅ = x =ᴮ y := by
    show x ∈ᴮ bSet.insert1 y ∅ = x =ᴮ y
    rw [show bSet.insert1 y ∅ = insert y ∅ from rfl, mem_insert1]
    have : x ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  -- From bSet.insert1 x ∅ =ᴮ bSet.insert1 y ∅, we get:
  -- bSet.insert1 x ∅ ⊆ bSet.insert1 y ∅, which gives x ∈ {y}
  -- since x ∈ {x} (by bval none = ⊤)
  have h1 : bSet.insert1 x ∅ =ᴮ bSet.insert1 y ∅ ≤ bSet.insert1 x ∅ ⊆ᴮ bSet.insert1 y ∅ := by
    rw [bv_eq_unfold]; exact inf_le_left
  have h2 : bSet.insert1 x ∅ ⊆ᴮ bSet.insert1 y ∅ ≤ x ∈ᴮ bSet.insert1 y ∅ := by
    rw [subset_unfold']
    apply iInf_le_of_le x
    -- Goal: x ∈ {x} ⟹ x ∈ {y} ≤ x ∈ {y}
    -- x ∈ {x} = ⊤, so ⊤ ⟹ x ∈ {y} = x ∈ {y}
    have hmem : x ∈ᴮ bSet.insert1 x ∅ = ⊤ := by
      rw [show bSet.insert1 x ∅ = insert x ∅ from rfl, mem_insert1]
      simp [bv_eq_refl, mem_unfold, exists_over_empty]
    unfold imp
    rw [hmem, compl_top, bot_sup_eq]
  rw [mem_eq] at h2
  exact le_trans (le_trans h h1) h2

-- src/bvm.lean:874


-- src/bvm.lean:877


-- src/bvm.lean:879
@[simp] lemma singleton_type {x : bSet 𝔹} :
    (type (bSet.insert1 x ∅)) = Option PEmpty := by
  simp only [bSet.insert1, bSet.insert, bSet.type, empty, bSet.mk.injEq]
  rfl

-- src/bvm.lean:881
@[simp] lemma singleton_func {x : bSet 𝔹} {o : Option PEmpty} :
    func (bSet.insert1 x ∅) o = Option.casesOn o x (fun e => e.elim) := by
  simp only [bSet.insert1, bSet.insert]
  cases o with
  | none => rfl
  | some e => exact (e.elim)

-- src/bvm.lean:883
@[simp] lemma singleton_bval {x : bSet 𝔹} {o : Option PEmpty} :
    bval (bSet.insert1 x ∅) o = Option.casesOn o ⊤ (fun e => e.elim) := by
  simp only [bSet.insert1, bSet.insert]
  cases o with
  | none => rfl
  | some e => exact (e.elim)

-- src/bvm.lean:885
@[simp] lemma singleton_bval_none {x : bSet 𝔹} : bval (bSet.insert1 x ∅) none = ⊤ := by
  have := singleton_bval (x := x) (o := none)
  simp at this; exact this

/-! ### mixture / mixing lemma -/

-- src/bvm.lean:899
def mixture {ι : Type u} (a : ι → 𝔹) (u : ι → bSet 𝔹) : bSet 𝔹 :=
  ⟨Σ (i : ι), (u i).type, fun x => (u x.1).func x.2,
    fun x => ⨆ (j : ι), a j ⊓ (u x.1).func x.2 ∈ᴮ u j⟩

-- src/bvm.lean:904
/-- Given a₁ a₂ : 𝔹, return the canonical map from ULift Bool to 𝔹 given by false ↦ a₁, true ↦ a₂ -/
@[reducible] def bool_map {α : Type*} (a₁ a₂ : α) : ULift Bool → α :=
  fun x => Bool.rec a₁ a₂ x.down

-- src/bvm.lean:908
def two_term_mixture (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) : bSet 𝔹 :=
  @mixture 𝔹 _ (ULift Bool) (bool_map a₁ a₂) (bool_map u₁ u₂)

-- src/bvm.lean:921
@[simp] lemma bval_mixture {ι : Type u} {a : ι → 𝔹} {u : ι → bSet 𝔹} :
    (mixture a u).bval = fun x => ⨆ (j : ι), a j ⊓ (u x.1).func x.2 ∈ᴮ u j := rfl

-- src/bvm.lean:925
@[simp] lemma two_term_mixture_bval (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (u₁ u₂ : bSet 𝔹) :
    ∀ i, (two_term_mixture a₁ a₂ h_anti u₁ u₂).bval i =
      (a₁ ⊓ ((two_term_mixture a₁ a₂ h_anti u₁ u₂).func i ∈ᴮ u₁)) ⊔
      (a₂ ⊓ ((two_term_mixture a₁ a₂ h_anti u₁ u₂).func i ∈ᴮ u₂)) := fun i => by
  simp only [two_term_mixture, bval_mixture, bool_map]
  -- bval i = ⨆ (j : ULift Bool), Bool.rec a₁ a₂ j.down ⊓ ...
  apply le_antisymm
  · apply iSup_le; intro ⟨j⟩; cases j
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le
    · exact le_iSup_of_le ⟨false⟩ le_rfl
    · exact le_iSup_of_le ⟨true⟩ le_rfl

-- src/bvm.lean:933


-- src/bvm.lean:914


-- src/bvm.lean:937 — Mixing Lemma
lemma mixing_lemma' {ι : Type u} (a : ι → 𝔹) (τ : ι → bSet 𝔹)
    (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) :
    ∀ i : ι, a i ≤ (mixture a τ) =ᴮ τ i := fun i => by
  rw [bv_eq_unfold]
  apply le_inf
  · -- First: ⨅ i_z, bval (mixture a τ) i_z ⟹ func (mixture a τ) i_z ∈ᴮ τ i
    apply le_iInf; intro ⟨i_z_fst, i_z_snd⟩
    rw [← deduction]
    -- bval (mixture a τ) ⟨j, i_z_snd⟩ = ⨆ k, a k ⊓ (τ j).func i_z_snd ∈ᴮ τ k
    simp only [bval_mixture, mixture, func, bval]
    rw [inf_iSup_eq]
    apply iSup_le; intro j
    -- a i ⊓ a j ⊓ (τ j).func i_z_snd ∈ᴮ τ j ≤ (τ i_z_fst).func i_z_snd ∈ᴮ τ i
    -- Note: func (mixture a τ) ⟨j, ...⟩ = (τ j).func ...
    rw [← inf_assoc]
    -- a i ⊓ a j ≤ τ i =ᴮ τ j, so we can subst
    have h_eq := h_star i j
    -- a i ⊓ a j ⊓ (τ j).func i_z_snd ∈ᴮ τ j ≤ (τ i =ᴮ τ j) ⊓ (τ j).func i_z_snd ∈ᴮ τ j
    --   ≤ (τ j).func i_z_snd ∈ᴮ τ i  (by subst_congr_mem_right with bv_eq_symm)
    -- goal: a i ⊓ (a j ⊓ (τ i_z_fst).func i_z_snd ∈ᴮ τ j) ≤ (τ i_z_fst).func i_z_snd ∈ᴮ τ i
    have heq : a i ⊓ a j ≤ τ i =ᴮ τ j := h_eq
    calc a i ⊓ a j ⊓ (τ i_z_fst).func i_z_snd ∈ᴮ τ j
        ≤ (τ i =ᴮ τ j) ⊓ (τ i_z_fst).func i_z_snd ∈ᴮ τ j :=
          le_inf (inf_le_left.trans heq) inf_le_right
      _ = (τ j =ᴮ τ i) ⊓ (τ i_z_fst).func i_z_snd ∈ᴮ τ j := by rw [bv_eq_symm]
      _ ≤ (τ i_z_fst).func i_z_snd ∈ᴮ τ i := subst_congr_mem_right
  · -- Second: ⨅ i_z : (τ i).type, (τ i).bval i_z ⟹ (τ i).func i_z ∈ᴮ mixture a τ
    apply le_iInf; intro i_z
    rw [← deduction]
    -- a i ⊓ (τ i).bval i_z ≤ (τ i).func i_z ∈ᴮ mixture a τ
    -- Use index ⟨i, i_z⟩ in mixture: bval ⟨i, i_z⟩ ≥ a i ⊓ (τ i).bval i_z
    -- via a i ⊓ (τ i).bval i_z ≤ a i ⊓ (τ i).func i_z ∈ᴮ τ i ≤ bval ⟨i, i_z⟩
    -- and bval ⟨i, i_z⟩ ⊓ eq ≤ func ⟨i, i_z⟩ ∈ mixture...
    apply le_trans _ (mem_mk' (mixture a τ) ⟨i, i_z⟩)
    -- goal: a i ⊓ (τ i).bval i_z ≤ (mixture a τ).bval ⟨i, i_z⟩
    simp only [bval_mixture, mixture, func]
    -- bval ⟨i, i_z⟩ = ⨆ j, a j ⊓ (τ i).func i_z ∈ᴮ τ j
    apply le_iSup_of_le i
    -- a i ⊓ (τ i).bval i_z ≤ a i ⊓ (τ i).func i_z ∈ᴮ τ i
    exact le_inf inf_le_left (inf_le_right.trans (mem_mk' (τ i) i_z))

-- src/bvm.lean:954
lemma mixing_lemma {ι : Type u} (a : ι → 𝔹) (τ : ι → bSet 𝔹)
    (h_star : ∀ i j : ι, a i ⊓ a j ≤ τ i =ᴮ τ j) :
    ∃ x, ∀ i : ι, a i ≤ x =ᴮ τ i :=
  ⟨mixture a τ, fun i => mixing_lemma' a τ h_star i⟩

-- src/bvm.lean:957


/-! ### smallness -/

section smallness
variable {ϕ : bSet 𝔹 → 𝔹}

-- src/bvm.lean:988
@[reducible, simp] noncomputable def fiber_lift (b : ϕ '' Set.univ) :=
  Classical.indefiniteDescription (fun a : bSet 𝔹 => ϕ a = b.val) (by
    obtain ⟨x, _, hx⟩ := b.2
    exact ⟨x, hx⟩)

-- src/bvm.lean:992
noncomputable def B_small_witness : bSet 𝔹 :=
  ⟨ϕ '' Set.univ, fun b => (fiber_lift b).val, fun _ => ⊤⟩

-- src/bvm.lean:995
@[simp] lemma B_small_witness_spec : ∀ b, ϕ ((@B_small_witness _ _ ϕ).func b) = b.val :=
  fun b => (fiber_lift b).2

-- src/bvm.lean:998
lemma B_small_witness_supr :
    (⨆ (x : bSet 𝔹), ϕ x) = ⨆ (b : (@B_small_witness _ _ ϕ).type), ϕ (B_small_witness.func b) := by
  apply le_antisymm
  · apply iSup_le; intro x
    let b : (@B_small_witness _ _ ϕ).type :=
      ⟨ϕ x, Set.mem_image_of_mem _ (Set.mem_univ _)⟩
    apply le_iSup_of_le b
    -- ϕ x ≤ ϕ (B_small_witness.func b): note B_small_witness_spec b : ϕ (func b) = b.val = ϕ x
    have h := @B_small_witness_spec _ _ ϕ b
    -- h : ϕ (B_small_witness.func b) = b.val = ϕ x
    simp only [b, Subtype.coe_mk] at h
    exact h.symm.le
  · apply iSup_le; intro b
    apply le_iSup_of_le (fiber_lift b).val
    simp only [B_small_witness, func]
    exact le_rfl

-- src/bvm.lean:1007
@[reducible, simp] def not_b (b : 𝔹) : Set 𝔹 := fun y => y ≠ b

/-! ### well_ordering -/

section well_ordering
variable {α : Type*} (r : α → α → Prop) [IsWellOrder α r]
local infix:50 " ≺ " => r

-- src/bvm.lean:1013
def down_set (a : α) : Set α := {a' | a' ≺ a}

-- src/bvm.lean:1015


-- src/bvm.lean:1017


end well_ordering

variable (r : type (@B_small_witness _ _ ϕ) → type (@B_small_witness _ _ ϕ) → Prop)
variable [IsWellOrder _ r]
local infix:50 " ≺ " => r

-- src/bvm.lean:1029


-- src/bvm.lean:1036


-- src/bvm.lean:1045
def witness_antichain (b : type (@B_small_witness _ _ ϕ)) : 𝔹 :=
  b.val \ ⨆ (b' : ↑(down_set r b)), b'.val.val

-- src/bvm.lean:1048
lemma r_trichotomy (x y : type B_small_witness) : r x y ∨ x = y ∨ r y x :=
  @trichotomous _ r _ x y

-- src/bvm.lean:1050
lemma dichotomy_of_neq (x y : type B_small_witness) : x ≠ y → r x y ∨ r y x := by
  intro h
  rcases r_trichotomy r x y with h1 | rfl | h1
  · exact Or.inl h1
  · exact absurd rfl h
  · exact Or.inr h1

-- src/bvm.lean:1053


-- src/bvm.lean:1060
lemma witness_antichain_index {i j : type B_small_witness} (h_neq : i ≠ j) :
    witness_antichain r i ⊓ witness_antichain r j = ⊥ := by
  apply bot_unique
  simp only [witness_antichain, sdiff_eq]
  -- (i.val ⊓ (⨆ i' ∈ ds i, i'.val)ᶜ) ⊓ (j.val ⊓ (⨆ j' ∈ ds j, j'.val)ᶜ) ≤ ⊥
  rcases dichotomy_of_neq r i j h_neq with hij | hji
  · -- r i j: i.val ≤ ⨆ b' ∈ down_set r j, b'.val.val
    -- i : type B_small_witness = ϕ '' Set.univ, so i.val : 𝔹
    -- b' : ↑(down_set r j), so b'.val : type B_small_witness, b'.val.val : 𝔹
    have h_mem : i.val ≤ ⨆ (b' : ↑(down_set r j)), b'.val.val :=
      le_iSup_of_le ⟨i, hij⟩ le_rfl
    -- Strategy: use h_mem and inf_compl to get ⊥
    have step1 : i.val ⊓ (⨆ (b' : ↑(down_set r j)), b'.val.val)ᶜ ≤ ⊥ := by
      have : i.val ⊓ (⨆ (b' : ↑(down_set r j)), b'.val.val)ᶜ ≤
          (⨆ (b' : ↑(down_set r j)), b'.val.val) ⊓ (⨆ (b' : ↑(down_set r j)), b'.val.val)ᶜ :=
        inf_le_inf_right _ h_mem
      exact le_trans this (le_of_eq inf_compl_eq_bot)
    -- LHS ≤ ↑i ⊓ (⨆ ds j)ᶜ ≤ ⊥
    exact le_trans (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)) step1
  · -- r j i: symmetric
    have h_mem : j.val ≤ ⨆ (b' : ↑(down_set r i)), b'.val.val :=
      le_iSup_of_le ⟨j, hji⟩ le_rfl
    have step1 : (⨆ (b' : ↑(down_set r i)), b'.val.val)ᶜ ⊓ j.val ≤ ⊥ := by
      have : (⨆ (b' : ↑(down_set r i)), b'.val.val)ᶜ ⊓ j.val ≤
          (⨆ (b' : ↑(down_set r i)), b'.val.val)ᶜ ⊓ (⨆ (b' : ↑(down_set r i)), b'.val.val) :=
        inf_le_inf_left _ h_mem
      exact le_trans this (le_of_eq (by rw [inf_comm, inf_compl_eq_bot]))
    -- LHS ≤ (⨆ ds i)ᶜ ⊓ ↑j ≤ ⊥
    exact le_trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_left)) step1

-- src/bvm.lean:1075
-- Note: the Lean 3 `antichain` means pairwise inf = ⊥, which is exactly witness_antichain_index.
-- The Lean 4 IsAntichain (· ≤ ·) is a different (unprovable here) notion, so we state the
-- correct pairwise-disjoint version.


-- src/bvm.lean:1082
lemma witness_antichain_property : ∀ b : type (@B_small_witness _ _ ϕ), witness_antichain r b ≤ b.val := by
  intro b; unfold witness_antichain; exact sdiff_le

-- src/bvm.lean:1085
lemma supr_antichain2_contains :
    (⨆ (b' : type (@B_small_witness _ _ ϕ)), ϕ (func (@B_small_witness _ _ ϕ) b')) ≤
    ⨆ (b : type (@B_small_witness _ _ ϕ)), witness_antichain r b := by
  apply iSup_le
  intro i
  -- B_small_witness_spec: ϕ (func B_small_witness i) = i.val
  have hspec := @B_small_witness_spec _ _ ϕ i
  rw [hspec]
  -- By well-founded induction on i: show i.val ≤ ⨆ b, witness_antichain r b
  apply (IsWellFounded.wf (r := r)).induction i
  intro i ih
  -- Decompose: i.val = (i.val \ ⨆ j ∈ ds r i, j.val) ⊔ (i.val ⊓ ⨆ j ∈ ds r i, j.val)
  --           = witness_antichain r i ⊔ (i.val ⊓ ⨆ j ∈ ds r i, j.val)
  calc i.val
      = witness_antichain r i ⊔ (i.val ⊓ ⨆ (j : ↑(down_set r i)), j.val.val) := by
          simp only [witness_antichain]; exact (sup_sdiff_inf _ _).symm
    _ ≤ (⨆ b, witness_antichain r b) ⊔ (⨆ b, witness_antichain r b) := by
          apply sup_le_sup
          · exact le_iSup (witness_antichain r) i
          · -- i.val ⊓ ⨆ j ∈ ds r i, j.val ≤ ⨆ j ∈ ds r i, j.val ≤ ⨆ b, w_ac b by IH
            calc i.val ⊓ ⨆ (j : ↑(down_set r i)), j.val.val
                ≤ ⨆ (j : ↑(down_set r i)), j.val.val := inf_le_right
              _ ≤ ⨆ b, witness_antichain r b := by
                  apply iSup_le; intro ⟨j, hj⟩; exact ih j hj
    _ = ⨆ b, witness_antichain r b := sup_idem _

end smallness

/-! ### maximum principle and AE_convert -/

-- src/bvm.lean:1107
lemma maximum_principle (ϕ : bSet 𝔹 → 𝔹) (h_congr : B_ext ϕ) : ∃ u, (⨆ (x : bSet 𝔹), ϕ x) = ϕ u := by
  -- Get a well-order r on type B_small_witness
  let r := @WellOrderingRel ((@B_small_witness 𝔹 _ ϕ).type)
  haveI : IsWellOrder _ r := WellOrderingRel.isWellOrder
  -- Hypothesis for mixing_lemma: w_ac i ⊓ w_ac j ≤ func i =ᴮ func j
  have mixing_hyp : ∀ i j : (@B_small_witness 𝔹 _ ϕ).type,
      witness_antichain r i ⊓ witness_antichain r j ≤
      ((@B_small_witness 𝔹 _ ϕ).func i) =ᴮ ((@B_small_witness 𝔹 _ ϕ).func j) := by
    intro i j
    by_cases h : i = j
    · subst h; simp [bv_eq_refl]
    · rw [witness_antichain_index r h]; exact bot_le
  -- Get u from mixing_lemma: ∀ i, w_ac i ≤ u =ᴮ func i
  obtain ⟨u, H_w⟩ := mixing_lemma (witness_antichain r) ((@B_small_witness 𝔹 _ ϕ).func) mixing_hyp
  refine ⟨u, le_antisymm ?_ (le_iSup ϕ u)⟩
  -- Forward: ⨆ x, ϕ x ≤ ϕ u
  rw [B_small_witness_supr]
  apply le_trans (supr_antichain2_contains r)
  apply iSup_le; intro ξ
  -- w_ac ξ ≤ u =ᴮ func ξ (from mixing), w_ac ξ ≤ ξ.val = ϕ (func ξ) (from spec/property)
  -- So w_ac ξ ≤ (func ξ =ᴮ u) ⊓ ϕ (func ξ) ≤ ϕ u (by h_congr)
  have hw_ξ := H_w ξ
  have hprop_ξ : witness_antichain r ξ ≤ ξ.val := witness_antichain_property r ξ
  have hspec_ξ : ϕ ((@B_small_witness 𝔹 _ ϕ).func ξ) = ξ.val := @B_small_witness_spec 𝔹 _ ϕ ξ
  calc witness_antichain r ξ
      ≤ (u =ᴮ (@B_small_witness 𝔹 _ ϕ).func ξ) ⊓ ϕ ((@B_small_witness 𝔹 _ ϕ).func ξ) :=
          le_inf hw_ξ (hspec_ξ ▸ hprop_ξ)
    _ = ((@B_small_witness 𝔹 _ ϕ).func ξ =ᴮ u) ⊓ ϕ ((@B_small_witness 𝔹 _ ϕ).func ξ) := by
          rw [bv_eq_symm]
    _ ≤ ϕ u := h_congr _ _

-- src/bvm.lean:1131
/-- Extract an element witnessing a 𝔹-valued existential -/
lemma exists_convert {ϕ : bSet 𝔹 → 𝔹} {Γ : 𝔹} (H : Γ ≤ ⨆ x, ϕ x)
    (H_congr : B_ext ϕ) : ∃ u, Γ ≤ ϕ u := by
  obtain ⟨u, Hu⟩ := maximum_principle ϕ H_congr
  exact ⟨u, Hu ▸ H⟩

-- src/bvm.lean:1134


-- src/bvm.lean:1138


-- src/bvm.lean:1141


-- src/bvm.lean:1155
lemma AE_convert {α : Type*} (A : α → bSet 𝔹)
    (B : α → 𝔹) (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹) (h_congr : ∀ z, B_ext (fun x => ϕ z x)) :
    ∀ i : α, ∃ y : bSet 𝔹, (⨅ (j : α), (B j ⟹ ⨆ (z : bSet 𝔹), ϕ (A j) z)) ≤
      (B i ⟹ ϕ (A i) y) := by
  intro i
  obtain ⟨u', H'⟩ := maximum_principle (fun y => ϕ (A i) y) (h_congr (A i))
  exact ⟨u', le_trans (iInf_le (fun j => (B j ⟹ ⨆ (z : bSet 𝔹), ϕ (A j) z)) i)
    (@imp_le_of_right_le 𝔹 _ _ _ _ (le_of_eq H'))⟩

-- src/bvm.lean:1164


/-! ### mixing corollaries -/

section mixing_corollaries

-- src/bvm.lean:1175-1208
variable (X u₁ u₂ : bSet 𝔹) (a₁ a₂ : 𝔹) (h_anti : a₁ ⊓ a₂ = ⊥) (h_partition : a₁ ⊔ a₂ = ⊤)

-- src/bvm.lean:1178


-- src/bvm.lean:1192


end mixing_corollaries

/-! ### core_aux_lemma -/

-- src/bvm.lean:1210


-- src/bvm.lean:1229


/-! ### smallness' -/

section smallness'
variable {α : Type u} (ϕ' : bSet 𝔹 → α)

-- src/bvm.lean:1243
@[reducible, simp] noncomputable def fiber_lift' (b : ϕ' '' Set.univ) :
    { x : bSet 𝔹 // ϕ' x = b.val } :=
  Classical.indefiniteDescription (fun a : bSet 𝔹 => ϕ' a = b.val) (by
    obtain ⟨x, _, hx⟩ := b.2; exact ⟨x, hx⟩)

end smallness'

/-! ### cores -/

section cores

-- src/bvm.lean:1250
@[reducible] def pullback_eq_rel {α β : Type*} (f : α → β) (E : β → β → Prop) :
    α → α → Prop :=
  fun a₁ a₂ => E (f a₁) (f a₂)

-- src/bvm.lean:1253
def core {α : Type u} (u : bSet 𝔹) (S : α → bSet 𝔹) : Prop :=
  (∀ x : α, S x ∈ᴮ u = ⊤) ∧
  (∀ y : bSet 𝔹, y ∈ᴮ u = ⊤ → ∃! x_y : α, y =ᴮ S x_y = ⊤)

-- src/bvm.lean:1256
noncomputable def core_witness {α : Type u} {u : bSet 𝔹} {S : α → bSet 𝔹}
    (h_core : core u S) (x : bSet 𝔹) (h_X : x ∈ᴮ u = ⊤) :
    Σ' (x_y : α), x =ᴮ S x_y = ⊤ := by
  have h := h_core.2 x h_X
  exact ⟨h.choose, h.choose_spec.1⟩

-- src/bvm.lean:1262


-- src/bvm.lean:1272
lemma core_inj' {α : Type u} {u : bSet 𝔹} {S : α → bSet 𝔹} (h_core : core u S) :
    ∀ a b : α, S a =ᴮ S b = ⊤ → a = b := by
  intro x y H
  have h_left₁ := h_core.1 x
  obtain ⟨w1, H1, H2⟩ := h_core.2 (S x) h_left₁
  have Q2 : y = w1 := H2 y H
  have Q3 : x = w1 := H2 x (bv_eq_refl (S x))
  exact Q3.trans Q2.symm

-- src/bvm.lean:1282
def core.mk_ϕ (u : bSet 𝔹) : bSet 𝔹 → (u.type → 𝔹) :=
  fun x => fun a => u.bval a ⊓ x =ᴮ u.func a

-- src/bvm.lean:1285


-- src/bvm.lean:1296
noncomputable def core.S' (u : bSet 𝔹) : (core.mk_ϕ u '' Set.univ) → bSet 𝔹 :=
  fun x => (fiber_lift' (core.mk_ϕ u) x).val

-- src/bvm.lean:1299
def core.α_S'' (u : bSet 𝔹) : Type u :=
  { i : core.mk_ϕ u '' Set.univ // core.S' u i ∈ᴮ u = ⊤ }

-- src/bvm.lean:1301
noncomputable def core.S'' (u : bSet 𝔹) : core.α_S'' u → bSet 𝔹 :=
  fun x => core.S' u x.val

-- src/bvm.lean:1303


-- src/bvm.lean:1306
def core.bv_eq_top : bSet 𝔹 → bSet 𝔹 → Prop :=
  fun x₁ x₂ => x₁ =ᴮ x₂ = ⊤

-- src/bvm.lean:1309


-- src/bvm.lean:1320
instance core.S''_setoid (u : bSet 𝔹) : Setoid (core.α_S'' u) where
  r := pullback_eq_rel (core.S'' u) core.bv_eq_top
  iseqv := {
    refl := fun x => bv_eq_refl _
    symm := fun h => by simp only [pullback_eq_rel, core.bv_eq_top] at *; rwa [bv_eq_symm]
    trans := fun h1 h2 => by
      simp only [pullback_eq_rel, core.bv_eq_top] at *
      exact top_unique (le_trans (by rw [h1, h2]; simp) bv_eq_trans)
  }

-- src/bvm.lean:1331
noncomputable def core.mk_aux (u : bSet 𝔹) :
    (Quotient (@core.S''_setoid 𝔹 _ u)) → bSet 𝔹 :=
  fun x => (core.S'' u) (Quotient.out x)

-- src/bvm.lean:1334
@[reducible]  def image_mk {α β : Type*} {f : α → β} (a : α) : f '' Set.univ :=
  ⟨f a, Set.mem_image_of_mem _ (Set.mem_univ _)⟩

-- src/bvm.lean:1337


-- src/bvm.lean:1376
/-- Given a subset C of α, and an α-indexed core S, return the bSet whose underlying type is C -/
def bSet_of_core_set {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S)
    (C : Set α) : bSet 𝔹 :=
  ⟨C, fun x => S x, fun _ => ⊤⟩

-- src/bvm.lean:1379


-- src/bvm.lean:1382
@[simp] lemma of_core_type {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S}
    {C : Set α} : (bSet_of_core_set h C).type = C := rfl

-- src/bvm.lean:1384
@[simp] lemma of_core_bval {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} {h : core u S}
    {C : Set α} {i : C} : (bSet_of_core_set h C).bval i = ⊤ := rfl

-- src/bvm.lean:1387


-- src/bvm.lean:1392
/-- Given a core S for u, pull back the ordering -/
def subset' {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) : α → α → Prop :=
  fun a₁ a₂ => S a₁ ⊆ᴮ S a₂ = ⊤

-- src/bvm.lean:1397
def subset'_partial_order {u : bSet 𝔹} {α : Type u} {S : α → bSet 𝔹} (h : core u S) :
    PartialOrder α where
  le := subset' h
  le_refl := by intro a; simp [subset', bv_eq_refl]
  le_trans := by
    intro a b c
    simp only [subset']
    intro h₁ h₂
    rw [eq_top_iff] at h₁ h₂ ⊢
    exact subset_trans' h₁ h₂
  le_antisymm := by
    intro a b H₁ H₂
    apply core_inj' h
    simp only [subset'] at H₁ H₂
    rw [eq_top_iff] at H₁ H₂ ⊢
    exact subset_ext H₁ H₂

-- src/bvm.lean:1424
-- (these lemmas have complex `letI` formulations in Lean 3; skipped as auxiliary)


-- src/bvm.lean:1427


-- src/bvm.lean:1430
@[reducible] def exists_mem (x : bSet 𝔹) : 𝔹 := ⨆ (y : bSet 𝔹), y ∈ᴮ x

-- src/bvm.lean:1432
@[reducible] def not_empty (x : bSet 𝔹) : 𝔹 := (x =ᴮ ∅)ᶜ

-- src/bvm.lean:1435
lemma exists_mem_of_nonempty (u : bSet 𝔹) {Γ : 𝔹} (H : Γ ≤ (u =ᴮ ∅)ᶜ) : Γ ≤ ⨆ x, x ∈ᴮ u := by
  apply le_trans H
  simp [eq_empty]
  intro x
  apply bv_use (u.func x)
  apply mem_mk'

-- src/bvm.lean:1438
lemma nonempty_of_exists_mem (u : bSet 𝔹) {Γ : 𝔹} (H : Γ ≤ (⨆ x, x ∈ᴮ u)) : Γ ≤ (u =ᴮ ∅)ᶜ := by
  apply le_trans H
  simp [eq_empty]
  intro x
  rw [mem_unfold]
  apply bv_Or_elim
  intro i
  apply bv_use i
  apply inf_le_left

-- src/bvm.lean:1443
lemma nonempty_iff_exists_mem {u : bSet 𝔹} {Γ : 𝔹} : Γ ≤ (u =ᴮ ∅)ᶜ ↔ Γ ≤ ⨆ x, x ∈ᴮ u :=
  ⟨fun H => exists_mem_of_nonempty _ H, fun H => nonempty_of_exists_mem _ H⟩

-- src/bvm.lean:1450


-- src/bvm.lean:1459


-- src/bvm.lean:1470


end cores

section check_names

/-! `check` is the canonical embedding of PSet into bSet.
Note that a check-name is not only definite, but recursively definite. -/

-- src/bvm.lean:1479
@[simp] def check : PSet.{u} → bSet 𝔹
  | ⟨α, A⟩ => ⟨α, fun a => check (A a), fun _ => ⊤⟩

-- Postfix notation to match Lean 3 `̌ ` postfix notation
scoped postfix:9999 "̌" => check

-- src/bvm.lean:1484
@[simp] lemma check_type {α : Type u} {A : α → PSet} :
    (check (PSet.mk α A) : bSet 𝔹).type = α := rfl

-- src/bvm.lean:1487
@[simp] lemma check_type_iInf {α : Type u} {A : α → PSet} {s : α → 𝔹} :
    (⨅ (a : (check (PSet.mk α A) : bSet 𝔹).type), s a) = (⨅ (a : α), s a : 𝔹) :=
  rfl

-- src/bvm.lean:1491
@[simp] lemma check_type_iSup {α : Type u} {A : α → PSet} {s : α → 𝔹} :
    (⨆ (a : (check (PSet.mk α A) : bSet 𝔹).type), s a) = (⨆ (a : α), s a : 𝔹) :=
  rfl

-- src/bvm.lean:1494 (this is trivially true in Lean 4)

-- src/bvm.lean:1497
@[simp] lemma check_type' {x : PSet.{u}} :
    (check x : bSet 𝔹).type = x.Type := by
  cases x; simp [check]

-- src/bvm.lean:1500
@[simp] lemma check_type'_set {x : PSet} :
    Set (check x : bSet 𝔹).type = Set (x.Type) := by
  cases x; simp [check]

-- src/bvm.lean:1503
@[reducible, simp] def check_cast {x : PSet} (i : (check x : bSet 𝔹).type) : x.Type :=
  cast check_type' i

-- src/bvm.lean:1506
@[reducible, simp] def check_cast_symm {x : PSet} (i : x.Type) : (check x : bSet 𝔹).type :=
  cast check_type'.symm i

-- src/bvm.lean:1509
@[reducible, simp] def check_cast_set {x : PSet} (S : Set (check x : bSet 𝔹).type) :
    Set (x.Type) :=
  cast check_type'_set S

-- src/bvm.lean:1512
lemma check_func {x : PSet} {i} :
    (check x : bSet 𝔹).func i = check (x.Func (check_cast i)) := by
  cases x; rfl

-- src/bvm.lean:1516
lemma check_unfold {x : PSet.{u}} :
    (check x : bSet 𝔹) = bSet.mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by
  cases x; rfl

-- src/bvm.lean:1519
@[simp] lemma check_bval_top (x : PSet) {i} : (check x : bSet 𝔹).bval i = ⊤ := by
  cases x; rfl

-- src/bvm.lean:1521
@[simp] lemma check_bval_mk {α : Type u} {A : α → PSet} {i} :
    (check (PSet.mk α A) : bSet 𝔹).bval i = (⊤ : 𝔹) := rfl

-- src/bvm.lean:1523
@[simp] lemma check_empty_eq_empty : check (∅ : PSet) = (∅ : bSet 𝔹) := by
  -- (∅ : PSet) = PSet.mk PEmpty PEmpty.elim
  -- check (PSet.mk PEmpty f) = bSet.mk PEmpty (fun i => check (f i)) (fun _ => ⊤)
  -- (∅ : bSet 𝔹) = bSet.mk PEmpty PEmpty.elim PEmpty.elim
  -- Both have the same type (PEmpty) and all functions on PEmpty are equal
  show bSet.mk PEmpty (fun i => check (PEmpty.elim i)) (fun _ => ⊤) =
       bSet.mk PEmpty PEmpty.elim PEmpty.elim
  congr 1 <;> funext i <;> exact i.elim

-- src/bvm.lean:1527
@[simp] lemma mem_top_of_bval_top {u : bSet 𝔹} {i : u.type} (H_top : u.bval i = ⊤) :
    u.func i ∈ᴮ u = ⊤ := by
  apply top_unique; rw [← H_top]; apply mem_mk'

-- src/bvm.lean:1530
@[simp] lemma check_mem_top {x : PSet} {i : (check x : bSet 𝔹).type} :
    (check x : bSet 𝔹).func i ∈ᴮ check x = ⊤ :=
  mem_top_of_bval_top (check_bval_top x)

-- src/bvm.lean:1536
@[simp] lemma mem_check_of_mem {x : PSet} {i : x.Type} {Γ : 𝔹} :
    Γ ≤ check (x.Func i) ∈ᴮ check x := by
  rw [mem_unfold]
  apply bv_use (check_cast_symm i)
  simp only [true_and, le_inf_iff, le_top, check_cast_symm, check_bval_top]
  convert bv_refl
  cases x; rfl

-- src/bvm.lean:1544
lemma check_bv_eq_top_of_equiv {x y : PSet} (h : PSet.Equiv x y) :
    (check x : bSet 𝔹) =ᴮ check y = (⊤ : 𝔹) := by
  induction x generalizing y with
  | mk α A ih =>
  cases y with
  | mk β B =>
  rw [check_unfold, check_unfold, bv_eq]
  apply top_unique
  apply le_inf
  · apply le_iInf; intro a
    rw [← deduction, top_inf_eq]
    obtain ⟨b, hb⟩ := h.1 a
    exact le_iSup_of_le b (le_inf le_top (le_of_eq (ih a hb).symm))
  · apply le_iInf; intro b
    rw [← deduction, top_inf_eq]
    obtain ⟨a, ha⟩ := h.2 b
    exact le_iSup_of_le a (le_inf le_top (le_of_eq (ih a ha).symm))

-- src/bvm.lean:1556
lemma check_bv_eq {x y : PSet} {Γ : 𝔹} (H : PSet.Equiv x y) :
    (Γ : 𝔹) ≤ check x =ᴮ check y := by
  exact le_trans le_top (by rw [top_le_iff]; exact check_bv_eq_top_of_equiv H)

-- src/bvm.lean:1560


-- src/bvm.lean:1564
lemma check_bv_eq_bot_of_not_equiv {x y : PSet} (H : ¬ PSet.Equiv x y) :
    (check x : bSet 𝔹) =ᴮ check y = (⊥ : 𝔹) := by
  induction x generalizing y with
  | mk α A ih =>
  cases y with
  | mk β B =>
  rw [check_unfold, check_unfold, bv_eq]
  apply bot_unique
  rcases PSet.not_equiv H with ⟨a, ha⟩ | ⟨b, hb⟩
  · -- ∃ a : α, ∀ b : β, ¬ (A a).Equiv (B b) → forward direction ≤ ⊥
    apply inf_le_left.trans; apply iInf_le_of_le a
    simp only [imp, compl_top, bot_sup_eq]
    apply iSup_le; intro b; simp only [top_inf_eq]
    exact le_of_eq (@ih a (B b) (ha b))
  · -- ∃ b : β, ∀ a : α, ¬ (A a).Equiv (B b) → backward direction ≤ ⊥
    apply inf_le_right.trans; apply iInf_le_of_le b
    simp only [imp, compl_top, bot_sup_eq]
    apply iSup_le; intro a; simp only [top_inf_eq]
    exact le_of_eq (@ih a (B b) (hb a))

-- src/bvm.lean:1573


-- src/bvm.lean:1581


-- src/bvm.lean:1600


-- src/bvm.lean:1609


-- src/bvm.lean:1612


-- src/bvm.lean:1619


-- src/bvm.lean:1625
@[simp] lemma check_insert (a b : PSet) :
    check (PSet.insert a b) = (bSet.insert1 (check a) (check b) : bSet 𝔹) := by
  cases a with | mk α A => cases b with | mk β B =>
  -- Both are bSet.mk (Option β) (fun o => ...) (fun _ => ⊤)
  -- LHS: check (PSet.insert a b)
  -- = check (PSet.mk (Option β) (fun o => Option.rec (PSet.mk α A) B o))
  -- = bSet.mk (Option β) (fun o => check (Option.rec (PSet.mk α A) B o)) (fun _ => ⊤)
  -- = bSet.mk (Option β) (fun o => Option.rec (check (PSet.mk α A)) (fun i => check (B i)) o) (fun _ => ⊤)
  -- RHS: bSet.insert1 (check (PSet.mk α A)) (check (PSet.mk β B))
  -- = bSet.insert (check (PSet.mk α A)) ⊤ (bSet.mk β (fun i => check (B i)) (fun _ => ⊤))
  -- = bSet.mk (Option β) (fun o => Option.rec (check (PSet.mk α A)) (fun i => check (B i)) o) (fun _ => ⊤)
  simp only [PSet.insert, bSet.insert1, bSet.insert, check, PSet.mk_type, PSet.mk_func]
  congr 1
  · funext o; cases o <;> rfl
  · funext o; cases o <;> rfl

-- src/bvm.lean:1628


-- src/bvm.lean:1640


-- src/bvm.lean:1650


-- src/bvm.lean:1662


-- src/bvm.lean:1665


-- src/bvm.lean:1671


-- src/bvm.lean:1678


-- src/bvm.lean:1684
@[simp] lemma check_mem {x y : PSet} {Γ : 𝔹} (h_mem : x ∈ y) :
    (Γ : 𝔹) ≤ check x ∈ᴮ check y := by
  rw [mem_unfold]
  cases y
  rename_i β B
  simp only [PSet.mem_iff] at h_mem
  obtain ⟨w, hw⟩ := h_mem
  apply bv_use w
  apply le_inf
  · simp
  · exact check_bv_eq hw

-- src/bvm.lean:1691
@[simp] lemma check_subset_of_subset {x y : PSet} (h_subset : x ⊆ y) :
    (⊤ : 𝔹) ≤ check x ⊆ᴮ check y := by
  rw [subset_unfold]
  apply le_iInf; intro j
  simp only [check_bval_top, top_imp, check_func]
  -- Goal: ⊤ ≤ check (x.Func (check_cast j)) ∈ᴮ check y
  obtain ⟨b, hb⟩ := h_subset (check_cast j)
  exact check_mem ⟨b, hb⟩

-- src/bvm.lean:1699
lemma check_subset {x y : PSet} {Γ : 𝔹} (h_subset : x ⊆ y) :
    Γ ≤ check x ⊆ᴮ check y :=
  le_trans le_top (check_subset_of_subset h_subset)

-- src/bvm.lean:1702


-- src/bvm.lean:1713
@[simp] lemma check_exists_mem {y : PSet} (H_exists_mem : ∃ z, z ∈ y) {Γ : 𝔹} :
    Γ ≤ exists_mem (check y) := by
  obtain ⟨z, hz⟩ := H_exists_mem
  apply bv_use (check z)
  simp [check_mem hz]

-- src/bvm.lean:1746


-- src/bvm.lean:1755


-- src/bvm.lean:1762


-- src/bvm.lean:1766


-- src/bvm.lean:1775


-- src/bvm.lean:1787


end check_names

-- src/bvm.lean:1802-1836 — collect definitions (outside section to avoid section var issues)

/-- The choice function underlying collect -/
noncomputable def collect.func
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (u : bSet 𝔹) : u.type → bSet 𝔹 :=
  Classical.choose (Classical.axiomOfChoice
    (AE_convert u.func u.bval ϕ (by intro z; intro xv yv; exact h_congr_right xv yv z)))

/-- The collect bSet -/
noncomputable def collect
    (ϕ : bSet 𝔹 → bSet 𝔹 → 𝔹)
    (h_congr_right : ∀ x y z, x =ᴮ y ⊓ ϕ z x ≤ ϕ z y)
    (h_congr_left : ∀ x y z, x =ᴮ y ⊓ ϕ x z ≤ ϕ y z)
    (u : bSet 𝔹) : bSet 𝔹 :=
  ⟨u.type, collect.func ϕ h_congr_right u, u.bval⟩



-- src/bvm.lean:1814


-- src/bvm.lean:1825



-- src/bvm.lean:1844


-- src/bvm.lean:1860
/-- The boolean-valued unionset operator -/
def bv_union (u : bSet 𝔹) : bSet 𝔹 :=
  ⟨Σ (i : u.type), (u.func i).type,
   fun x => (u.func x.1).func x.2,
   fun x => ⨆ (y : u.type), u.bval y ⊓ (u.func x.1).func x.2 ∈ᴮ u.func y⟩

-- src/bvm.lean:1871
lemma bv_union_spec (u : bSet 𝔹) : ⊤ ≤ ⨅ (x : bSet 𝔹),
    (x ∈ᴮ bv_union u ⟹ ⨆ (y : u.type), u.bval y ⊓ x ∈ᴮ u.func y) ⊓
    ((⨆ (y : u.type), u.bval y ⊓ x ∈ᴮ u.func y) ⟹ x ∈ᴮ bv_union u) := by
  apply le_iInf; intro x
  apply le_inf
  · -- Forward: x ∈ bv_union u → ⨆ y, u.bval y ⊓ x ∈ u.func y
    rw [← deduction, top_inf_eq, mem_unfold (v := bv_union u)]
    -- after unfolding, bval⟨a,i⟩ = ⨆ y, u.bval y ⊓ (u.func a).func i ∈ u.func y
    -- func ⟨a,i⟩ = (u.func a).func i
    apply iSup_le; intro ⟨a, i⟩
    -- goal: (bv_union u).bval ⟨a,i⟩ ⊓ x =ᴮ (bv_union u).func ⟨a,i⟩ ≤ ⨆ y, u.bval y ⊓ x ∈ u.func y
    -- (bv_union u).bval ⟨a,i⟩ = ⨆ y, u.bval y ⊓ (u.func a).func i ∈ u.func y
    -- (bv_union u).func ⟨a,i⟩ = (u.func a).func i
    change (⨆ y, u.bval y ⊓ (u.func a).func i ∈ᴮ u.func y) ⊓ x =ᴮ (u.func a).func i ≤ _
    rw [iSup_inf_eq]
    apply iSup_le; intro y
    apply le_iSup_of_le y
    -- (u.bval y ⊓ (u.func a).func i ∈ u.func y) ⊓ x =ᴮ (u.func a).func i ≤ u.bval y ⊓ x ∈ u.func y
    apply le_inf (inf_le_left.trans inf_le_left)
    -- Need: ... ≤ x ∈ u.func y via subst_congr_mem_left (u.func a).func i =ᴮ x ⊓ ... ∈ u.func y
    exact poset_yoneda_inv _ subst_congr_mem_left
      (le_inf (by rw [← bv_eq_symm]; exact inf_le_right) (inf_le_left.trans inf_le_right))
  · -- Backward: ⨆ y, u.bval y ⊓ x ∈ u.func y → x ∈ bv_union u
    rw [← deduction, top_inf_eq, mem_unfold (v := bv_union u)]
    apply iSup_le; intro y
    rw [mem_unfold, inf_iSup_eq]
    apply iSup_le; intro j
    apply le_iSup_of_le ⟨y, j⟩
    -- goal: u.bval y ⊓ ((u.func y).bval j ⊓ x =ᴮ (u.func y).func j) ≤ bval⟨y,j⟩ ⊓ x =ᴮ func⟨y,j⟩
    change _ ≤ (⨆ z, u.bval z ⊓ (u.func y).func j ∈ᴮ u.func z) ⊓ x =ᴮ (u.func y).func j
    apply le_inf
    · apply le_iSup_of_le y
      apply le_inf inf_le_left
      exact le_trans (inf_le_right.trans inf_le_left) (mem_mk'' le_rfl)
    · exact inf_le_right.trans inf_le_right

-- src/bvm.lean:1888
lemma bv_union_spec' (u : bSet 𝔹) {Γ : 𝔹} : Γ ≤ ⨅ (x : bSet 𝔹),
    (x ∈ᴮ bv_union u ⟹ ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) ⊓
    ((⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) ⟹ x ∈ᴮ bv_union u) := by
  apply le_iInf; intro x
  have hspec := bv_union_spec u |>.trans (iInf_le _ x)
  -- derive boolean inequalities from hspec
  have h_fwd_raw : x ∈ᴮ bv_union u ≤ ⨆ i, u.bval i ⊓ x ∈ᴮ u.func i :=
    le_trans (le_inf (le_top.trans (hspec.trans inf_le_left)) le_rfl) bv_imp_elim
  have h_bwd_raw : (⨆ i, u.bval i ⊓ x ∈ᴮ u.func i) ≤ x ∈ᴮ bv_union u :=
    le_trans (le_inf (le_top.trans (hspec.trans inf_le_right)) le_rfl) bv_imp_elim
  rw [@bounded_exists _ _ u (fun z => x ∈ᴮ z) (h_congr := fun a b => subst_congr_mem_right)] at h_fwd_raw h_bwd_raw
  apply le_inf
  · exact le_top.trans (le_of_eq (imp_top_iff_le.mpr h_fwd_raw).symm)
  · exact le_top.trans (le_of_eq (imp_top_iff_le.mpr h_bwd_raw).symm)

lemma bv_union_spec_split (u : bSet 𝔹) {Γ : 𝔹} (x : bSet 𝔹) :
    (Γ ≤ x ∈ᴮ bv_union u) ↔ (Γ ≤ ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) := by
  have hspec := bv_union_spec' u (Γ := Γ) |>.trans (iInf_le _ x)
  constructor
  · intro H
    exact poset_yoneda_inv Γ bv_imp_elim (le_inf (hspec.trans inf_le_left) H)
  · intro H
    exact poset_yoneda_inv Γ bv_imp_elim (le_inf (hspec.trans inf_le_right) H)





lemma bv_union_congr {x y : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ x =ᴮ y) :
    Γ ≤ bv_union x =ᴮ bv_union y := by
  -- helper: Γ ⊓ (w ∈ a ⊓ z ∈ w) ≤ w ∈ b ⊓ z ∈ w given Γ ≤ a =ᴮ b
  have aux : ∀ (a b : bSet 𝔹) (H : Γ ≤ a =ᴮ b) (z w : bSet 𝔹),
      Γ ⊓ (w ∈ᴮ a ⊓ z ∈ᴮ w) ≤ w ∈ᴮ b ⊓ z ∈ᴮ w := fun a b H z w =>
    le_inf
      (le_trans (le_inf (inf_le_left.trans H) (inf_le_right.trans inf_le_left)) subst_congr_mem_right)
      (inf_le_right.trans inf_le_right)
  apply mem_ext
  · apply le_iInf; intro z
    rw [← deduction]
    -- Γ ⊓ z ∈ bv_union x ≤ z ∈ bv_union y
    have hx : z ∈ᴮ bv_union x = ⨆ w, w ∈ᴮ x ⊓ z ∈ᴮ w :=
      le_antisymm ((bv_union_spec_split x z (Γ := z ∈ᴮ bv_union x)).mp le_rfl)
                  ((bv_union_spec_split x z (Γ := ⨆ w, w ∈ᴮ x ⊓ z ∈ᴮ w)).mpr le_rfl)
    have hy : z ∈ᴮ bv_union y = ⨆ w, w ∈ᴮ y ⊓ z ∈ᴮ w :=
      le_antisymm ((bv_union_spec_split y z (Γ := z ∈ᴮ bv_union y)).mp le_rfl)
                  ((bv_union_spec_split y z (Γ := ⨆ w, w ∈ᴮ y ⊓ z ∈ᴮ w)).mpr le_rfl)
    rw [hx, hy, inf_iSup_eq]
    exact iSup_le fun w => le_iSup_of_le w (aux x y H_eq z w)
  · apply le_iInf; intro z
    rw [← deduction]
    have hx : z ∈ᴮ bv_union x = ⨆ w, w ∈ᴮ x ⊓ z ∈ᴮ w :=
      le_antisymm ((bv_union_spec_split x z (Γ := z ∈ᴮ bv_union x)).mp le_rfl)
                  ((bv_union_spec_split x z (Γ := ⨆ w, w ∈ᴮ x ⊓ z ∈ᴮ w)).mpr le_rfl)
    have hy : z ∈ᴮ bv_union y = ⨆ w, w ∈ᴮ y ⊓ z ∈ᴮ w :=
      le_antisymm ((bv_union_spec_split y z (Γ := z ∈ᴮ bv_union y)).mp le_rfl)
                  ((bv_union_spec_split y z (Γ := ⨆ w, w ∈ᴮ y ⊓ z ∈ᴮ w)).mpr le_rfl)
    rw [hy, hx, inf_iSup_eq]
    exact iSup_le fun w => le_iSup_of_le w
      (aux y x (H_eq.trans (le_of_eq bv_eq_symm)) z w)

@[simp] lemma B_congr_bv_union : B_congr (bv_union : bSet 𝔹 → bSet 𝔹) :=
  fun H => bv_union_congr H

-- src/bvm.lean:1971


-- src/bvm.lean:1978
@[simp] def set_of_indicator {u : bSet 𝔹} (f : u.type → 𝔹) : bSet 𝔹 :=
  ⟨u.type, u.func, f⟩

@[simp] lemma set_of_indicator_type {u : bSet 𝔹} {f : u.type → 𝔹} :
    (set_of_indicator f).type = u.type := rfl

@[simp] lemma set_of_indicator_func {u : bSet 𝔹} {f : u.type → 𝔹} {i : u.type} :
    (set_of_indicator f).func i = u.func i := rfl

@[simp] lemma set_of_indicator_bval {u : bSet 𝔹} {f : u.type → 𝔹} {i : u.type} :
    (set_of_indicator f).bval i = f i := rfl

-- src/bvm.lean:1993
def bv_powerset (u : bSet 𝔹) : bSet 𝔹 :=
  ⟨u.type → 𝔹,
   fun (f : u.type → 𝔹) => (⟨u.type, u.func, f⟩ : bSet 𝔹),
   fun (f : u.type → 𝔹) => (⟨u.type, u.func, f⟩ : bSet 𝔹) ⊆ᴮ u⟩

prefix:80 "𝒫" => bv_powerset

-- src/bvm.lean:2026 (bSet_axiom_of_powerset' -- stub for downstream usage)
-- TODO: The full statement uses ⨅ (y : x.type) which has elaboration issues in Lean 4.
-- Replacing with equivalent formulation via bv_powerset_spec.
-- lemma bSet_axiom_of_powerset' {Γ : 𝔹} (u : bSet 𝔹) : ... := by sorry

-- src/bvm.lean:2080
-- Auxiliary: bv_powerset unfolds membership
 lemma bv_powerset_mem_unfold {u x : bSet 𝔹} :
    x ∈ᴮ bv_powerset u =
    ⨆ f : u.type → 𝔹, (set_of_indicator (u := u) f ⊆ᴮ u) ⊓ x =ᴮ set_of_indicator (u := u) f := by
  rw [mem_unfold]
  rfl

lemma bv_powerset_spec {u x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ u ↔ Γ ≤ x ∈ᴮ (bv_powerset u) := by
  rw [bv_powerset_mem_unfold]
  constructor
  · -- Forward: x ⊆ u → x ∈ bv_powerset u
    intro H
    -- Choose f = fun j => u.func j ∈ᴮ x
    apply bv_use (fun j => u.func j ∈ᴮ x)
    apply le_inf
    · -- set_of_indicator (fun j => u.func j ∈ x) ⊆ᴮ u
      -- = ⨅ j : u.type, (u.func j ∈ x) ⟹ u.func j ∈ u
      rw [subset_unfold]
      simp only [set_of_indicator_bval, set_of_indicator_func]
      apply le_iInf; intro j; rw [← deduction]
      -- Need: Γ ⊓ u.func j ∈ x ≤ u.func j ∈ u
      -- From H : Γ ≤ x ⊆ u, take z = u.func j in subset_unfold'
      have hspec : Γ ≤ u.func j ∈ᴮ x ⟹ u.func j ∈ᴮ u :=
        le_trans H (by rw [subset_unfold']; exact iInf_le _ (u.func j))
      exact le_trans (le_inf (le_trans inf_le_left hspec) inf_le_right) bv_imp_elim
    · -- x =ᴮ set_of_indicator (fun j => u.func j ∈ x)
      apply mem_ext
      · -- ⨅ z, z ∈ x ⟹ z ∈ set_of_indicator (fun j => u.func j ∈ x)
        apply le_iInf; intro z; rw [← deduction]
        -- Γ ⊓ z ∈ x ≤ z ∈ set_of_indicator (fun j => u.func j ∈ x)
        -- Expand membership in set_of_indicator
        rw [mem_unfold (v := set_of_indicator (u := u) (fun j => u.func j ∈ᴮ x))]
        simp only [set_of_indicator_bval, set_of_indicator_func]
        -- Goal: Γ ⊓ z ∈ x ≤ ⨆ j : u.type, (u.func j ∈ x) ⊓ z =ᴮ u.func j
        -- From H: Γ ≤ x ⊆ u, so Γ ⊓ z ∈ x ≤ z ∈ u
        have hmem_u : Γ ⊓ z ∈ᴮ x ≤ z ∈ᴮ u := by
          have : Γ ≤ z ∈ᴮ x ⟹ z ∈ᴮ u :=
            le_trans H (by rw [subset_unfold']; exact iInf_le _ z)
          exact le_trans (le_inf (le_trans inf_le_left this) inf_le_right) bv_imp_elim
        -- (Γ ⊓ z ∈ x) ≤ (Γ ⊓ z ∈ x) ⊓ z ∈ u ≤ ⨆ j, (u.func j ∈ x) ⊓ z =ᴮ u.func j
        calc Γ ⊓ z ∈ᴮ x
            ≤ (Γ ⊓ z ∈ᴮ x) ⊓ (z ∈ᴮ u) := le_inf le_rfl hmem_u
          _ = (Γ ⊓ z ∈ᴮ x) ⊓ ⨆ j, u.bval j ⊓ z =ᴮ u.func j := by rw [← mem_unfold]
          _ = ⨆ j, (Γ ⊓ z ∈ᴮ x) ⊓ (u.bval j ⊓ z =ᴮ u.func j) := by
              rw [inf_iSup_eq]
          _ ≤ ⨆ j, (u.func j ∈ᴮ x) ⊓ z =ᴮ u.func j := by
              apply iSup_le; intro j; apply le_iSup_of_le j
              apply le_inf
              · -- (Γ ⊓ z ∈ x) ⊓ u.bval j ⊓ z =ᴮ u.func j ≤ u.func j ∈ x
                have : (Γ ⊓ z ∈ᴮ x) ⊓ (u.bval j ⊓ z =ᴮ u.func j) ≤
                       z ∈ᴮ x ⊓ z =ᴮ u.func j :=
                  le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
                exact le_trans this (by rw [inf_comm]; exact subst_congr_mem_left)
              · exact inf_le_right.trans inf_le_right
      · -- ⨅ z, z ∈ set_of_indicator (fun j => u.func j ∈ x) ⟹ z ∈ x
        -- bval j = u.func j ∈ x, func j = u.func j
        apply le_iInf; intro z; rw [← deduction]
        -- Γ ⊓ z ∈ set_of_indicator (...) ≤ z ∈ x
        -- z ∈ set_of_indicator (...) = ⨆ j, (u.func j ∈ x) ⊓ z =ᴮ u.func j
        rw [mem_unfold (v := set_of_indicator (u := u) (fun j => u.func j ∈ᴮ x))]
        simp only [set_of_indicator_bval, set_of_indicator_func]
        -- Goal: Γ ⊓ ⨆ j, (u.func j ∈ x) ⊓ z =ᴮ u.func j ≤ z ∈ x
        rw [inf_iSup_eq]
        apply iSup_le; intro j
        -- Γ ⊓ (u.func j ∈ x ⊓ z =ᴮ u.func j) ≤ z ∈ x
        calc Γ ⊓ (u.func j ∈ᴮ x ⊓ z =ᴮ u.func j)
            ≤ u.func j ∈ᴮ x ⊓ z =ᴮ u.func j := inf_le_right
          _ ≤ u.func j =ᴮ z ⊓ u.func j ∈ᴮ x :=
              le_inf (inf_le_right.trans (le_of_eq bv_eq_symm)) inf_le_left
          _ ≤ z ∈ᴮ x := subst_congr_mem_left
  · -- Backward: x ∈ bv_powerset u → x ⊆ u
    intro H
    apply le_trans H
    apply iSup_le; intro f
    -- (set_of_indicator f ⊆ u) ⊓ x =ᴮ set_of_indicator f ≤ x ⊆ u
    exact le_trans (le_inf inf_le_left inf_le_right) subst_congr_subset_left



-- src/bvm.lean:2074
-- Note: direct apply le_iInf fails for bSet-indexed iInf with ⇔ involving ⊆ᴮ
-- due to elaboration issue. We use an auxiliary lemma with an explicit u argument.




-- src/bvm.lean:2091
lemma bv_powerset_congr {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) :
    Γ ≤ bv_powerset x =ᴮ bv_powerset y := by
  apply mem_ext
  · -- ⨅ z, z ∈ bv_powerset x ⟹ z ∈ bv_powerset y
    apply le_iInf; intro z; rw [← deduction]
    -- Γ ⊓ z ∈ bv_powerset x ≤ z ∈ bv_powerset y
    -- Step 1: z ∈ bv_powerset x → z ⊆ x (via .mpr)
    have hz_sub_x : Γ ⊓ z ∈ᴮ bv_powerset x ≤ z ⊆ᴮ x :=
      le_trans inf_le_right (bv_powerset_spec.mpr le_rfl)
    -- Step 2: (z ⊆ x) ⊓ (x =ᴮ y) ≤ z ⊆ y
    have hz_sub_y : Γ ⊓ z ∈ᴮ bv_powerset x ≤ z ⊆ᴮ y :=
      le_trans (le_inf hz_sub_x (le_trans inf_le_left H)) subst_congr_subset_right
    -- Step 3: z ⊆ y → z ∈ bv_powerset y (via .mp)
    exact bv_powerset_spec.mp hz_sub_y
  · -- ⨅ z, z ∈ bv_powerset y ⟹ z ∈ bv_powerset x
    apply le_iInf; intro z; rw [← deduction]
    have hz_sub_y : Γ ⊓ z ∈ᴮ bv_powerset y ≤ z ⊆ᴮ y :=
      le_trans inf_le_right (bv_powerset_spec.mpr le_rfl)
    have Hy : Γ ≤ y =ᴮ x := le_trans H (le_of_eq bv_eq_symm)
    have hz_sub_x : Γ ⊓ z ∈ᴮ bv_powerset y ≤ z ⊆ᴮ x :=
      le_trans (le_inf hz_sub_y (le_trans inf_le_left Hy)) subst_congr_subset_right
    exact bv_powerset_spec.mp hz_sub_x

-- src/bvm.lean:2099
@[simp] lemma set_of_indicator_mem.mk {x : bSet 𝔹} {i : x.type} {χ : x.type → 𝔹} {Γ : 𝔹}
    (H_Γ : Γ ≤ χ i) : Γ ≤ x.func i ∈ᴮ set_of_indicator χ := by
  rw [mem_unfold]
  apply bv_use i
  exact le_inf H_Γ bv_refl

-- src/bvm.lean:2102
@[simp] lemma set_of_indicator_subset {x : bSet 𝔹} {χ : x.type → 𝔹} {Γ : 𝔹}
    (H_χ : ∀ i, χ i ≤ x.bval i) : Γ ≤ set_of_indicator χ ⊆ᴮ x := by
  rw [subset_unfold']
  apply le_iInf; intro z
  rw [← deduction]
  -- Γ ⊓ z ∈ᴮ set_of_indicator χ ≤ z ∈ᴮ x
  apply le_trans inf_le_right
  -- z ∈ᴮ set_of_indicator χ ≤ z ∈ᴮ x
  simp only [mem_unfold, set_of_indicator_bval, set_of_indicator_func]
  apply iSup_le; intro i
  apply le_iSup_of_le i
  exact inf_le_inf_right _ (H_χ i)

-- src/bvm.lean:2108
@[reducible, simp] def subset.mk {u : bSet 𝔹} (χ : u.type → 𝔹) : bSet 𝔹 :=
  set_of_indicator (fun i => χ i ⊓ u.bval i)

@[simp] lemma subset.mk_subset {u : bSet 𝔹} {χ : u.type → 𝔹} {Γ : 𝔹} :
    Γ ≤ subset.mk χ ⊆ᴮ u := by
  apply set_of_indicator_subset; intro i; simp



-- src/bvm.lean:2122
lemma mem_set_of_indicator_iff {x : bSet 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} {Γ : 𝔹}
    (H_χ : ∀ i, χ i ≤ x.bval i) :
    Γ ≤ z ∈ᴮ set_of_indicator χ ↔ Γ ≤ ⨆ (i : x.type), z =ᴮ x.func i ⊓ χ i := by
  -- z ∈ᴮ set_of_indicator χ = ⨆ i, χ i ⊓ z =ᴮ x.func i = ⨆ i, z =ᴮ x.func i ⊓ χ i
  rw [mem_unfold]
  simp only [set_of_indicator_bval, set_of_indicator_func]
  constructor <;> intro H <;> apply le_trans H <;> apply iSup_le <;> intro i <;>
    apply le_iSup_of_le i <;> simp [inf_comm]

-- src/bvm.lean:2132
lemma mem_subset.mk_iff {x : bSet 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ subset.mk χ ↔ Γ ≤ ⨆ (i : x.type), z =ᴮ x.func i ⊓ (χ i ⊓ x.bval i) :=
  mem_set_of_indicator_iff (by simp)

-- same as mem_subset.mk_iff, but with better ordering of terms on the RHS
-- src/bvm.lean:2137
lemma mem_subset.mk_iff₂ {x : bSet 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ subset.mk χ ↔ Γ ≤ ⨆ (i : x.type), x.bval i ⊓ (z =ᴮ x.func i ⊓ χ i) := by
  rw [mem_subset.mk_iff]
  -- reorder: z =ᴮ x.func i ⊓ (χ i ⊓ x.bval i) = x.bval i ⊓ (z =ᴮ x.func i ⊓ χ i)
  have heq : (⨆ i : x.type, z =ᴮ x.func i ⊓ (χ i ⊓ x.bval i)) =
             (⨆ i : x.type, x.bval i ⊓ (z =ᴮ x.func i ⊓ χ i)) :=
    iSup_congr fun i => by rw [← inf_assoc, inf_comm (z =ᴮ x.func i ⊓ χ i)]
  rw [heq]

@[simp] lemma mem_of_mem_subset.mk {x : bSet 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} {Γ : 𝔹}
    (Hz : Γ ≤ z ∈ᴮ subset.mk χ) : Γ ≤ z ∈ᴮ x :=
  mem_of_mem_subset subset.mk_subset Hz

-- src/bvm.lean:2147


-- src/bvm.lean:2163


-- src/bvm.lean:2169


-- src/bvm.lean:2184


-- src/bvm.lean:2191


-- src/bvm.lean:2199
section infinity
-- ω stands for PSet.omega throughout this section
 def ω' := PSet.omega

@[simp] lemma check_omega_type : (check ω' : bSet 𝔹).type = ULift ℕ := rfl
@[simp] lemma check_omega_func :
    (check ω' : bSet 𝔹).func = fun x => check (PSet.ofNat x.down) := rfl

-- src/bvm.lean:2207
@[simp, reducible] def axiom_of_infinity_spec (u : bSet 𝔹) : 𝔹 :=
  (∅ ∈ᴮ u) ⊓ (⨅ (i_x : u.type), ⨆ (i_y : u.type), u.func i_x ∈ᴮ u.func i_y)

@[reducible] def contains_empty (u : bSet 𝔹) : 𝔹 := ∅ ∈ᴮ u











-- src/bvm.lean:2234
@[reducible] def omega : bSet 𝔹 := check ω'

@[simp] lemma omega_type : (omega : bSet 𝔹).type = ULift ℕ := rfl

/-- The n-th von Neumann ordinal in bSet 𝔹 is the check-name of the n-th ordinal in PSet -/
@[reducible] def of_nat : ℕ → bSet 𝔹 := fun n => check (PSet.ofNat n)

@[simp] lemma omega_func {k : ULift ℕ} : (omega : bSet 𝔹).func k = of_nat k.down := rfl





instance has_zero_bSet : Zero (bSet 𝔹) := ⟨of_nat 0⟩
instance has_one_bSet : One (bSet 𝔹) := ⟨of_nat 1⟩

@[reducible] def two : bSet 𝔹 := of_nat 2
notation "𝟚" => bSet.two

-- src/bvm.lean:2261


-- Helper: PSet-level membership gives check-level membership
 lemma of_nat_mem_of_nat_succ (n : ℕ) : (of_nat n : bSet 𝔹) ∈ᴮ of_nat (n + 1) = ⊤ := by
  show check (PSet.ofNat n) ∈ᴮ check (PSet.ofNat (n + 1)) = (⊤ : 𝔹)
  have hmem := @PSet.ofNat_mem_of_lt n (n + 1) (Nat.lt_succ_self n)
  rcases hmem with ⟨i, hi⟩
  apply top_unique
  have h_eq : check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) = (⊤ : 𝔹) :=
    check_bv_eq_top_of_equiv hi
  have h_mem : (⊤ : 𝔹) ≤ check ((PSet.ofNat (n + 1)).Func i) ∈ᴮ check (PSet.ofNat (n + 1)) :=
    @mem_check_of_mem 𝔹 _ (PSet.ofNat (n + 1)) i (Γ := ⊤)
  calc ⊤
      = check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) ⊓
          check ((PSet.ofNat (n + 1)).Func i) ∈ᴮ check (PSet.ofNat (n + 1)) := by
            rw [h_eq, top_inf_eq, top_le_iff.mp h_mem]
    _ ≤ check (PSet.ofNat n) ∈ᴮ check (PSet.ofNat (n + 1)) := by
          rw [show check (PSet.ofNat n) =ᴮ check ((PSet.ofNat (n + 1)).Func i) =
              check ((PSet.ofNat (n + 1)).Func i) =ᴮ check (PSet.ofNat n) from bv_eq_symm]
          exact subst_congr_mem_left

@[simp] lemma zero_mem_one {Γ : 𝔹} : Γ ≤ (0 : bSet 𝔹) ∈ᴮ (1 : bSet 𝔹) := by
  apply le_trans le_top; rw [top_le_iff]
  exact of_nat_mem_of_nat_succ 0

-- src/bvm.lean:2270 (one_eq_singleton_zero) -- TODO: singleton notation for bSet
-- lemma one_eq_singleton_zero : Γ ≤ (1 : bSet 𝔹) =ᴮ {(0 : bSet 𝔹)} := by sorry



@[simp] lemma omega_bval {k : ULift ℕ} : (omega : bSet 𝔹).bval k = ⊤ := rfl

-- src/bvm.lean:2291


-- example {w : bSet 𝔹} : let ϕ := fun x => ⨅ z, z ∈ᴮ w ⊓ z ⊆ᴮ x ⊓ x ⊆ᴮ z; B_ext ϕ := by simp

end infinity

-- src/bvm.lean:2310




@[elab_as_elim] protected noncomputable def rec_on' {C : bSet 𝔹 → Sort*} (y : bSet 𝔹)
    (IH : ∀ (x : bSet 𝔹), (∀ (a : x.type), C (x.func a)) → C x) : C y := by
  induction y with
  | mk α A B ih => exact IH ⟨α, A, B⟩ ih

@[elab_as_elim] protected noncomputable def rec' {C : bSet 𝔹 → Sort*}
    (IH : ∀ (x : bSet 𝔹), (∀ (a : x.type), C (x.func a)) → C x) : ∀ (y : bSet 𝔹), C y :=
  fun y => bSet.rec_on' y IH

-- src/bvm.lean:2345
-- Auxiliary statement used in regularity_aux (with Γ = ⊤)
 lemma regularity_aux_top (x : bSet 𝔹) :
    (⊤ : 𝔹) ≤ ⨅ u, x ∈ᴮ u ⟹ (⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ)) := by
  induction x using bSet.rec' with
  | _ x IH =>
    -- IH a : ⊤ ≤ ⨅ u, x.func a ∈ u ⟹ ⨆ y, y ∈ u ⊓ ...
    -- Specialize IH: x.func a ∈ u' ≤ ⨆ y, y ∈ u' ⊓ ...
    have IH_spec : ∀ (a : x.type) (u' : bSet 𝔹),
        x.func a ∈ᴮ u' ≤ ⨆ y, y ∈ᴮ u' ⊓ (⨅ z', z' ∈ᴮ u' ⟹ (z' ∈ᴮ y)ᶜ) := fun a u' =>
      le_trans
        (le_inf (le_trans le_top (le_trans (IH a) (iInf_le _ u'))) le_rfl)
        bv_imp_elim
    apply le_iInf; intro u
    rw [← deduction, top_inf_eq]
    -- Goal: x ∈ u ≤ ⨆ y, y ∈ u ⊓ ⨅ z', z' ∈ u ⟹ (z' ∈ y)ᶜ
    -- Use bv_em on P = ⨅ z', z' ∈ u ⟹ (z' ∈ x)ᶜ
    set P := ⨅ (z' : bSet 𝔹), z' ∈ᴮ u ⟹ (z' ∈ᴮ x)ᶜ with hP_def
    -- x ∈ u ≤ (x ∈ u ⊓ P) ⊔ (x ∈ u ⊓ Pᶜ)
    calc x ∈ᴮ u
        = x ∈ᴮ u ⊓ (P ⊔ Pᶜ) := by rw [sup_compl_eq_top, inf_top_eq]
      _ = (x ∈ᴮ u ⊓ P) ⊔ (x ∈ᴮ u ⊓ Pᶜ) := inf_sup_left (a := x ∈ᴮ u) (b := P) (c := Pᶜ)
      _ ≤ ⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ) := by
          apply sup_le
          · -- Case A: x ∈ u ⊓ P ≤ ⨆ y, y ∈ u ⊓ ⨅ z', z' ∈ u ⟹ (z' ∈ y)ᶜ
            -- Use y = x: x ∈ u ⊓ P = x ∈ u ⊓ ⨅ z', z' ∈ u ⟹ (z' ∈ x)ᶜ
            apply le_iSup_of_le x
            exact le_inf inf_le_left inf_le_right
          · -- Case B: x ∈ u ⊓ Pᶜ ≤ ⨆ y, y ∈ u ⊓ ...
            -- Pᶜ = ⨆ z', z' ∈ u ⊓ z' ∈ x
            rw [show Pᶜ = ⨆ (z' : bSet 𝔹), z' ∈ᴮ u ⊓ z' ∈ᴮ x by
              simp only [hP_def, compl_iInf, neg_imp, compl_compl]]
            rw [inf_iSup_eq]
            -- x ∈ u ⊓ (z' ∈ u ⊓ z' ∈ x) ≤ ⨆ y, ...
            apply iSup_le; intro z'
            -- z' ∈ x = ⨆ a : x.type, x.bval a ⊓ z' =ᴮ x.func a
            rw [mem_unfold (v := x), inf_iSup_eq, inf_iSup_eq]
            apply iSup_le; intro a
            -- x ∈ u ⊓ (z' ∈ u ⊓ (x.bval a ⊓ z' =ᴮ x.func a)) ≤ ⨆ y, ...
            -- z' ∈ u ⊓ z' =ᴮ x.func a ≤ x.func a ∈ u by subst_congr_mem_left
            have h_mem : x ∈ᴮ u ⊓ (z' ∈ᴮ u ⊓ (x.bval a ⊓ z' =ᴮ x.func a)) ≤ x.func a ∈ᴮ u :=
              calc x ∈ᴮ u ⊓ (z' ∈ᴮ u ⊓ (x.bval a ⊓ z' =ᴮ x.func a))
                  ≤ z' ∈ᴮ u ⊓ z' =ᴮ x.func a :=
                    le_inf (inf_le_right.trans inf_le_left)
                           (inf_le_right.trans inf_le_right |>.trans inf_le_right)
                _ ≤ x.func a ∈ᴮ u := by rw [inf_comm]; exact subst_congr_mem_left
            exact le_trans h_mem (IH_spec a u)



theorem bSet_axiom_of_regularity (x : bSet 𝔹) {Γ : 𝔹} (H : Γ ≤ (x =ᴮ ∅)ᶜ) :
    Γ ≤ ⨆ y, y ∈ᴮ x ⊓ (⨅ z', z' ∈ᴮ x ⟹ (z' ∈ᴮ y)ᶜ) := by
  -- From H: Γ ≤ ⨆ u, u ∈ x (nonempty)
  have H_nonempty : Γ ≤ ⨆ u, u ∈ᴮ x := nonempty_iff_exists_mem.mp H
  -- For each u: u ∈ x ≤ ⨆ y, y ∈ x ⊓ ⨅ z', z' ∈ x ⟹ (z' ∈ y)ᶜ
  -- from regularity_aux_top u instantiated at x with bv_imp_elim
  have h_each : ∀ u : bSet 𝔹, u ∈ᴮ x ≤ ⨆ y, y ∈ᴮ x ⊓ (⨅ z', z' ∈ᴮ x ⟹ (z' ∈ᴮ y)ᶜ) := fun u =>
    le_trans
      (le_inf (le_trans le_top (le_trans (regularity_aux_top u) (iInf_le _ x))) le_rfl)
      bv_imp_elim
  exact le_trans H_nonempty (iSup_le h_each)



-- src/bvm.lean:2375
section zorns_lemma






 def zorn_chain_hyp (X : bSet 𝔹) : 𝔹 :=
  ⨅ y, (y ⊆ᴮ X ⊓ ⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
    w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁)) ⟹ bv_union y ∈ᴮ X





end zorns_lemma

-- src/bvm.lean:2487
section comprehension
variable (ϕ : bSet 𝔹 → 𝔹) (x : bSet 𝔹) (H_congr : B_ext ϕ)

@[reducible] def comprehend : bSet 𝔹 := subset.mk (fun i : x.type => ϕ (x.func i))







variable {ϕ} {H_congr}



variable (ϕ) (H_congr)



end comprehension

-- src/bvm.lean:2557










-- src/bvm.lean:2572






end bSet


end CohenSource_Bvm


