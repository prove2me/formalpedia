-- Prove2me | Definitions.Def_CH_Cohen_Library03
-- name    : CH_Cohen_Library03
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T01:48:03.904537+00:00
-- url     : https://prove2.me/theorems/79b5dc54-9f5a-4e8e-921e-7c12a0d312b7
-- title:
--   Boolean-valued set theory: BvmExtras
-- statement:
--   This module provides internal relation graphs, function predicates, ordinals, and cardinal comparisons. These objects form the language and model interfaces used in the forcing and completeness arguments.
--
--   **Formalization Note** The module retains the structural normalization facts needed by these definitions and their constructor proofs. The principal forcing and model-existence assertions are separate theorem nodes.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/BvmExtras.lean

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
import Definitions.Def_CH_Cohen_Library02
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

/- Source module: Definitions.Flypitch4.BvmExtras -/
section CohenSource_BvmExtras
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/bvm_extras.lean lines 1-700 — Task 14a -/



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch
open Lattice

universe u

namespace bSet

section extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Singleton instance for bSet so that `{x}` notation works -/
instance singleton_bSet : Singleton (bSet 𝔹) (bSet 𝔹) :=
  ⟨fun x => bSet.insert1 x ∅⟩

/-- Rewrite `{x}` to `bSet.insert1 x ∅` for membership -/
@[simp] lemma mem_singleton_bSet {x y : bSet 𝔹} :
    x ∈ᴮ ({y} : bSet 𝔹) = x =ᴮ y ⊔ x ∈ᴮ (∅ : bSet 𝔹) :=
  show x ∈ᴮ bSet.insert1 y ∅ = _ from mem_insert1

-- src/bvm_extras.lean:24
@[simp] lemma insert1_bval_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).bval none = ⊤ := rfl

-- src/bvm_extras.lean:27
@[simp] lemma insert1_bval_some {u v : bSet 𝔹} {i} :
    (bSet.insert1 u ({v})).bval (some i) = (bval ({v} : bSet 𝔹)) i := rfl

-- src/bvm_extras.lean:30
@[simp] lemma insert1_func_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).func none = u := rfl

-- src/bvm_extras.lean:33
@[simp] lemma insert1_func_some {u v : bSet 𝔹} {i} :
    (bSet.insert1 u ({v})).func (some i) = (func ({v} : bSet 𝔹)) i := rfl

-- src/bvm_extras.lean:36
@[simp] lemma mem_singleton {x : bSet 𝔹} : ⊤ ≤ x ∈ᴮ ({x} : bSet 𝔹) := by
  simp [mem_singleton_bSet, bv_eq_refl]

-- src/bvm_extras.lean:39
lemma eq_of_mem_singleton' {x y : bSet 𝔹} : y ∈ᴮ ({x} : bSet 𝔹) ≤ x =ᴮ y := by
  simp only [mem_singleton_bSet]
  exact sup_le (le_of_eq bv_eq_symm) (le_trans (bot_of_mem_empty le_rfl) bot_le)

-- src/bvm_extras.lean:42


-- src/bvm_extras.lean:45


-- src/bvm_extras.lean:48


-- src/bvm_extras.lean:56


-- src/bvm_extras.lean:62
lemma eq_inserted_of_eq_singleton {x y z : bSet 𝔹} :
    ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ x =ᴮ y := by
  -- From bv_eq_unfold, the second (⊆ LHS) component gives: at index none in insert1 y {z}:
  -- bval none = ⊤, func none = y → y ∈ {x}. And y ∈ {x} = y =ᴮ x, so x =ᴮ y.
  -- From the first (⊆ RHS) component at none in {x}: x ∈ insert1 y {z} = x =ᴮ y ⊔ x =ᴮ z.
  -- Combined: (x =ᴮ y ⊔ x =ᴮ z) ⊓ y =ᴮ x ≤ x =ᴮ y.
  -- bval none for insert1 u v is ⊤ by insert1_unfold
  -- func none for insert1 u v is u by insert1_unfold
  -- Extract: {x} =ᴮ insert1 y {z} ≤ y ∈ {x} (from RHS ⊆ LHS at index none)
  -- bv_eq_unfold gives ⨅ a : (bSet.insert1 y {z}).type, bval a ⟹ func a ∈ {x}
  -- (bSet.insert1 y {z}).type = Option ({z}).type = Option (Option PEmpty)
  -- At a = (none : Option (Option PEmpty)): bval none = ⊤, func none = y
  have hR : ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ y ∈ᴮ ({x} : bSet 𝔹) := by
    have h1 : ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤
        ⨅ (a : (bSet.insert1 y ({z} : bSet 𝔹)).type),
          (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
          (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹) := by
      rw [bv_eq_unfold]; exact inf_le_right
    have h2 : (⨅ (a : (bSet.insert1 y ({z} : bSet 𝔹)).type),
          (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
          (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹)) ≤
        y ∈ᴮ ({x} : bSet 𝔹) := by
      -- Specialize at none; definitionally .bval none = ⊤ and .func none = y
      have step := iInf_le (f := fun (a : (bSet.insert1 y ({z} : bSet 𝔹)).type) =>
        (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
        (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹)) (none)
      -- (bSet.insert1 y {z}).bval none = ⊤ and .func none = y by definition
      have hbval : (bSet.insert1 y ({z} : bSet 𝔹)).bval (none : (bSet.insert1 y ({z} : bSet 𝔹)).type) = ⊤ := rfl
      have hfunc : (bSet.insert1 y ({z} : bSet 𝔹)).func (none : (bSet.insert1 y ({z} : bSet 𝔹)).type) = y := rfl
      rw [hbval, hfunc, top_imp] at step
      exact step
    exact le_trans h1 h2
  -- y ∈ {x} = y =ᴮ x, so we get x =ᴮ y from symmetry
  have hmem_R : y ∈ᴮ ({x} : bSet 𝔹) = y =ᴮ x := by
    show y ∈ᴮ insert x (∅ : bSet 𝔹) = _
    rw [mem_insert1]
    have : y ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  rw [hmem_R] at hR
  -- hR: {x} =ᴮ insert1 y {z} ≤ y =ᴮ x
  exact hR.trans (le_of_eq bv_eq_symm)

-- src/bvm_extras.lean:69


-- src/bvm_extras.lean:78


-- src/bvm_extras.lean:81


-- src/bvm_extras.lean:84
def binary_inter (x y : bSet 𝔹) : bSet 𝔹 :=
  ⟨x.type, x.func, fun i => x.bval i ⊓ (x.func i) ∈ᴮ y⟩

scoped infix:81 " ∩ᴮ " => bSet.binary_inter

-- src/bvm_extras.lean:88
@[simp] lemma binary_inter_bval {x y : bSet 𝔹} {i : x.type} :
    (x ∩ᴮ y).bval i = x.bval i ⊓ (x.func i) ∈ᴮ y := rfl

-- src/bvm_extras.lean:90
@[simp] lemma binary_inter_type {x y : bSet 𝔹} : (x ∩ᴮ y).type = x.type := rfl

-- src/bvm_extras.lean:92
@[simp] lemma binary_inter_func {x y : bSet 𝔹} {i} : (x ∩ᴮ y).func i = x.func i := rfl

-- src/bvm_extras.lean:94


-- src/bvm_extras.lean:112


-- src/bvm_extras.lean:126


-- src/bvm_extras.lean:132


-- src/bvm_extras.lean:139


-- src/bvm_extras.lean:146


-- src/bvm_extras.lean:150


-- src/bvm_extras.lean:158


-- src/bvm_extras.lean:166


-- src/bvm_extras.lean:179
/-- The successor operation on sets (in particular von Neumann ordinals) -/
@[reducible] def succ (x : bSet 𝔹) := bSet.insert1 x x

-- src/bvm_extras.lean:182
@[simp] lemma subset_succ {x : bSet 𝔹} {Γ} : Γ ≤ x ⊆ᴮ (succ x) := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have : z ∈ᴮ x.insert1 x = z =ᴮ x ⊔ z ∈ᴮ x := mem_insert1
  rw [this]; exact le_trans inf_le_right le_sup_right

-- src/bvm_extras.lean:185


-- src/bvm_extras.lean:204


-- src/bvm_extras.lean:207
@[reducible] def pair (x y : bSet 𝔹) : bSet 𝔹 := ({{x}, {x, y}} : bSet 𝔹)

-- src/bvm_extras.lean:209
@[simp] lemma subst_congr_pair_left {x z y : bSet 𝔹} : x =ᴮ z ≤ pair x y =ᴮ pair z y := by
  unfold pair
  -- pair x y = insert1 {x} (insert1 {x,y} ∅), pair z y = insert1 {z} (insert1 {z,y} ∅)
  -- Change {x} to {z} in head, then {x,y} to {z,y} in tail
  exact bv_trans
    (subst_congr_insert1_left' (subst_congr_insert1_left (v := (∅ : bSet 𝔹))))
    (subst_congr_insert1_left'' subst_congr_insert1_left)

-- src/bvm_extras.lean:216
@[simp] lemma subst_congr_pair_left' {x z y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x =ᴮ z → Γ ≤ pair x y =ᴮ pair z y :=
  poset_yoneda_inv Γ subst_congr_pair_left

-- src/bvm_extras.lean:219
lemma subst_congr_pair_right {x y z : bSet 𝔹} : y =ᴮ z ≤ pair x y =ᴮ pair x z := by
  unfold pair
  -- pair x y = {{x},{x,y}}, pair x z = {{x},{x,z}}
  -- y =ᴮ z → {x,y} =ᴮ {x,z}: subst_congr_insert1_left'' le_refl
  -- y =ᴮ z → {{x},{x,y}} =ᴮ {{x},{x,z}}: apply again
  exact subst_congr_insert1_left'' (subst_congr_insert1_left'' (le_refl _))

-- src/bvm_extras.lean:222
lemma subst_congr_pair_right' {Γ} {x y z : bSet 𝔹} (H : Γ ≤ y =ᴮ z) :
    Γ ≤ pair x y =ᴮ pair x z :=
  poset_yoneda_inv Γ subst_congr_pair_right H

-- src/bvm_extras.lean:225
lemma pair_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ x₁ =ᴮ y₁) (H₂ : Γ ≤ x₂ =ᴮ y₂) :
    Γ ≤ pair x₁ x₂ =ᴮ pair y₁ y₂ :=
  bv_trans (subst_congr_pair_left' H₁) (subst_congr_pair_right' H₂)

-- src/bvm_extras.lean:240
@[simp] lemma B_congr_insert1_left {y : bSet 𝔹} : B_congr (fun x => bSet.insert1 x y) :=
  fun h => poset_yoneda_inv _ subst_congr_insert1_left h

-- src/bvm_extras.lean:243
@[simp] lemma B_congr_insert1_right {y : bSet 𝔹} : B_congr (fun x => bSet.insert1 y x) :=
  fun h => poset_yoneda_inv _ subst_congr_insert1_right h

-- src/bvm_extras.lean:246
@[simp] lemma B_congr_succ : B_congr (succ : bSet 𝔹 → bSet 𝔹) := by
  intro x y Γ h_eq; unfold succ
  exact bv_trans (B_congr_insert1_right h_eq) (B_congr_insert1_left h_eq)

-- src/bvm_extras.lean:257
@[simp] lemma B_congr_pair_left {y : bSet 𝔹} : B_congr (fun x => pair x y) :=
  fun h => poset_yoneda_inv _ subst_congr_pair_left h

-- src/bvm_extras.lean:260
@[simp] lemma B_congr_pair_right {y : bSet 𝔹} : B_congr (fun x => pair y x) :=
  fun h => poset_yoneda_inv _ subst_congr_pair_right h

-- src/bvm_extras.lean:263
@[simp] lemma B_ext_pair_left {ϕ : bSet 𝔹 → 𝔹} (H : B_ext ϕ) {x} :
    B_ext (fun z => ϕ (pair z x)) := B_ext_term ϕ (fun z => pair z x) H B_congr_pair_left

-- src/bvm_extras.lean:265
@[simp] lemma B_ext_pair_right {ϕ : bSet 𝔹 → 𝔹} (H : B_ext ϕ) {x} :
    B_ext (fun z => ϕ (pair x z)) := B_ext_term ϕ (fun z => pair x z) H B_congr_pair_right

-- src/bvm_extras.lean:270
@[simp] lemma B_ext_pair_mem_left {x y : bSet 𝔹} : B_ext (fun z => pair z x ∈ᴮ y) :=
  B_ext_term (fun w => w ∈ᴮ y) (fun z => pair z x) B_ext_mem_left B_congr_pair_left

-- src/bvm_extras.lean:273
@[simp] lemma B_ext_pair_mem_right {x y : bSet 𝔹} : B_ext (fun z => pair x z ∈ᴮ y) :=
  B_ext_term (fun w => w ∈ᴮ y) (fun z => pair x z) B_ext_mem_left B_congr_pair_right

-- src/bvm_extras.lean:276


-- src/bvm_extras.lean:287
lemma inserted_eq_of_insert_eq {y v w : bSet 𝔹} :
    ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ y =ᴮ w := by
  -- From bv_eq_unfold at 'some none' in {v,y} and {v,w}:
  -- Left: {v,y} =ᴮ {v,w} ≤ y ∈ {v,w} = y =ᴮ v ⊔ y =ᴮ w
  -- Right: {v,y} =ᴮ {v,w} ≤ w ∈ {v,y} = w =ᴮ v ⊔ w =ᴮ y
  -- Both cases: (y=v ∨ y=w) ∧ (w=v ∨ w=y) → y=w
  have hL : ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ y ∈ᴮ ({v, w} : bSet 𝔹) := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : ({v, y} : bSet 𝔹).type)
    -- Definitionally: bval (some none) = ⊤, func (some none) = y
    show (⊤ : 𝔹) ⟹ y ∈ᴮ ({v, w} : bSet 𝔹) ≤ y ∈ᴮ ({v, w} : bSet 𝔹)
    rw [top_imp]
  have hR : ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ w ∈ᴮ ({v, y} : bSet 𝔹) := by
    rw [bv_eq_unfold]
    apply inf_le_right.trans
    apply iInf_le_of_le (some none : ({v, w} : bSet 𝔹).type)
    show (⊤ : 𝔹) ⟹ w ∈ᴮ ({v, y} : bSet 𝔹) ≤ w ∈ᴮ ({v, y} : bSet 𝔹)
    rw [top_imp]
  -- y ∈ {v,w} = y =ᴮ v ⊔ y =ᴮ w
  have hmem_yw : y ∈ᴮ ({v, w} : bSet 𝔹) = y =ᴮ v ⊔ y =ᴮ w := by
    show y ∈ᴮ insert v ({w} : bSet 𝔹) = _
    rw [mem_insert1, mem_singleton_bSet]
    have : y ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  -- w ∈ {v,y} = w =ᴮ v ⊔ w =ᴮ y
  have hmem_wvy : w ∈ᴮ ({v, y} : bSet 𝔹) = w =ᴮ v ⊔ w =ᴮ y := by
    show w ∈ᴮ insert v ({y} : bSet 𝔹) = _
    rw [mem_insert1, mem_singleton_bSet]
    have : w ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  rw [hmem_yw] at hL; rw [hmem_wvy] at hR
  calc ({v, y} : bSet 𝔹) =ᴮ {v, w}
      ≤ (y =ᴮ v ⊔ y =ᴮ w) ⊓ (w =ᴮ v ⊔ w =ᴮ y) := le_inf hL hR
    _ ≤ y =ᴮ w := by
          -- (y=v ⊔ y=w) ⊓ (w=v ⊔ w=y) ≤ y=w
          -- Step 1: distribute via inf_sup_right: (y=v ⊓ (w=v⊔w=y)) ⊔ (y=w ⊓ (w=v⊔w=y)) ≤ y=w
          have step : (y =ᴮ v ⊔ y =ᴮ w) ⊓ (w =ᴮ v ⊔ w =ᴮ y)
              ≤ (y =ᴮ v ⊓ (w =ᴮ v ⊔ w =ᴮ y)) ⊔ (y =ᴮ w ⊓ (w =ᴮ v ⊔ w =ᴮ y)) :=
            le_of_eq (inf_sup_right _ _ _)
          apply le_trans step
          apply sup_le
          · -- y=v ⊓ (w=v ⊔ w=y) ≤ y=w
            have step2 : y =ᴮ v ⊓ (w =ᴮ v ⊔ w =ᴮ y)
                ≤ (y =ᴮ v ⊓ w =ᴮ v) ⊔ (y =ᴮ v ⊓ w =ᴮ y) :=
              le_of_eq (inf_sup_left _ _ _)
            apply le_trans step2
            apply sup_le
            · -- y=v ⊓ w=v ≤ y=w: y=v, w=v → w=y, then y=w
              rw [inf_comm]
              exact le_trans (inf_le_inf_left _ (le_of_eq bv_eq_symm))
                (le_trans bv_eq_trans (le_of_eq bv_eq_symm))
            · -- y=v ⊓ w=y ≤ y=w: w=y → y=w
              exact inf_le_right.trans (le_of_eq bv_eq_symm)
          · exact inf_le_left

-- src/bvm_extras.lean:297
lemma eq_of_eq_pair'_right {x z y : bSet 𝔹} : pair y x =ᴮ pair y z ≤ x =ᴮ z := by
  -- Approach: pair y x =ᴮ pair y z → {y,x} ∈ pair y z (from left bv_eq at some none)
  -- {y,x} ∈ pair y z = {y,x} =ᴮ {y} ⊔ {y,x} =ᴮ {y,z}
  -- Also pair y x =ᴮ pair y z → {y,z} ∈ pair y x (from right bv_eq at some none)
  -- {y,z} ∈ pair y x = {y,z} =ᴮ {y} ⊔ {y,z} =ᴮ {y,x}
  -- From {y,x}=ᴮ{y}: x=ᴮy (specialize at some none of {y,x})
  -- From {y,x}=ᴮ{y,z}: x=ᴮz (by inserted_eq_of_insert_eq)
  -- From {y,z}=ᴮ{y}: z=ᴮy
  -- From {y,z}=ᴮ{y,x}: z=ᴮx=bv_eq_symm→x=ᴮz (by inserted_eq_of_insert_eq)
  -- Helper: {v,u} =ᴮ {v} ≤ u =ᴮ v (from left bv_eq at some none)
  have pair_eq_sing_le : ∀ (u v : bSet 𝔹), (insert v ({u} : bSet 𝔹) : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ≤ u =ᴮ v := by
    intro u v
    -- From left bv_eq at 'some none': bval(some none) = ⊤, func(some none) = u
    -- So pair_eq_sing_le extracts u ∈ {v} which gives u=v by eq_of_mem_singleton'
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : (insert v ({u} : bSet 𝔹) : bSet 𝔹).type)
    -- Goal: {v,u}.bval(some none) ⟹ {v,u}.func(some none) ∈ {v} ≤ u =ᴮ v
    -- {v,u} = bSet.insert1 v {u}, so:
    -- .bval(some none) = ({u}).bval none = ⊤ by insert1_bval_some + singleton_bval_none
    -- .func(some none) = ({u}).func none = u by insert1_func_some + singleton_func
    -- {v,u}.bval(some none) = ⊤ and {v,u}.func(some none) = u: use insert1_bval_some/func_some
    -- but {v,u} = bSet.insert1 v {u} = insert v {u} so rw uses the same expression
    -- Use conv to rewrite inside the imp
    conv_lhs =>
      rw [show ({v, u} : bSet 𝔹).bval (some none : ({v, u} : bSet 𝔹).type) = ⊤ from by
        show (bSet.insert1 v ({u} : bSet 𝔹)).bval (some none) = ⊤
        rw [insert1_bval_some]; exact singleton_bval_none]
      rw [show ({v, u} : bSet 𝔹).func (some none : ({v, u} : bSet 𝔹).type) = u from by
        show (bSet.insert1 v ({u} : bSet 𝔹)).func (some none) = u
        rw [insert1_func_some]; rfl]
    rw [top_imp]
    exact le_trans eq_of_mem_singleton' (le_of_eq bv_eq_symm)
  -- Extract {y,x} ∈ pair y z and {y,z} ∈ pair y x
  have hL : pair y x =ᴮ pair y z ≤ ({y, x} : bSet 𝔹) ∈ᴮ pair y z := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : (pair y x).type)
    show (⊤ : 𝔹) ⟹ ({y, x} : bSet 𝔹) ∈ᴮ pair y z ≤ ({y, x} : bSet 𝔹) ∈ᴮ pair y z
    rw [top_imp]
  have hR : pair y x =ᴮ pair y z ≤ ({y, z} : bSet 𝔹) ∈ᴮ pair y x := by
    rw [bv_eq_unfold]
    apply inf_le_right.trans
    apply iInf_le_of_le (some none : (pair y z).type)
    show (⊤ : 𝔹) ⟹ ({y, z} : bSet 𝔹) ∈ᴮ pair y x ≤ ({y, z} : bSet 𝔹) ∈ᴮ pair y x
    rw [top_imp]
  -- Membership in pair y z: {y,x} ∈ pair y z = {y,x} =ᴮ {y} ⊔ {y,x} =ᴮ {y,z}
  have hmem_yz : ({y, x} : bSet 𝔹) ∈ᴮ pair y z = ({y, x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, x} : bSet 𝔹) =ᴮ ({y, z} : bSet 𝔹) := by
    show ({y, x} : bSet 𝔹) ∈ᴮ insert ({y} : bSet 𝔹) (insert ({y, z} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({y, x} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({y, x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, x} : bSet 𝔹) ∈ᴮ insert ({y, z} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  have hmem_yx : ({y, z} : bSet 𝔹) ∈ᴮ pair y x = ({y, z} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, z} : bSet 𝔹) =ᴮ ({y, x} : bSet 𝔹) := by
    show ({y, z} : bSet 𝔹) ∈ᴮ insert ({y} : bSet 𝔹) (insert ({y, x} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({y, z} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({y, z} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, z} : bSet 𝔹) ∈ᴮ insert ({y, x} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  rw [hmem_yz] at hL; rw [hmem_yx] at hR
  -- hL: Γ ≤ ({y,x}=ᴮ{y} ⊔ {y,x}=ᴮ{y,z})
  -- hR: Γ ≤ ({y,z}=ᴮ{y} ⊔ {y,z}=ᴮ{y,x})
  calc pair y x =ᴮ pair y z
      ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊔ ({y, x} : bSet 𝔹) =ᴮ {y, z}) ⊓
        (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x}) := le_inf hL hR
    _ ≤ x =ᴮ z := by
          -- (A₁⊔A₂) ⊓ (B₁⊔B₂) where A₁={y,x}={y}, A₂={y,x}={y,z}, B₁={y,z}={y}, B₂={y,z}={y,x}
          have step : (({y, x} : bSet 𝔹) =ᴮ {y} ⊔ ({y, x} : bSet 𝔹) =ᴮ {y, z}) ⊓
              (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})
              ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})) ⊔
                (({y, x} : bSet 𝔹) =ᴮ {y, z} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})) :=
            le_of_eq (inf_sup_right _ _ _)
          apply le_trans step
          apply sup_le
          · -- A₁ ⊓ (B₁⊔B₂): {y,x}=ᴮ{y} ⊓ (...)
            have step2 : ({y, x} : bSet 𝔹) =ᴮ {y} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})
                ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y}) ⊔
                  (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y, x}) :=
              le_of_eq (inf_sup_left _ _ _)
            apply le_trans step2
            apply sup_le
            · -- {y,x}=ᴮ{y} ⊓ {y,z}=ᴮ{y}: x=y, z=y → x=z
              have hxy := pair_eq_sing_le x y
              have hzy := pair_eq_sing_le z y
              calc ({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y}
                  ≤ x =ᴮ y ⊓ z =ᴮ y := le_inf (inf_le_left.trans hxy) (inf_le_right.trans hzy)
                _ ≤ x =ᴮ z := by
                    rw [inf_comm]
                    exact le_trans (inf_le_inf_left _ (le_of_eq bv_eq_symm))
                      (le_trans bv_eq_trans (le_of_eq bv_eq_symm))
            · -- {y,x}=ᴮ{y} ⊓ {y,z}=ᴮ{y,x}: z=x → x=z
              have hzx : ({y, z} : bSet 𝔹) =ᴮ {y, x} ≤ z =ᴮ x := inserted_eq_of_insert_eq
              exact inf_le_right.trans (hzx.trans (le_of_eq bv_eq_symm))
          · -- A₂ ⊓ (B₁⊔B₂): {y,x}=ᴮ{y,z} → x=z
            exact inf_le_left.trans inserted_eq_of_insert_eq

-- src/bvm_extras.lean:316
theorem eq_of_eq_pair_left {x y v w : bSet 𝔹} : pair x y =ᴮ pair v w ≤ x =ᴮ v := by
  -- Same as eq_of_eq_pair'_left: extract {x} ∈ pair v w from left bv_eq at none
  have hL : pair x y =ᴮ pair v w ≤ ({x} : bSet 𝔹) ∈ᴮ pair v w := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (none : (pair x y).type)
    show (⊤ : 𝔹) ⟹ ({x} : bSet 𝔹) ∈ᴮ pair v w ≤ ({x} : bSet 𝔹) ∈ᴮ pair v w
    rw [top_imp]
  have hmem : ({x} : bSet 𝔹) ∈ᴮ pair v w = ({x} : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) =ᴮ ({v, w} : bSet 𝔹) := by
    show ({x} : bSet 𝔹) ∈ᴮ insert ({v} : bSet 𝔹) (insert ({v, w} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({x} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({x} : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) ∈ᴮ insert ({v, w} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  rw [hmem] at hL
  exact hL.trans (sup_le (eq_of_eq_singleton le_rfl) eq_inserted_of_eq_singleton)

-- src/bvm_extras.lean:330
lemma eq_of_eq_pair_left' {x y v w : bSet 𝔹} {Γ} :
    Γ ≤ pair x y =ᴮ pair v w → Γ ≤ x =ᴮ v :=
  poset_yoneda_inv Γ eq_of_eq_pair_left

-- src/bvm_extras.lean:333
theorem eq_of_eq_pair_right {x y v w : bSet 𝔹} : pair x y =ᴮ pair v w ≤ y =ᴮ w := by
  -- From pair x y =ᴮ pair v w:
  -- 1. Get x =ᴮ v by eq_of_eq_pair_left
  -- 2. From x =ᴮ v, pair x y =ᴮ pair v y (by subst_congr_pair_left, symm)
  -- 3. pair v y =ᴮ pair v w from transitivity
  -- 4. Use eq_of_eq_pair'_right to get y =ᴮ w
  -- Step: pair x y =ᴮ pair v w ⊓ (pair x y =ᴮ pair v w) ≤ pair v y =ᴮ pair v w
  -- From pair x y =ᴮ pair v w, x =ᴮ v by eq_of_eq_pair_left.
  -- pair x y =ᴮ pair v y from x =ᴮ v (by subst_congr_pair_left with h:= bv_eq_symm).
  -- Then pair v y =ᴮ pair v w by bv_eq_trans of pair x y =ᴮ pair v y (symm) and pair x y =ᴮ pair v w.
  -- Then y =ᴮ w by eq_of_eq_pair'_right.
  calc pair x y =ᴮ pair v w
      ≤ pair v y =ᴮ pair v w := by
          -- From pair x y =ᴮ pair v w, get pair v y =ᴮ pair v w via:
          -- pair x y =ᴮ pair v y (from x =ᴮ v) and pair x y =ᴮ pair v w → pair v y =ᴮ pair v w
          -- pair v y =ᴮ pair v w = symm(pair x y =ᴮ pair v y) ⊓ (pair x y =ᴮ pair v w) → bv_eq_trans
          have hxv : pair x y =ᴮ pair v w ≤ x =ᴮ v := eq_of_eq_pair_left
          have hpair : pair x y =ᴮ pair v w ≤ pair x y =ᴮ pair v y := by
            -- x =ᴮ v → pair v y =ᴮ pair x y (by subst_congr_pair_left with args flipped)
            -- then pair v y =ᴮ pair x y ≤ pair x y =ᴮ pair v y (by bv_eq_symm)
            exact le_trans hxv (le_trans (le_of_eq bv_eq_symm)
              (le_trans subst_congr_pair_left (le_of_eq bv_eq_symm)))
          -- pair v y =ᴮ pair v w from: symm(pair x y =ᴮ pair v y) and (pair x y =ᴮ pair v w)
          apply le_trans (le_inf (le_trans hpair (le_of_eq bv_eq_symm)) le_rfl)
          exact bv_eq_trans
    _ ≤ y =ᴮ w := eq_of_eq_pair'_right

-- src/bvm_extras.lean:342
lemma eq_of_eq_pair_right' {x y v w : bSet 𝔹} {Γ} :
    Γ ≤ pair x y =ᴮ pair v w → Γ ≤ y =ᴮ w :=
  poset_yoneda_inv Γ eq_of_eq_pair_right

-- src/bvm_extras.lean:345
lemma eq_of_eq_pair {x y z w : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ pair x y =ᴮ pair z w) :
    Γ ≤ x =ᴮ z ∧ Γ ≤ y =ᴮ w :=
  ⟨eq_of_eq_pair_left' H_eq, eq_of_eq_pair_right' H_eq⟩

-- src/bvm_extras.lean:349
lemma pair_eq_pair_iff {x y x' y' : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y =ᴮ pair x' y' ↔ Γ ≤ x =ᴮ x' ∧ Γ ≤ y =ᴮ y' :=
  ⟨fun h => eq_of_eq_pair h, fun ⟨h₁, h₂⟩ => pair_congr h₁ h₂⟩

-- src/bvm_extras.lean:353
@[reducible] def prod (v w : bSet 𝔹) : bSet 𝔹 :=
  ⟨v.type × w.type, fun a => pair (v.func a.1) (w.func a.2), fun a => v.bval a.1 ⊓ w.bval a.2⟩

-- src/bvm_extras.lean:355
@[simp] lemma prod_type {v w : bSet 𝔹} : (prod v w).type = (v.type × w.type) := rfl

-- src/bvm_extras.lean:357
@[simp] lemma prod_func {v w : bSet 𝔹} {pr} :
    (prod v w).func pr = pair (v.func pr.1) (w.func pr.2) := rfl

-- src/bvm_extras.lean:360
@[simp] lemma prod_bval {v w : bSet 𝔹} {a b} :
    (prod v w).bval (a, b) = v.bval a ⊓ w.bval b := rfl

-- src/bvm_extras.lean:362
@[simp] lemma prod_type_forall {v w : bSet 𝔹} {ϕ : (prod v w).type → 𝔹} :
    (⨅ (z : (prod v w).type), ϕ z) = ⨅ (z : v.type × w.type), ϕ z := rfl

-- src/bvm_extras.lean:366
@[simp] lemma prod_check_bval {x y : PSet.{u}} {pr} :
    (prod (check x) (check y) : bSet 𝔹).bval pr = ⊤ := by
  cases pr; simp only [prod_bval, check_bval_top, top_inf_eq]

-- src/bvm_extras.lean:371
lemma prod_mem_old {v w x y : bSet 𝔹} :
    x ∈ᴮ v ⊓ y ∈ᴮ w ≤ pair x y ∈ᴮ prod v w := by
  -- From x ∈ v and y ∈ w, show pair x y ∈ prod v w
  -- prod v w has type v.type × w.type, func (i,j) = pair (v.func i) (w.func j), bval (i,j) = v.bval i ⊓ w.bval j
  rw [mem_unfold, mem_unfold, mem_unfold]
  -- (⨆ i, v.bval i ⊓ x =ᴮ v.func i) ⊓ (⨆ j, w.bval j ⊓ y =ᴮ w.func j)
  -- ≤ ⨆ p : v.type × w.type, (v.bval p.1 ⊓ w.bval p.2) ⊓ pair x y =ᴮ pair (v.func p.1) (w.func p.2)
  rw [iSup_inf_iSup]
  apply iSup_le; intro ⟨i, j⟩
  -- (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j) ≤ ...
  apply le_iSup_of_le (i, j)
  simp only [prod_bval, prod_func]
  -- Need: (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j)
  --   ≤ (v.bval i ⊓ w.bval j) ⊓ pair x y =ᴮ pair (v.func i) (w.func j)
  refine le_inf (le_inf ?_ ?_) ?_
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right.trans inf_le_left
  · -- pair x y =ᴮ pair (v.func i) (w.func j) from x =ᴮ v.func i and y =ᴮ w.func j
    have hx : (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j) ≤ x =ᴮ v.func i :=
      inf_le_left.trans inf_le_right
    have hy : (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j) ≤ y =ᴮ w.func j :=
      inf_le_right.trans inf_le_right
    exact pair_congr hx hy

-- src/bvm_extras.lean:389
lemma prod_mem {v w x y : bSet 𝔹} {Γ} : Γ ≤ x ∈ᴮ v → Γ ≤ y ∈ᴮ w → Γ ≤ pair x y ∈ᴮ prod v w :=
  fun H₁ H₂ => le_trans (le_inf H₁ H₂) prod_mem_old

-- src/bvm_extras.lean:392
lemma mem_left_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y ∈ᴮ prod v w → Γ ≤ x ∈ᴮ v := by
  intro H
  -- pair x y ∈ prod v w = ⨆ (i,j), bval(i,j) ⊓ pair x y =ᴮ func(i,j)
  rw [mem_unfold] at H
  -- H : Γ ≤ ⨆ p : (prod v w).type, (prod v w).bval p ⊓ pair x y =ᴮ (prod v w).func p
  -- = ⨆ (i,j), (v.bval i ⊓ w.bval j) ⊓ pair x y =ᴮ pair (v.func i) (w.func j)
  rw [mem_unfold]
  -- Need: Γ ≤ ⨆ i : v.type, v.bval i ⊓ x =ᴮ v.func i
  apply le_trans H
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le i
  simp only [prod_bval, prod_func]
  -- (v.bval i ⊓ w.bval j) ⊓ pair x y =ᴮ pair (v.func i) (w.func j) ≤ v.bval i ⊓ x =ᴮ v.func i
  refine le_inf (inf_le_left.trans inf_le_left) ?_
  -- pair x y =ᴮ pair (v.func i) (w.func j) ≤ x =ᴮ v.func i by eq_of_eq_pair_left
  exact inf_le_right.trans eq_of_eq_pair_left

-- src/bvm_extras.lean:400
lemma mem_right_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y ∈ᴮ prod v w → Γ ≤ y ∈ᴮ w := by
  intro H
  rw [mem_unfold] at H
  rw [mem_unfold]
  apply le_trans H
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le j
  simp only [prod_bval, prod_func]
  refine le_inf (inf_le_left.trans inf_le_right) ?_
  exact inf_le_right.trans eq_of_eq_pair_right

-- src/bvm_extras.lean:408
@[simp] lemma mem_prod_iff {v w x y : bSet 𝔹} {Γ} :
    Γ ≤ pair x y ∈ᴮ prod v w ↔ (Γ ≤ x ∈ᴮ v ∧ Γ ≤ y ∈ᴮ w) :=
  ⟨fun h => ⟨mem_left_of_prod_mem h, mem_right_of_prod_mem h⟩, fun ⟨h₁, h₂⟩ => prod_mem h₁ h₂⟩

-- src/bvm_extras.lean:411
@[simp] lemma mem_prod {v w x y : bSet 𝔹} {Γ} (H_mem₁ : Γ ≤ x ∈ᴮ v) (H_mem₂ : Γ ≤ y ∈ᴮ w) :
    Γ ≤ pair x y ∈ᴮ prod v w :=
  mem_prod_iff.mpr ⟨H_mem₁, H_mem₂⟩

-- src/bvm_extras.lean:415
@[simp] lemma B_congr_prod_left {y : bSet 𝔹} : B_congr (fun x => prod x y) := by
  intro a b Γ H_eq
  rw [bv_eq_unfold]
  simp only [prod_type, prod_bval, prod_func]
  -- Need two sides: prod a y ⊆ prod b y and prod b y ⊆ prod a y
  refine le_inf (le_iInf fun ⟨i, j⟩ => ?_) (le_iInf fun ⟨i, j⟩ => ?_)
  · -- (prod a y).bval (i,j) ⟹ pair (a.func i) (y.func j) ∈ prod b y
    rw [← deduction]
    -- Context: Γ ⊓ (a.bval i ⊓ y.bval j)
    have hai : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ a.func i ∈ᴮ a :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' a i))
    have hab : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ a.func i ∈ᴮ b :=
      bv_rw' (bv_symm (le_trans inf_le_left H_eq)) (ϕ := fun z => a.func i ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hai)
    have hyj : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ y.func j ∈ᴮ y :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' y j))
    exact prod_mem hab hyj
  · -- (prod b y).bval (i,j) ⟹ pair (b.func i) (y.func j) ∈ prod a y
    rw [← deduction]
    -- Context: Γ ⊓ (b.bval i ⊓ y.bval j)
    have hbi : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ b.func i ∈ᴮ b :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' b i))
    have hba : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ b.func i ∈ᴮ a :=
      bv_rw' (le_trans inf_le_left H_eq) (ϕ := fun z => b.func i ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hbi)
    have hyj : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ y.func j ∈ᴮ y :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' y j))
    exact prod_mem hba hyj

-- src/bvm_extras.lean:428
@[simp] lemma B_congr_prod_right {x : bSet 𝔹} : B_congr (fun y => prod x y) := by
  intro a b Γ H_eq
  rw [bv_eq_unfold]
  simp only [prod_type, prod_bval, prod_func]
  refine le_inf (le_iInf fun ⟨i, j⟩ => ?_) (le_iInf fun ⟨i, j⟩ => ?_)
  · -- (x.bval i ⊓ a.bval j) ⟹ pair (x.func i) (a.func j) ∈ prod x b
    rw [← deduction]
    have hxi : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ x.func i ∈ᴮ x :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' x i))
    have haj : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ a.func j ∈ᴮ a :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' a j))
    have hab : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ a.func j ∈ᴮ b :=
      bv_rw' (bv_symm (le_trans inf_le_left H_eq)) (ϕ := fun z => a.func j ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := haj)
    exact prod_mem hxi hab
  · -- (x.bval i ⊓ b.bval j) ⟹ pair (x.func i) (b.func j) ∈ prod x a
    rw [← deduction]
    have hxi : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ x.func i ∈ᴮ x :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' x i))
    have hbj : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ b.func j ∈ᴮ b :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' b j))
    have hba : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ b.func j ∈ᴮ a :=
      bv_rw' (le_trans inf_le_left H_eq) (ϕ := fun z => b.func j ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hbj)
    exact prod_mem hxi hba

-- src/bvm_extras.lean:441
lemma prod_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ} (H₁ : Γ ≤ x₁ =ᴮ x₂) (H₂ : Γ ≤ y₁ =ᴮ y₂) :
    Γ ≤ prod x₁ y₁ =ᴮ prod x₂ y₂ :=
  bv_trans (B_congr_prod_left H₁) (B_congr_prod_right H₂)

-- src/bvm_extras.lean:448
lemma mem_prod_iff₂ {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ∈ᴮ prod x y ↔
    ∃ v, ∃ _hv : Γ ≤ v ∈ᴮ x, ∃ w, ∃ _hw : Γ ≤ w ∈ᴮ y, Γ ≤ z =ᴮ pair v w := by
  constructor
  · intro H
    -- H : Γ ≤ z ∈ prod x y
    -- Convert to bSet-indexed iSup for classical extraction
    have H_iSup : Γ ≤ ⨆ v : bSet 𝔹, v ∈ᴮ x ⊓ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ z =ᴮ pair v w := by
      rw [mem_unfold] at H
      apply H.trans; apply iSup_le; intro ⟨i, j⟩
      simp only [prod_func, prod_bval]
      -- After simp: (x.bval i ⊓ y.bval j) ⊓ z =ᴮ pair (x.func i) (y.func j)
      apply le_iSup_of_le (x.func i)
      apply le_inf
      · -- x.func i ∈ x: from x.bval i (left-left component)
        exact (inf_le_left.trans inf_le_left).trans (mem_mk' x i)
      · apply le_iSup_of_le (y.func j)
        apply le_inf
        · -- y.func j ∈ y: from y.bval j (left-right component)
          exact (inf_le_left.trans inf_le_right).trans (mem_mk' y j)
        · -- z =ᴮ pair (x.func i) (y.func j): from right component
          exact inf_le_right
    -- Extract witnesses classically using B_ext_iSup
    -- B_ext for fun v => v ∈ x ⊓ ⨆ w, w ∈ y ⊓ z =ᴮ pair v w
    have B_outer : B_ext (fun v => v ∈ᴮ x ⊓ ⨆ w : bSet 𝔹, w ∈ᴮ y ⊓ z =ᴮ pair v w) :=
      B_ext_inf B_ext_mem_left (B_ext_iSup (h := fun w =>
        B_ext_inf B_ext_const
          (B_ext_term (fun p => z =ᴮ p) (fun v => pair v w)
            B_ext_bv_eq_right (fun {_ _ _} h => pair_congr h bv_refl))))
    -- B_ext for fun w => w ∈ y ⊓ z =ᴮ pair v w (for fixed v)
    have B_inner (v : bSet 𝔹) : B_ext (fun w => w ∈ᴮ y ⊓ z =ᴮ pair v w) :=
      B_ext_inf B_ext_mem_left
        (B_ext_term (fun p => z =ᴮ p) (fun w => pair v w)
          B_ext_bv_eq_right (fun {_ _ _} h => pair_congr bv_refl h))
    obtain ⟨v, Hv⟩ := exists_convert H_iSup B_outer
    obtain ⟨w, Hw⟩ := exists_convert (Hv.trans inf_le_right) (B_inner v)
    exact ⟨v, Hv.trans inf_le_left, w, Hw.trans inf_le_left, Hw.trans inf_le_right⟩
  · intro ⟨v, Hv, w, Hw, H_eq⟩
    -- z =ᴮ pair v w and pair v w ∈ prod x y → z ∈ prod x y
    exact subst_congr_mem_left' (bv_symm H_eq) (prod_mem Hv Hw)

-- src/bvm_extras.lean:465
lemma prod_ext {S₁ S₂ x y : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ S₁ ⊆ᴮ prod x y) (H₂ : Γ ≤ S₂ ⊆ᴮ prod x y)
    (H_prod_ext : Γ ≤ ⨅ v, v ∈ᴮ x ⟹ ⨅ w, w ∈ᴮ y ⟹ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂)) :
    Γ ≤ S₁ =ᴮ S₂ := by
  -- Use mem_ext: prove ⨅ z, z ∈ S₁ ⟹ z ∈ S₂ and vice versa
  apply mem_ext
  · -- ⨅ z, z ∈ S₁ ⟹ z ∈ S₂
    apply le_iInf; intro z; rw [← deduction]
    -- ctx₀ = Γ ⊓ z ∈ S₁
    have Hz_prod : Γ ⊓ z ∈ᴮ S₁ ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset (inf_le_left.trans H₁) inf_le_right
    obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp Hz_prod
    -- Use H_prod_ext to get the biconditional for (v, w)
    -- Specialize H_prod_ext at v and w using bv_specialize approach
    -- Use H_prod_ext to get the biconditional for (v, w) via tactic mode
    -- Use bv_specialize_left_twice to specialize ⨅ v, v ∈ x ⟹ ⨅ w, w ∈ y ⟹ φ at v and w
    have H_spec₁ : Γ ⊓ z ∈ᴮ S₁ ≤ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂) := by
      have h1 : Γ ⊓ z ∈ᴮ S₁ ≤ v ∈ᴮ x ⟹ ⨅ w' : bSet 𝔹, w' ∈ᴮ y ⟹
          (pair v w' ∈ᴮ S₁ ⇔ pair v w' ∈ᴮ S₂) :=
        (inf_le_left.trans H_prod_ext).trans (iInf_le _ v)
      have h2 : Γ ⊓ z ∈ᴮ S₁ ≤ ⨅ w' : bSet 𝔹, w' ∈ᴮ y ⟹
          (pair v w' ∈ᴮ S₁ ⇔ pair v w' ∈ᴮ S₂) :=
        le_trans (le_inf h1 Hv) bv_imp_elim
      have h3 : Γ ⊓ z ∈ᴮ S₁ ≤ w ∈ᴮ y ⟹ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂) :=
        h2.trans (iInf_le _ w)
      exact le_trans (le_inf h3 Hw) bv_imp_elim
    -- pair v w ∈ S₁ from z =ᴮ pair v w
    have Hvw_S₁ : Γ ⊓ z ∈ᴮ S₁ ≤ pair v w ∈ᴮ S₁ := subst_congr_mem_left' H_eq inf_le_right
    -- Get pair v w ∈ S₂ via forward direction of biconditional
    have Hvw_S₂ : Γ ⊓ z ∈ᴮ S₁ ≤ pair v w ∈ᴮ S₂ :=
      le_trans (le_inf (H_spec₁.trans inf_le_left) Hvw_S₁) bv_imp_elim
    exact subst_congr_mem_left' (bv_symm H_eq) Hvw_S₂
  · -- ⨅ z, z ∈ S₂ ⟹ z ∈ S₁
    apply le_iInf; intro z; rw [← deduction]
    have Hz_prod : Γ ⊓ z ∈ᴮ S₂ ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset (inf_le_left.trans H₂) inf_le_right
    obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp Hz_prod
    have H_spec₂ : Γ ⊓ z ∈ᴮ S₂ ≤ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂) := by
      have h1 : Γ ⊓ z ∈ᴮ S₂ ≤ v ∈ᴮ x ⟹ ⨅ w' : bSet 𝔹, w' ∈ᴮ y ⟹
          (pair v w' ∈ᴮ S₁ ⇔ pair v w' ∈ᴮ S₂) :=
        (inf_le_left.trans H_prod_ext).trans (iInf_le _ v)
      have h2 : Γ ⊓ z ∈ᴮ S₂ ≤ ⨅ w' : bSet 𝔹, w' ∈ᴮ y ⟹
          (pair v w' ∈ᴮ S₁ ⇔ pair v w' ∈ᴮ S₂) :=
        le_trans (le_inf h1 Hv) bv_imp_elim
      have h3 : Γ ⊓ z ∈ᴮ S₂ ≤ w ∈ᴮ y ⟹ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂) :=
        h2.trans (iInf_le _ w)
      exact le_trans (le_inf h3 Hw) bv_imp_elim
    have Hvw_S₂ : Γ ⊓ z ∈ᴮ S₂ ≤ pair v w ∈ᴮ S₂ := subst_congr_mem_left' H_eq inf_le_right
    have Hvw_S₁ : Γ ⊓ z ∈ᴮ S₂ ≤ pair v w ∈ᴮ S₁ :=
      le_trans (le_inf (H_spec₂.trans inf_le_right) Hvw_S₂) bv_imp_elim
    exact subst_congr_mem_left' (bv_symm H_eq) Hvw_S₁

-- src/bvm_extras.lean:489
@[simp] lemma check_singleton {x : PSet.{u}} {Γ : 𝔹} :
    Γ ≤ check ({x} : PSet) =ᴮ ({check x} : bSet 𝔹) := by
  have h : check ({x} : PSet) = ({check x} : bSet 𝔹) := by
    show check (PSet.insert x ∅) = bSet.insert1 (check x) ∅
    rw [check_insert]; simp [check_empty_eq_empty]
  rw [h]; exact bv_refl

-- src/bvm_extras.lean:494
@[simp] lemma check_unordered_pair {x y : PSet.{u}} {Γ} :
    Γ ≤ check ({x, y} : PSet) =ᴮ ({check x, check y} : bSet 𝔹) := by
  have h : check ({x, y} : PSet) = ({check x, check y} : bSet 𝔹) := by
    show check (PSet.insert x (PSet.insert y ∅)) = bSet.insert1 (check x) (bSet.insert1 (check y) ∅)
    rw [check_insert, check_insert]; simp [check_empty_eq_empty]
  rw [h]; exact bv_refl

-- src/bvm_extras.lean:499
@[simp] lemma eq_unordered_pair_of_eq {a b c d : bSet 𝔹} {Γ} (H₁ : Γ ≤ a =ᴮ c)
    (H₂ : Γ ≤ b =ᴮ d) : Γ ≤ ({a, b} : bSet 𝔹) =ᴮ {c, d} :=
  bv_trans (subst_congr_insert1_left' H₁) (subst_congr_insert1_left'' H₂)

-- src/bvm_extras.lean:506
-- (In Lean 4 port, PSet.pair is PSet.pSet_pair from PSetOrdinal.lean)


-- Auxiliary: propositional equality check (pSet_pair a b) = pair (check a) (check b)


-- src/bvm_extras.lean:514
-- (In Lean 4 port, PSet.prod is PSet.pSet_prod from PSetOrdinal.lean)


-- src/bvm_extras.lean:535
/-- f is =ᴮ-extensional if for every w₁ w₂ v₁ v₂, if pair (w₁ v₁) and pair (w₂ v₂) ∈ f and
    w₁ =ᴮ w₂, then v₁ =ᴮ v₂ -/
@[reducible] def is_func (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, ⨅ w₂, ⨅ v₁, ⨅ v₂, pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)

-- src/bvm_extras.lean:538
@[simp] lemma is_func_subset_of_is_func {f g : bSet 𝔹} {Γ} (H : Γ ≤ is_func f)
    (H_sub : Γ ≤ g ⊆ᴮ f) : Γ ≤ is_func g := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]
  -- Γ ⊓ (pair w₁ v₁ ∈ g ⊓ pair w₂ v₂ ∈ g) ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂
  have hspec : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤
      pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂) :=
    le_trans (le_trans inf_le_left H)
      (iInf_le _ w₁ |>.trans (iInf_le _ w₂) |>.trans (iInf_le _ v₁) |>.trans (iInf_le _ v₂))
  have hmem₁ : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤ pair w₁ v₁ ∈ᴮ f :=
    mem_of_mem_subset (le_trans inf_le_left H_sub) (inf_le_right.trans inf_le_left)
  have hmem₂ : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤ pair w₂ v₂ ∈ᴮ f :=
    mem_of_mem_subset (le_trans inf_le_left H_sub) (inf_le_right.trans inf_le_right)
  exact le_trans (le_inf hspec (le_inf hmem₁ hmem₂)) bv_imp_elim

-- src/bvm_extras.lean:548


-- src/bvm_extras.lean:551


-- src/bvm_extras.lean:561
@[reducible] def is_total (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, w₁ ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f

-- src/bvm_extras.lean:565
@[reducible] def is_total' (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ i, x.bval i ⟹ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ f

-- src/bvm_extras.lean:568


-- src/bvm_extras.lean:581
@[simp] lemma is_total_subset_of_is_total {S x y f : bSet 𝔹} {Γ}
    (H_is_total : Γ ≤ is_total x y f) (H_subset : Γ ≤ S ⊆ᴮ x) : Γ ≤ is_total S y f := by
  apply le_iInf; intro z; rw [← deduction]
  exact le_trans (le_inf
    (le_trans (le_trans inf_le_left H_is_total) (iInf_le _ z))
    (mem_of_mem_subset (inf_le_left.trans H_subset) inf_le_right)) bv_imp_elim

/-- f is (more precisely, contains) a function from x to y -/
-- src/bvm_extras.lean:585
@[reducible] def is_func' (x y f : bSet 𝔹) : 𝔹 :=
  is_func f ⊓ is_total x y f

-- src/bvm_extras.lean:588
@[simp] lemma is_func_of_is_func' {x y f : bSet 𝔹} {Γ} (H : Γ ≤ is_func' x y f) :
    Γ ≤ is_func f := le_trans H inf_le_left

-- src/bvm_extras.lean:591
lemma is_total_of_is_func' {x y f : bSet 𝔹} {Γ : 𝔹} (H_is_func' : Γ ≤ is_func' x y f) :
    Γ ≤ is_total x y f := le_trans H_is_func' inf_le_right

-- src/bvm_extras.lean:595


-- src/bvm_extras.lean:604
-- aka function extensionality
@[simp] lemma eq_of_is_func_of_eq {x y f x' y' : bSet 𝔹} {Γ : 𝔹} (H_is_func : Γ ≤ is_func f)
    (H_eq₁ : Γ ≤ x =ᴮ y) (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) :
    Γ ≤ x' =ᴮ y' := by
  -- is_func f = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)
  have hspec := le_trans H_is_func
    (iInf_le _ x |>.trans (iInf_le _ y) |>.trans (iInf_le _ x') |>.trans (iInf_le _ y'))
  -- hspec : Γ ≤ pair x x' ∈ f ⊓ pair y y' ∈ f ⟹ (x =ᴮ y ⟹ x' =ᴮ y')
  exact le_trans (le_inf (le_trans (le_inf hspec (le_inf H_mem₁ H_mem₂)) bv_imp_elim) H_eq₁) bv_imp_elim

-- src/bvm_extras.lean:610
-- aka function extensionality
@[simp] lemma eq_of_is_func'_of_eq {a b x y f x' y' : bSet 𝔹} {Γ : 𝔹}
    (H_is_func' : Γ ≤ is_func' a b f) (H_eq₁ : Γ ≤ x =ᴮ y)
    (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x' =ᴮ y' :=
  eq_of_is_func_of_eq (is_func_of_is_func' H_is_func') H_eq₁ H_mem₁ H_mem₂

-- src/bvm_extras.lean:614
@[simp] lemma is_func'_subset_of_is_func' {S x y f : bSet 𝔹} {Γ : 𝔹}
    (H_is_func : Γ ≤ is_func' x y f) (H_subset : Γ ≤ S ⊆ᴮ x) : Γ ≤ is_func' S y f :=
  le_inf (is_func_of_is_func' H_is_func)
         (is_total_subset_of_is_total (is_total_of_is_func' H_is_func) H_subset)

-- src/bvm_extras.lean:622
-- bounded image
def image (x y f : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun j : y.type => ⨆ z, z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f)

-- src/bvm_extras.lean:625
@[simp] lemma image_subset {x y f : bSet 𝔹} {Γ} : Γ ≤ image x y f ⊆ᴮ y :=
  subset.mk_subset

-- src/bvm_extras.lean:628
@[simp] lemma mem_image {x y a b f : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pair a b ∈ᴮ f) (H_mem'' : Γ ≤ a ∈ᴮ x) (H_mem' : Γ ≤ b ∈ᴮ y) :
    Γ ≤ b ∈ᴮ image x y f := by
  -- image x y f = subset.mk (fun j : y.type => ⨆ z, z ∈ x ⊓ pair z (y.func j) ∈ f)
  unfold image
  rw [mem_subset.mk_iff]
  -- Need: Γ ≤ ⨆ i, b =ᴮ y.func i ⊓ ((⨆ z, z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ y.bval i)
  -- Extract index i from b ∈ y, augmenting with Γ to access H_mem and H_mem''
  rw [mem_unfold] at H_mem'
  calc Γ ≤ (⨆ i, y.bval i ⊓ b =ᴮ y.func i) ⊓ Γ := le_inf H_mem' le_rfl
    _ ≤ ⨆ i, (y.bval i ⊓ b =ᴮ y.func i) ⊓ Γ := (iSup_inf_eq _ _).le
    _ ≤ ⨆ i, b =ᴮ y.func i ⊓ ((⨆ z, z ∈ᴮ x ⊓ pair z (y.func i) ∈ᴮ f) ⊓ y.bval i) := by
          apply iSup_le; intro i
          apply le_iSup_of_le i
          -- Context: (y.bval i ⊓ b =ᴮ y.func i) ⊓ Γ
          refine le_inf (inf_le_left.trans inf_le_right) (le_inf ?_ (inf_le_left.trans inf_le_left))
          -- Need: ... ≤ ⨆ z, z ∈ x ⊓ pair z (y.func i) ∈ f
          apply le_iSup_of_le a
          -- Need: ... ≤ a ∈ x ⊓ pair a (y.func i) ∈ f
          refine le_inf (inf_le_right.trans H_mem'') ?_
          -- pair a (y.func i) ∈ f from pair a b ∈ f and b =ᴮ y.func i
          -- bv_rw' with H : y.func i =ᴮ b, H_new : pair a b ∈ f → pair a (y.func i) ∈ f
          exact bv_rw' (bv_symm (inf_le_left.trans inf_le_right)) (ϕ := fun z => pair a z ∈ᴮ f)
            (h_congr := B_ext_pair_mem_right) (H_new := inf_le_right.trans H_mem)

-- src/bvm_extras.lean:638
lemma mem_image_iff {x y b f : bSet 𝔹} {Γ} :
    Γ ≤ b ∈ᴮ image x y f ↔ (Γ ≤ b ∈ᴮ y) ∧ Γ ≤ ⨆ z, z ∈ᴮ x ⊓ pair z b ∈ᴮ f := by
  constructor
  · intro H
    refine ⟨mem_of_mem_subset image_subset H, ?_⟩
    unfold image at H; rw [mem_subset.mk_iff] at H
    -- H: Γ ≤ ⨆ i, b =ᴮ y.func i ⊓ ((⨆ z, z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ y.bval i)
    apply H.trans
    apply iSup_le; intro i
    -- Context: b =ᴮ y.func i ⊓ ((⨆ z, z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ y.bval i)
    set A := b =ᴮ y.func i
    set Chi := ⨆ z, z ∈ᴮ x ⊓ pair z (y.func i) ∈ᴮ f
    -- hbeq : A ⊓ (Chi ⊓ y.bval i) ≤ A
    -- hChi : A ⊓ (Chi ⊓ y.bval i) ≤ Chi
    have hbeq : A ⊓ (Chi ⊓ y.bval i) ≤ A := inf_le_left
    have hChi : A ⊓ (Chi ⊓ y.bval i) ≤ Chi :=
      inf_le_right.trans inf_le_left
    -- Show Chi ⊓ A ≤ ⨆ z, z ∈ x ⊓ pair z b ∈ f
    apply le_trans (le_inf hChi hbeq)
    rw [iSup_inf_eq]
    apply iSup_le; intro z
    apply le_iSup_of_le z
    -- Context: (z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ A  where A = b =ᴮ y.func i
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    -- Context: (z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ (b =ᴮ y.func i)
    -- H_beq : _ ≤ b =ᴮ y.func i (from inf_le_right)
    -- H_mem : _ ≤ pair z (y.func i) ∈ f (from inf_le_left.trans inf_le_right)
    -- bv_rw' with b =ᴮ y.func i, ϕ = fun w => pair z w ∈ f,
    --   H_new = pair z (y.func i) ∈ f → pair z b ∈ f
    exact bv_rw' (H := inf_le_right) (ϕ := fun w => pair z w ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right) (H_new := inf_le_left.trans inf_le_right)
  · intro ⟨H_mem_y, H_ex⟩
    obtain ⟨a, Ha⟩ := exists_convert H_ex (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image (Ha.trans inf_le_right) (Ha.trans inf_le_left) H_mem_y
-- src/bvm_extras.lean:649
@[simp] lemma B_congr_image_left {y f : bSet 𝔹} : B_congr (fun x => image x y f) := by
  intro x₁ x₂ Γ H_eq
  apply mem_ext
  · -- fwd: image x₁ y f ⊆ image x₂ y f
    apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x₁ y f ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x₁ y f ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x₁ y f ≤ ⨆ w, w ∈ᴮ x₁ ⊓ pair w z ∈ᴮ f :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := bv_symm (hΓ.trans H_eq)) (ϕ := fun x => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)) (H_new := hmem.2)⟩
  · -- bwd: image x₂ y f ⊆ image x₁ y f
    apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x₂ y f ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x₂ y f ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x₂ y f ≤ ⨆ w, w ∈ᴮ x₂ ⊓ pair w z ∈ᴮ f :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := hΓ.trans H_eq) (ϕ := fun x => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)) (H_new := hmem.2)⟩

-- src/bvm_extras.lean:658
@[simp] lemma B_congr_image_right {x y : bSet 𝔹} : B_congr (fun f => image x y f) := by
  intro f₁ f₂ Γ H_eq
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x y f₁ ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x y f₁ ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x y f₁ ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f₁ :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := bv_symm (hΓ.trans H_eq)) (ϕ := fun f => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)) (H_new := hmem.2)⟩
  · apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x y f₂ ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x y f₂ ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x y f₂ ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f₂ :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := hΓ.trans H_eq) (ϕ := fun f => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)) (H_new := hmem.2)⟩

-- src/bvm_extras.lean:668
-- bounded preimage
def preimage (x y f : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun i : x.type => ⨆ b, b ∈ᴮ y ⊓ pair (x.func i) b ∈ᴮ f)

-- src/bvm_extras.lean:671
@[simp] lemma preimage_subset {x y f} {Γ : 𝔹} : Γ ≤ preimage x y f ⊆ᴮ x :=
  subset.mk_subset

-- src/bvm_extras.lean:673
@[simp] lemma mem_preimage {x y a b f : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pair a b ∈ᴮ f) (H_mem'' : Γ ≤ a ∈ᴮ x) (H_mem' : Γ ≤ b ∈ᴮ y) :
    Γ ≤ a ∈ᴮ preimage x y f := by
  unfold preimage; rw [mem_subset.mk_iff]
  rw [mem_unfold] at H_mem''
  -- H_mem'' : Γ ≤ ⨆ i, x.bval i ⊓ a =ᴮ x.func i
  -- Goal: Γ ≤ ⨆ i, a =ᴮ x.func i ⊓ ((⨆ b', b' ∈ y ⊓ pair (x.func i) b' ∈ f) ⊓ x.bval i)
  calc Γ ≤ (⨆ i, x.bval i ⊓ a =ᴮ x.func i) ⊓ Γ := le_inf H_mem'' le_rfl
    _ ≤ ⨆ i, (x.bval i ⊓ a =ᴮ x.func i) ⊓ Γ := (iSup_inf_eq _ _).le
    _ ≤ ⨆ i, a =ᴮ x.func i ⊓ ((⨆ b', b' ∈ᴮ y ⊓ pair (x.func i) b' ∈ᴮ f) ⊓ x.bval i) := by
          apply iSup_le; intro i
          apply le_iSup_of_le i
          set A := a =ᴮ x.func i
          -- Context: (x.bval i ⊓ A) ⊓ Γ
          refine le_inf (inf_le_left.trans inf_le_right) (le_inf ?_ (inf_le_left.trans inf_le_left))
          -- Need: _ ≤ ⨆ b', b' ∈ y ⊓ pair (x.func i) b' ∈ f
          apply le_iSup_of_le b
          refine le_inf (inf_le_right.trans H_mem') ?_
          -- pair (x.func i) b ∈ f from pair a b ∈ f and a =ᴮ x.func i
          -- bv_rw' with x.func i =ᴮ a, ϕ = fun w => pair w b ∈ f, H_new = pair a b ∈ f
          exact bv_rw' (bv_symm (inf_le_left.trans inf_le_right)) (ϕ := fun w => pair w b ∈ᴮ f)
            (h_congr := B_ext_pair_mem_left) (H_new := inf_le_right.trans H_mem)

/-- f is a function x → y if it is extensional, total, and is a subset of the product of x and y -/
-- src/bvm_extras.lean:684
@[reducible] def is_function (x y f : bSet 𝔹) : 𝔹 :=
  is_func' x y f ⊓ (f ⊆ᴮ prod x y)

-- src/bvm_extras.lean:687
@[simp] lemma B_ext_is_function_left {y f : bSet 𝔹} : B_ext (fun x => is_function x y f) :=
  -- is_function x y f = (is_func f ⊓ is_total x y f) ⊓ f ⊆ prod x y
  -- is_total x y f = ⨅ w₁, w₁ ∈ x ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
  -- f ⊆ prod x y = ⨅ j, f.bval j ⟹ f.func j ∈ prod x y
  B_ext_inf
    (B_ext_inf B_ext_const
      (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
    (B_ext_term (ϕ := fun v => f ⊆ᴮ v) (t := fun x => prod x y)
      (H := B_ext_subset_right) (H' := B_congr_prod_left))

-- src/bvm_extras.lean:690
@[simp] lemma B_ext_is_function_right {x y : bSet 𝔹} : B_ext (fun f => is_function x y f) :=
  -- is_function x y f = (is_func f ⊓ is_total x y f) ⊓ f ⊆ prod x y
  -- is_func f = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)
  -- is_total x y f = ⨅ w₁, w₁ ∈ x ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
  -- f ⊆ prod x y = ⨅ j, f.bval j ⟹ f.func j ∈ prod x y (but this uses f's own structure)
  -- B_ext_subset_left : B_ext (fun x => x ⊆ prod x y) (uses x both in domain and range)
  -- Actually need: B_ext (fun f => f ⊆ prod x y)
  -- f ⊆ prod x y as function of f
  B_ext_inf
    (B_ext_inf
      -- is_func f as function of f: ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⟹ ...
      -- B_ext (fun f => pair w₁ v₁ ∈ f) = B_ext_mem_right (x := pair w₁ v₁)
      (B_ext_iInf (h := fun w₁ => B_ext_iInf (h := fun w₂ => B_ext_iInf (h := fun v₁ => B_ext_iInf (h := fun v₂ =>
        B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_mem_right)
          (h₂ := B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_const)))))))
      -- is_total x y f as function of f: ⨅ w₁, w₁ ∈ x ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
      -- B_ext (fun f => pair w₁ w₂ ∈ f) = B_ext_mem_right
      (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
        (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))))
    (B_ext_subset_left (y := prod x y))

-- src/bvm_extras.lean:692


-- src/bvm_extras.lean:694


-- src/bvm_extras.lean:697


-- src/bvm_extras.lean:699


-- ============================================================
-- Task 14b: src/bvm_extras.lean lines 700-1300
-- ============================================================

-- src/bvm_extras.lean:702


-- src/bvm_extras.lean:709


-- src/bvm_extras.lean:716


-- src/bvm_extras.lean:727


-- src/bvm_extras.lean:740


-- src/bvm_extras.lean:757
-- Helper: membership in check f as iSup over indices




-- src/bvm_extras.lean:797


-- src/bvm_extras.lean:800


-- src/bvm_extras.lean:804


-- src/bvm_extras.lean:807
@[reducible] def is_inj (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, ⨅ w₂, ⨅ v₁, ⨅ v₂,
    (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂) ⟹ w₁ =ᴮ w₂

-- src/bvm_extras.lean:810
@[reducible] def is_injective_function (x y f : bSet 𝔹) : 𝔹 :=
  is_function x y f ⊓ is_inj f

-- src/bvm_extras.lean:812


-- src/bvm_extras.lean:814


-- src/bvm_extras.lean:821
@[simp] lemma B_ext_is_injective_function_left {y f : bSet 𝔹} :
    B_ext (fun x => is_injective_function x y f) :=
  -- is_injective_function x y f = is_function x y f ⊓ is_inj f
  B_ext_inf B_ext_is_function_left B_ext_const

-- src/bvm_extras.lean:824


-- src/bvm_extras.lean:828


-- src/bvm_extras.lean:868
@[simp] lemma eq_of_is_inj_of_eq {x y x' y' f : bSet 𝔹} {Γ : 𝔹}
    (H_is_inj : Γ ≤ is_inj f) (H_eq : Γ ≤ x' =ᴮ y')
    (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x =ᴮ y := by
  have hspec := le_trans H_is_inj
    (iInf_le _ x |>.trans (iInf_le _ y) |>.trans (iInf_le _ x') |>.trans (iInf_le _ y'))
  -- hspec : Γ ≤ pair x x' ∈ f ⊓ pair y y' ∈ f ⊓ x' =ᴮ y' ⟹ x =ᴮ y
  -- bv_imp_elim : (A ⟹ B) ⊓ A ≤ B
  exact le_trans (le_inf hspec (le_inf (le_inf H_mem₁ H_mem₂) H_eq)) bv_imp_elim

-- src/bvm_extras.lean:879
-- not really funext since it doesn't use extensionality in an essential way


-- src/bvm_extras.lean:891
/-- A relation f is surjective if for every w ∈ y there is a v ∈ x such that (v,w) ∈ f. -/
@[reducible] def is_surj (x y : bSet 𝔹) (f : bSet 𝔹) : 𝔹 :=
  ⨅ v, v ∈ᴮ y ⟹ (⨆ w, w ∈ᴮ x ⊓ pair w v ∈ᴮ f)

/-- x is larger than y if there is a subset S ⊆ X which surjects onto y. -/
-- src/bvm_extras.lean:895
def larger_than (x y : bSet 𝔹) : 𝔹 :=
  ⨆ S, ⨆ f, S ⊆ᴮ x ⊓ (is_func' S y f) ⊓ (is_surj S y f)

-- src/bvm_extras.lean:897


-- src/bvm_extras.lean:900


-- src/bvm_extras.lean:913


-- src/bvm_extras.lean:921


-- src/bvm_extras.lean:931


-- src/bvm_extras.lean:938


-- src/bvm_extras.lean:946
@[simp] lemma larger_than_domain_subset {Γ : 𝔹} {x y S : bSet 𝔹}
    (HS : Γ ≤ ⨆ f, S ⊆ᴮ x ⊓ (is_func' S y f) ⊓ (is_surj S y f)) : Γ ≤ S ⊆ᴮ x := by
  exact le_trans HS (iSup_le (fun f => le_trans (le_trans inf_le_left inf_le_left) (le_refl _)))

-- src/bvm_extras.lean:950
def injects_into (x y : bSet 𝔹) : 𝔹 := ⨆ f, (is_func' x y f) ⊓ is_inj f

-- src/bvm_extras.lean:952


-- src/bvm_extras.lean:954


-- src/bvm_extras.lean:963


-- src/bvm_extras.lean:969


-- src/bvm_extras.lean:972


-- src/bvm_extras.lean:981
@[reducible] def is_surj_onto (x y f : bSet 𝔹) : 𝔹 := (is_func' x y f) ⊓ (is_surj x y f)

-- src/bvm_extras.lean:983
def surjects_onto (x y : bSet 𝔹) : 𝔹 := ⨆ f, is_surj_onto x y f

-- src/bvm_extras.lean:985
-- larger_than y z = ⨆ S f, S ⊆ y ⊓ is_func' S z f ⊓ is_surj S z f
-- B_ext as function of z:
-- is_total S z f = ⨅ w₁, w₁ ∈ S ⟹ ⨆ w₂, w₂ ∈ z ⊓ pair w₁ w₂ ∈ f
-- is_surj S z f = ⨅ v, v ∈ z ⟹ ⨆ w, w ∈ S ⊓ pair w v ∈ f
 def B_ext_is_total_right (S f : bSet 𝔹) : B_ext (fun z => is_total S z f) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)))

 def B_ext_is_surj_codomain (S f : bSet 𝔹) : B_ext (fun z => is_surj S z f) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))

@[simp] lemma B_ext_larger_than_right {y : bSet 𝔹} : B_ext (fun z => larger_than y z) :=
  B_ext_iSup (h := fun S => B_ext_iSup (h := fun f =>
    B_ext_inf (B_ext_inf B_ext_const
      (B_ext_inf B_ext_const (B_ext_is_total_right S f)))
    (B_ext_is_surj_codomain S f)))

-- src/bvm_extras.lean:988
-- larger_than z y = ⨆ S f, S ⊆ z ⊓ is_func' S y f ⊓ is_surj S y f
-- B_ext as function of z: S ⊆ z = ⨅ j, S.bval j ⟹ S.func j ∈ z
@[simp] lemma B_ext_larger_than_left {y : bSet 𝔹} : B_ext (fun z => larger_than z y) :=
  -- larger_than z y = ⨆ S f, S ⊆ z ⊓ is_func' S y f ⊓ is_surj S y f
  -- B_ext (fun z => S ⊆ z) = B_ext_subset_right
  B_ext_iSup (h := fun S => B_ext_iSup (h := fun f =>
    B_ext_inf (B_ext_inf B_ext_subset_right B_ext_const) B_ext_const))

-- src/bvm_extras.lean:991
-- injects_into z y = ⨆ f, is_func' z y f ⊓ is_inj f
-- is_func' z y f = is_func f ⊓ is_total z y f
-- is_total z y f = ⨅ w₁, w₁ ∈ z ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
-- B_ext as function of z: w₁ ∈ z changes with z
@[simp] lemma B_ext_injects_into_left {y : bSet 𝔹} : B_ext (fun z => injects_into z y) :=
  B_ext_iSup (h := fun f =>
    B_ext_inf
      (B_ext_inf B_ext_const
        (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
      B_ext_const)

-- src/bvm_extras.lean:994
-- injects_into y z = ⨆ f, is_func' y z f ⊓ is_inj f
-- B_ext as function of z (in codomain y→z)
@[simp] lemma B_ext_injects_into_right {y : bSet 𝔹} : B_ext (fun z => injects_into y z) :=
  B_ext_iSup (h := fun f =>
    B_ext_inf
      (B_ext_inf B_ext_const (B_ext_is_total_right y f))
      B_ext_const)

-- ============================================================
-- src/bvm_extras.lean lines 1004-1300
-- ============================================================

-- src/bvm_extras.lean:1018
-- The pointed_extension construction: extends a partial surjection f : S ↠ y
-- to a total surjection x ↠ y by mapping elements outside S to b.
-- This definition uses subset.mk over (prod x y).type, with bval encoding
-- the condition.
def pointed_extension {x y : bSet 𝔹} {Γ : 𝔹} {S f : bSet 𝔹}
    (b : bSet 𝔹) (_H_b : Γ ≤ b ∈ᴮ y) (_H_S : Γ ≤ S ⊆ᴮ x)
    (_H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x y).type =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ (y.func pr.2) =ᴮ b))

-- src/bvm_extras.lean:1023
@[simp] lemma pointed_extension_func {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    {H_b : Γ ≤ b ∈ᴮ y} {H_S : Γ ≤ S ⊆ᴮ x} {H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f}
    {pr : (prod x y).type} :
    (pointed_extension b H_b H_S H_surj).func pr = pair (x.func pr.1) (y.func pr.2) := rfl

-- src/bvm_extras.lean:1072-1215: All lemmas about pointed_extension
-- These are sorry-stubbed since they require heavy tactic work.

-- src/bvm_extras.lean:1136


-- src/bvm_extras.lean:1177


-- src/bvm_extras.lean:1191


-- src/bvm_extras.lean:1198


-- src/bvm_extras.lean:1209


-- src/bvm_extras.lean:1220


-- src/bvm_extras.lean:1230


-- src/bvm_extras.lean:1238


-- src/bvm_extras.lean:1273


-- src/bvm_extras.lean:1291


-- ============================================================
-- src/bvm_extras.lean lines 1300-1900
-- ============================================================

-- src/bvm_extras.lean:1301
-- Given a surjection f : x ↠ z and an injection g : y ↪ z, lift f along g to a surjection f' : x ↠ y.
def lift_surj_inj {x z f g : bSet 𝔹} (y : bSet 𝔹) {Γ : 𝔹}
    (_H_surj : Γ ≤ is_surj x z f) (_H_inj : Γ ≤ is_inj g) : bSet 𝔹 :=
  @subset.mk _ _ (prod x y)
    (fun p => ⨆ w, w ∈ᴮ z ⊓ (pair (x.func p.1) w) ∈ᴮ f ⊓
                           (pair (y.func p.2) w ∈ᴮ g))

-- src/bvm_extras.lean:1306


-- src/bvm_extras.lean:1318


-- src/bvm_extras.lean:1346


-- src/bvm_extras.lean:1362


-- src/bvm_extras.lean:1375


-- src/bvm_extras.lean:1404


-- src/bvm_extras.lean:1410


-- src/bvm_extras.lean:1422


-- src/bvm_extras.lean:1445


-- src/bvm_extras.lean:1457


-- src/bvm_extras.lean:1472


-- src/bvm_extras.lean:1486
-- (locally: ≺ means (larger_than x y)ᶜ, ≼ means injects_into x y)


-- src/bvm_extras.lean:1500


-- ============================================================
-- src/bvm_extras.lean:1513-1604: is_func'_comp section
-- ============================================================

-- src/bvm_extras.lean:1518


-- src/bvm_extras.lean:1521


-- src/bvm_extras.lean:1554


-- src/bvm_extras.lean:1565


-- src/bvm_extras.lean:1576


-- src/bvm_extras.lean:1583


-- src/bvm_extras.lean:1594


-- src/bvm_extras.lean:1606


-- src/bvm_extras.lean:1609


-- src/bvm_extras.lean:1616


-- src/bvm_extras.lean:1619


-- src/bvm_extras.lean:1625


-- src/bvm_extras.lean:1628


-- src/bvm_extras.lean:1636


-- src/bvm_extras.lean:1639


-- src/bvm_extras.lean:1653


-- src/bvm_extras.lean:1692


-- src/bvm_extras.lean:1700
def functions (x y : bSet 𝔹) : bSet 𝔹 :=
  set_of_indicator (fun s : (bv_powerset (prod x y) : bSet 𝔹).type =>
    is_function x y ((bv_powerset (prod x y)).func s))

-- src/bvm_extras.lean:1703
@[simp] lemma functions_func {x y : bSet 𝔹} {i} :
    (functions x y).func i = (bv_powerset (prod x y)).func i := rfl

-- src/bvm_extras.lean:1705
@[simp] lemma functions_bval {x y : bSet 𝔹} {i} :
    (functions x y).bval i = is_function x y ((bv_powerset (prod x y)).func i) := rfl

-- src/bvm_extras.lean:1707
@[simp] lemma functions_type {x y : bSet 𝔹} :
    (functions x y).type = (bv_powerset (prod x y)).type := rfl

-- src/bvm_extras.lean:1709


-- ============================================================
-- src/bvm_extras.lean:1732-1798: function_mk' section
-- ============================================================

-- src/bvm_extras.lean:1740


-- src/bvm_extras.lean:1757


-- src/bvm_extras.lean:1767


-- src/bvm_extras.lean:1774


-- src/bvm_extras.lean:1780


-- src/bvm_extras.lean:1788


-- ============================================================
-- src/bvm_extras.lean:1800-1888: inj_inverse section
-- ============================================================

-- src/bvm_extras.lean:1806


-- src/bvm_extras.lean:1809


-- src/bvm_extras.lean:1841


-- src/bvm_extras.lean:1850


-- src/bvm_extras.lean:1858


-- src/bvm_extras.lean:1865


-- src/bvm_extras.lean:1875


-- src/bvm_extras.lean:1877


-- src/bvm_extras.lean:1880


-- ============================================================
-- src/bvm_extras.lean:1890-1900: injective_function_inverse section
-- ============================================================

section injective_function_inverse_section
variable {Γ : 𝔹}

-- src/bvm_extras.lean:1892


-- src/bvm_extras.lean:1895


-- src/bvm_extras.lean:1898


end injective_function_inverse_section

-- ============================================================
-- src/bvm_extras.lean:1902-1927: function_eval section
-- ============================================================

-- Helper: get existential from is_total


-- src/bvm_extras.lean:1906


-- src/bvm_extras.lean:1914


-- src/bvm_extras.lean:1921


-- src/bvm_extras.lean:1924


-- ============================================================
-- src/bvm_extras.lean:1930: surjects_onto_of_injects_into
-- ============================================================

-- src/bvm_extras.lean:1930


-- ============================================================
-- src/bvm_extras.lean:1956-1989: functionMk (= function.mk) and check''
-- ============================================================

-- src/bvm_extras.lean:1956: function.mk renamed to functionMk
-- (functionMk' already exists; this is a different construction called function.mk in Lean 3)
def functionMk {u : bSet 𝔹} (F : u.type → bSet 𝔹)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : bSet 𝔹 :=
  ⟨u.type, fun a => pair (u.func a) (F a), u.bval⟩

@[simp] lemma functionMk_type {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} :
    (functionMk F h_congr).type = u.type := rfl

@[simp] lemma functionMk_func {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} :
    (functionMk F h_congr).func i = pair (u.func i) (F i) := rfl

@[simp] lemma functionMk_bval {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} :
    (functionMk F h_congr).bval i = u.bval i := rfl

@[simp] lemma functionMk_self {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i : u.type} :
    u.bval i ≤ pair (u.func i) (F i) ∈ᴮ functionMk F h_congr := by
  simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]
  exact le_iSup_of_le i (le_inf le_rfl bv_refl)

-- src/bvm_extras.lean:1972: check' named check'' to avoid collision
def check'' {α : Type u} (A : α → bSet 𝔹) : bSet 𝔹 := ⟨α, A, fun _ => ⊤⟩

@[simp] lemma check''_type {α : Type u} {A : α → bSet 𝔹} : (check'' A).type = α := rfl
@[simp] lemma check''_bval {α : Type u} {A : α → bSet 𝔹} {i} : (check'' A).bval i = ⊤ := rfl
@[simp] lemma check''_func {α : Type u} {A : α → bSet 𝔹} {i} : (check'' A).func i = A i := rfl

-- src/bvm_extras.lean:1978


-- src/bvm_extras.lean:2041


-- ============================================================
-- src/bvm_extras.lean:2080-2136: bot_of_mem_self, bot_of_mem_mem
-- ============================================================

-- src/bvm_extras.lean:2080


-- src/bvm_extras.lean:2093


-- src/bvm_extras.lean:2099


-- src/bvm_extras.lean:2110


-- src/bvm_extras.lean:2131


end extras

-- ============================================================
-- src/bvm_extras.lean:2140-2218: section check (inside bSet namespace)
-- ============================================================

section bSet_check_extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2154


-- src/bvm_extras.lean:2193


-- src/bvm_extras.lean:2203
@[simp] lemma check_mem'' {y : PSet} {i : y.Type} :
    ((check (y.Func i) : bSet 𝔹)) ∈ᴮ (check y) = (⊤ : 𝔹) := by
  apply top_unique; simp

-- src/bvm_extras.lean:2206


-- src/bvm_extras.lean:2209


-- src/bvm_extras.lean:2215
@[simp] lemma zero_eq_some_none' {Γ : 𝔹} :
    Γ ≤ (0 : bSet 𝔹) =ᴮ (𝟚 : bSet 𝔹).func (some none) :=
  bv_refl

end bSet_check_extras

-- ============================================================
-- src/bvm_extras.lean:2220-2396: section powerset (inside bSet namespace)
-- ============================================================

section powerset_section
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
variable (x : bSet 𝔹)

-- src/bvm_extras.lean:2228
-- powerset_injects_F: maps (bv_powerset x).type → (functions x 𝟚).type
-- encodes χ ↦ characteristic function as subset of x × 𝟚


-- src/bvm_extras.lean:2231


-- Helper: under context Γ, if H_ba : χ_b ⊆ χ_a, then compl_a ⊆ compl_b (pointwise under Γ)


-- src/bvm_extras.lean:2249


-- src/bvm_extras.lean:2301


-- src/bvm_extras.lean:2318


-- src/bvm_extras.lean:2377


-- src/bvm_extras.lean:2387


-- src/bvm_extras.lean:2389


end powerset_section

-- ============================================================
-- src/bvm_extras.lean:2212: check_succ_eq_succ_check (needed by omega_is_omega)
-- ============================================================

-- src/bvm_extras.lean:2212


-- ============================================================
-- src/bvm_extras.lean:2398-2747: section ordinals
-- ============================================================

section ordinals
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2401
@[reducible] def epsilon_trichotomy (x : bSet 𝔹) : 𝔹 :=
  ⨅ y, y ∈ᴮ x ⟹ (⨅ z, z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))

-- src/bvm_extras.lean:2403
@[reducible] def epsilon_well_founded (x : bSet 𝔹) : 𝔹 :=
  ⨅ u, u ⊆ᴮ x ⟹ ((u =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ))

-- src/bvm_extras.lean:2405
def epsilon_well_orders (x : bSet 𝔹) : 𝔹 :=
  epsilon_trichotomy x ⊓ epsilon_well_founded x

-- src/bvm_extras.lean:2408


-- src/bvm_extras.lean:2410
@[simp] lemma B_ext_ewo : B_ext (fun w : bSet 𝔹 => epsilon_well_orders w) := by
  unfold epsilon_well_orders epsilon_trichotomy epsilon_well_founded
  apply B_ext_inf
  · -- epsilon_trichotomy: ⨅ y, y ∈ w ⟹ ⨅ z, z ∈ w ⟹ (y =ᴮ z ⊔ y ∈ z ⊔ z ∈ y)
    exact B_ext_iInf (h := fun y => B_ext_imp (h₁ := B_ext_mem_right) (h₂ :=
      B_ext_iInf (h := fun z => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
  · -- epsilon_well_founded: ⨅ u, u ⊆ w ⟹ (...)
    exact B_ext_iInf (h := fun u => B_ext_imp (h₁ := B_ext_subset_right) (h₂ := B_ext_const))

-- src/bvm_extras.lean:2413


-- src/bvm_extras.lean:2420
def is_transitive (x : bSet 𝔹) : 𝔹 := ⨅ y, y ∈ᴮ x ⟹ y ⊆ᴮ x

-- src/bvm_extras.lean:2422


-- src/bvm_extras.lean:2425
@[simp] lemma B_ext_is_transitive : B_ext (is_transitive : bSet 𝔹 → 𝔹) := by
  unfold is_transitive
  exact B_ext_iInf (h := fun y => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_subset_right))

-- src/bvm_extras.lean:2428
def Ord (x : bSet 𝔹) : 𝔹 := epsilon_well_orders x ⊓ is_transitive x

-- src/bvm_extras.lean:2430


-- src/bvm_extras.lean:2438

-- src/bvm_extras.lean:2475


-- src/bvm_extras.lean:2478


-- src/bvm_extras.lean:2481


-- src/bvm_extras.lean:2484


-- src/bvm_extras.lean:2486


-- src/bvm_extras.lean:2520


-- src/bvm_extras.lean:2551


-- src/bvm_extras.lean:2638
lemma check_is_transitive {x : PSet} (H : PSet.is_transitive x) {Γ : 𝔹} :
    Γ ≤ is_transitive (check x : bSet 𝔹) := by
  -- is_transitive (check x) = ⨅ y, y ∈ check x ⟹ y ⊆ check x
  apply le_iInf; intro y; rw [← deduction]
  -- Goal: Γ ⊓ y ∈ check x ≤ y ⊆ check x
  -- Extract the iSup from y ∈ check x
  -- y ∈ check x = ⨆ i : x.Type, y =ᴮ check (x.Func i) (after simp on bval=⊤)
  have h_ymem : Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ≤
      ⨆ i : x.Type, y =ᴮ check (x.Func i) := by
    calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)
        ≤ y ∈ᴮ (check x : bSet 𝔹) := inf_le_right
      _ = y ∈ᴮ bSet.mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by rw [check_unfold]
      _ = ⨆ i : x.Type, ⊤ ⊓ y =ᴮ check (x.Func i) := mem_unfold
      _ = ⨆ i : x.Type, y =ᴮ check (x.Func i) := by simp only [top_inf_eq]
  -- Carry context through iSup
  calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)
      ≤ (⨆ i : x.Type, y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)) :=
        le_inf h_ymem le_rfl
    _ ≤ ⨆ i : x.Type, (y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹)) :=
        (iSup_inf_eq _ _).le
    _ ≤ y ⊆ᴮ (check x : bSet 𝔹) := by
        apply iSup_le; intro i
        -- Context: (y =ᴮ check (x.Func i)) ⊓ ctx ≤ y ⊆ check x
        -- Use bv_rw' with y =ᴮ check (x.Func i) and check (x.Func i) ⊆ check x
        apply bv_rw' (H := inf_le_left) (ϕ := fun z => z ⊆ᴮ check x)
          (h_congr := B_ext_subset_left)
        -- Goal: ... ≤ check (x.Func i) ⊆ check x
        exact check_subset (H (x.Func i) (PSet.func_mem x i))

-- src/bvm_extras.lean:2647
lemma check_ewo_left {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ (⨅ y, y ∈ᴮ (check x : bSet 𝔹) ⟹
      (⨅ z, z ∈ᴮ (check x : bSet 𝔹) ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) := by
  apply le_iInf; intro y; rw [← deduction]
  apply le_iInf; intro z; rw [← deduction]
  -- Goal: Γ ⊓ y ∈ check x ⊓ z ∈ check x ≤ y =ᴮ z ⊔ y ∈ z ⊔ z ∈ y
  -- Unfold memberships
  have hy : Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹) ≤
      ⨆ i : x.Type, y =ᴮ check (x.Func i) :=
    calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)
        ≤ y ∈ᴮ (check x : bSet 𝔹) := inf_le_left.trans inf_le_right
      _ = y ∈ᴮ bSet.mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by rw [check_unfold]
      _ = ⨆ i : x.Type, ⊤ ⊓ y =ᴮ check (x.Func i) := mem_unfold
      _ = ⨆ i : x.Type, y =ᴮ check (x.Func i) := by simp only [top_inf_eq]
  have hz : Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹) ≤
      ⨆ j : x.Type, z =ᴮ check (x.Func j) :=
    calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)
        ≤ z ∈ᴮ (check x : bSet 𝔹) := inf_le_right
      _ = z ∈ᴮ bSet.mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by rw [check_unfold]
      _ = ⨆ j : x.Type, ⊤ ⊓ z =ᴮ check (x.Func j) := mem_unfold
      _ = ⨆ j : x.Type, z =ᴮ check (x.Func j) := by simp only [top_inf_eq]
  -- Double iSup distribution
  calc Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)
      ≤ (⨆ i, y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)) :=
        le_inf hy le_rfl
    _ ≤ ⨆ i, (y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)) :=
        (iSup_inf_eq _ _).le
    _ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y := by
        apply iSup_le; intro i
        -- Context: (y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ check x ⊓ z ∈ check x)
        -- Use hz to get ⨆ j, z =ᴮ check (x.Func j), then apply it
        calc (y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹))
            ≤ (⨆ j, z =ᴮ check (x.Func j)) ⊓
                ((y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹))) :=
              le_inf (inf_le_right.trans hz) le_rfl
          _ ≤ ⨆ j, (z =ᴮ check (x.Func j)) ⊓
                ((y =ᴮ check (x.Func i)) ⊓ (Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹))) :=
              (iSup_inf_eq _ _).le
          _ ≤ y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y := by
              apply iSup_le; intro j
              -- Context: (z =ᴮ check (x.Func j)) ⊓ ((y =ᴮ check (x.Func i)) ⊓ ctx)
              have h_tri := H.1 (x.Func i) (PSet.func_mem x i) (x.Func j) (PSet.func_mem x j)
              set ctx3 := Γ ⊓ y ∈ᴮ (check x : bSet 𝔹) ⊓ z ∈ᴮ (check x : bSet 𝔹)
              have hy_eq : (z =ᴮ check (x.Func j)) ⊓ ((y =ᴮ check (x.Func i)) ⊓ ctx3) ≤
                  y =ᴮ check (x.Func i) := inf_le_right.trans inf_le_left
              have hz_eq : (z =ᴮ check (x.Func j)) ⊓ ((y =ᴮ check (x.Func i)) ⊓ ctx3) ≤
                  z =ᴮ check (x.Func j) := inf_le_left
              set ctx2 := (z =ᴮ check (x.Func j)) ⊓ ((y =ᴮ check (x.Func i)) ⊓ ctx3)
              rcases h_tri with h_eq | h_mem_ij | h_mem_ji
              · -- Equiv (x.Func i) (x.Func j), so y =ᴮ z
                -- y =ᴮ z via chain y =ᴮ check(Func i) =ᴮ check(Func j) =ᴮ z (symm)
                have h_yz := bv_trans hy_eq (bv_trans (le_top.trans (check_bv_eq h_eq)) (bv_symm hz_eq))
                exact h_yz.trans (le_sup_left.trans le_sup_left)
              · -- x.Func i ∈ x.Func j, so y ∈ z
                -- check(Func i) ∈ check(Func j) from h_mem_ij
                have h_cm : ctx2 ≤ check (x.Func i) ∈ᴮ check (x.Func j) :=
                  le_top.trans (check_mem h_mem_ij)
                -- y ∈ z using mem_congr
                have h_ymemz := mem_congr (bv_symm hy_eq) (bv_symm hz_eq) h_cm
                exact h_ymemz.trans (le_sup_right.trans le_sup_left)
              · -- x.Func j ∈ x.Func i, so z ∈ y
                -- check(Func j) ∈ check(Func i) from h_mem_ji
                have h_cm : ctx2 ≤ check (x.Func j) ∈ᴮ check (x.Func i) :=
                  le_top.trans (check_mem h_mem_ji)
                -- z ∈ y using mem_congr:
                -- H₁ : check(Func j) =ᴮ z, H₂ : check(Func i) =ᴮ y, H₃ : check(Func j) ∈ check(Func i)
                exact (mem_congr (bv_symm hz_eq) (bv_symm hy_eq) h_cm).trans le_sup_right

-- src/bvm_extras.lean:2665
lemma check_ewo_right {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ (⨅ u, u ⊆ᴮ (check x : bSet 𝔹) ⟹
      ((u =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ))) := by
  apply le_iInf; intro u
  rw [← deduction, ← deduction]
  exact bSet_axiom_of_regularity u inf_le_right

-- src/bvm_extras.lean:2671
lemma check_ewo {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ epsilon_well_orders (check x : bSet 𝔹) :=
  le_inf (check_ewo_left H) (check_ewo_right H)

-- src/bvm_extras.lean:2674
@[simp] lemma check_Ord {x : PSet} (H : PSet.Ord x) {Γ : 𝔹} :
    Γ ≤ Ord (check x : bSet 𝔹) :=
  le_inf (check_ewo H.left) (check_is_transitive H.right)

-- src/bvm_extras.lean:2677
@[simp] lemma Ord_card_ex (κ : Cardinal) {Γ : 𝔹} :
    Γ ≤ Ord (check (PSet.card_ex κ) : bSet 𝔹) := by
  apply check_Ord; simp [PSet.card_ex]

-- src/bvm_extras.lean:2680


-- src/bvm_extras.lean:2682


-- src/bvm_extras.lean:2684


-- src/bvm_extras.lean:2694


-- src/bvm_extras.lean:2701


-- src/bvm_extras.lean:2714


-- src/bvm_extras.lean:2717


-- src/bvm_extras.lean:2719


-- src/bvm_extras.lean:2721


-- src/bvm_extras.lean:2723


-- src/bvm_extras.lean:2727


-- src/bvm_extras.lean:2730
@[simp] lemma aleph_one_check_exists_mem {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {Γ : 𝔹} : Γ ≤ exists_mem (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) := by
  apply check_exists_mem
  have : ∃ z, z ∈ PSet.card_ex (Cardinal.aleph (1 : ℕ)) :=
    @PSet.card_ex_aleph_exists_mem 1
  convert this using 2
  norm_cast

-- src/bvm_extras.lean:2736
@[simp] lemma B_ext_Ord : B_ext (Ord : bSet 𝔹 → 𝔹) :=
  B_ext_inf B_ext_ewo B_ext_is_transitive

-- src/bvm_extras.lean:2741
/-- The universal property of ℵ₁: it injects into any ordinal larger than ω -/
@[reducible] def le_of_omega_lt (x : bSet 𝔹) : 𝔹 :=
  ⨅ z, Ord z ⟹ ((larger_than bSet.omega z)ᶜ ⟹ injects_into x z)

-- src/bvm_extras.lean:2743
@[simp] lemma B_ext_le_of_omega_lt : B_ext (le_of_omega_lt : bSet 𝔹 → 𝔹) := by
  unfold le_of_omega_lt
  exact B_ext_iInf (h := fun z => B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_injects_into_left)))

end ordinals

-- ============================================================
-- src/bvm_extras.lean:2749-2793: section zorns_lemma
-- ============================================================

section zorns_lemma
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2753


end zorns_lemma

-- ============================================================
-- src/bvm_extras.lean:2795-2821: section CH
-- ============================================================

section CH
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2803
def CH : 𝔹 :=
  (⨆ (x : bSet 𝔹), Ord x ⊓ ⨆ (y : bSet 𝔹),
    (larger_than omega x)ᶜ ⊓ (larger_than x y)ᶜ ⊓
    injects_into y (bv_powerset omega))ᶜ

-- src/bvm_extras.lean:2805
def CH₂ : 𝔹 :=
  (⨆ (x : bSet 𝔹), Ord x ⊓ (larger_than omega x)ᶜ ⊓ (larger_than x (bv_powerset omega))ᶜ)ᶜ

-- src/bvm_extras.lean:2807


end CH

end bSet


end CohenSource_BvmExtras


