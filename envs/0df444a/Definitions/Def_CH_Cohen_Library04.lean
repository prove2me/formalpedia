-- Prove2me | Definitions.Def_CH_Cohen_Library04
-- name    : CH_Cohen_Library04
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T01:48:47.350595+00:00
-- url     : https://prove2.me/theorems/c20f6523-19ba-47c4-9da3-0c37779df215
-- title:
--   Boolean-valued set theory: BvmExtras2, AlephOne
-- statement:
--   This module provides auxiliary name constructions and ordinal interfaces; the countability and first-uncountable-ordinal interfaces for names. These objects form the language and model interfaces used in the forcing and completeness arguments.
--
--   **Formalization Note** The module retains the structural normalization facts needed by these definitions and their constructor proofs. The principal forcing and model-existence assertions are separate theorem nodes.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/BvmExtras2.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/AlephOne.lean

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
import Definitions.Def_CH_Cohen_Library03
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

/- Source module: Definitions.Flypitch4.BvmExtras2 -/
section CohenSource_BvmExtras2
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/bvm_extras2.lean



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch
open Lattice

universe u

namespace bSet

-- ============================================================
-- src/bvm_extras2.lean:17-35: section lemmas
-- ============================================================

section lemmas
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}

-- src/bvm_extras2.lean:20


-- src/bvm_extras2.lean:29


-- src/bvm_extras2.lean:32


end lemmas

-- ============================================================
-- src/bvm_extras2.lean:37-62: section inj_inverse_surj
-- ============================================================

section inj_inverse_surj
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {x y f : bSet 𝔹} {Γ : 𝔹}
  (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f)

-- src/bvm_extras2.lean:41


-- src/bvm_extras2.lean:48


-- src/bvm_extras2.lean:55


end inj_inverse_surj

-- ============================================================
-- src/bvm_extras2.lean:64-345: section Ord
-- ============================================================

section Ord
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}

-- src/bvm_extras2.lean:67


-- src/bvm_extras2.lean:70


-- src/bvm_extras2.lean:78


-- src/bvm_extras2.lean:88


-- src/bvm_extras2.lean:96


-- src/bvm_extras2.lean:104


-- src/bvm_extras2.lean:112


-- ============================================================
-- src/bvm_extras2.lean:122-158: section compl
-- ============================================================

section compl

def compl (x y : bSet 𝔹) : bSet 𝔹 := comprehend (fun z => (z ∈ᴮ y)ᶜ) x

-- src/bvm_extras2.lean:126


-- src/bvm_extras2.lean:129


end compl

-- src/bvm_extras2.lean:141


-- src/bvm_extras2.lean:149

-- src/bvm_extras2.lean:173


-- src/bvm_extras2.lean:201


-- src/bvm_extras2.lean:220


-- src/bvm_extras2.lean:232


-- src/bvm_extras2.lean:245


-- src/bvm_extras2.lean:160


-- src/bvm_extras2.lean:248


-- src/bvm_extras2.lean:259


-- src/bvm_extras2.lean:271


-- src/bvm_extras2.lean:280


-- src/bvm_extras2.lean:289


-- src/bvm_extras2.lean:295
def exists_two (η : bSet 𝔹) : 𝔹 :=
  (⨅ x, x ∈ᴮ η ⟹ ⨆ z, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x))

-- src/bvm_extras2.lean:297
@[simp] lemma B_ext_exists_two : B_ext (exists_two : bSet 𝔹 → 𝔹) := by
  unfold B_ext exists_two
  exact B_ext_iInf (h := fun x =>
    B_ext_imp (h₁ := B_ext_mem_right) (h₂ :=
      B_ext_iSup (h := fun z => B_ext_inf B_ext_mem_right B_ext_const)))

-- src/bvm_extras2.lean:302


-- src/bvm_extras2.lean:312


end Ord

-- ============================================================
-- src/bvm_extras2.lean:347-537: section eps_iso
-- ============================================================

section eps_iso
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras2.lean:350


-- src/bvm_extras2.lean:352


-- src/bvm_extras2.lean:365


-- src/bvm_extras2.lean:371


-- src/bvm_extras2.lean:373


-- src/bvm_extras2.lean:376


-- src/bvm_extras2.lean:379


-- src/bvm_extras2.lean:382


-- src/bvm_extras2.lean:385


-- src/bvm_extras2.lean:388


-- src/bvm_extras2.lean:394


-- src/bvm_extras2.lean:400


-- src/bvm_extras2.lean:423


-- src/bvm_extras2.lean:425


-- src/bvm_extras2.lean:428


-- src/bvm_extras2.lean:433


-- src/bvm_extras2.lean:449


-- src/bvm_extras2.lean:453


-- src/bvm_extras2.lean:460


-- src/bvm_extras2.lean:505


-- src/bvm_extras2.lean:526


end eps_iso

-- ============================================================
-- src/bvm_extras2.lean:539-597: remainder
-- ============================================================

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras2.lean:541
def is_limit (η : bSet 𝔹) : 𝔹 :=
  (∅ ∈ᴮ η) ⊓ (⨅ x, x ∈ᴮ η ⟹ ⨆ y, y ∈ᴮ η ⊓ x ∈ᴮ y)

-- src/bvm_extras2.lean:543


-- src/bvm_extras2.lean:546


-- src/bvm_extras2.lean:563

-- src/bvm_extras2.lean:572


end bSet


end CohenSource_BvmExtras2


/- Source module: Definitions.Flypitch4.AlephOne -/
section CohenSource_AlephOne
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/aleph_one.lean lines 1-450 — Task 19a (part 1 of 2)



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch
open Lattice

universe u v

-- ============================================================
-- src/aleph_one.lean:5-241: namespace PSet
-- ============================================================

namespace PSet

section
open Cardinal

-- src/aleph_one.lean:10


-- src/aleph_one.lean:18


-- src/aleph_one.lean:20


-- src/aleph_one.lean:22


-- src/aleph_one.lean:25


-- src/aleph_one.lean:27


-- src/aleph_one.lean:30


-- src/aleph_one.lean:33


-- src/aleph_one.lean:35


-- src/aleph_one.lean:38


-- src/aleph_one.lean:44


-- src/aleph_one.lean:47


-- src/aleph_one.lean:56


-- src/aleph_one.lean:58


-- src/aleph_one.lean:61


-- src/aleph_one.lean:63


-- src/aleph_one.lean:66


-- src/aleph_one.lean:73


-- src/aleph_one.lean:80


-- src/aleph_one.lean:89


-- src/aleph_one.lean:91


-- src/aleph_one.lean:94


-- src/aleph_one.lean:97


-- src/aleph_one.lean:109


-- src/aleph_one.lean:137


-- src/aleph_one.lean:155


-- src/aleph_one.lean:158


-- src/aleph_one.lean:171


-- src/aleph_one.lean:182


-- src/aleph_one.lean:195


-- src/aleph_one.lean:216


-- src/aleph_one.lean:226


end

end PSet

-- ============================================================
-- src/aleph_one.lean:242-450: namespace bSet
-- ============================================================

open Cardinal bSet
namespace bSet

-- ============================================================
-- src/aleph_one.lean:256-450: section well_ordering
-- ============================================================

section well_ordering

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:260


-- src/aleph_one.lean:262


-- src/aleph_one.lean:266
def mem_rel (x : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x x).type => x.func pr.1 ∈ᴮ x.func pr.2)

-- src/aleph_one.lean:268
lemma mem_mem_rel_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ pair y z ∈ᴮ mem_rel x ↔ (Γ ≤ y ∈ᴮ x ∧ Γ ≤ z ∈ᴮ x ∧ Γ ≤ y ∈ᴮ z) := by
  -- mem_rel x = subset.mk (fun pr : (prod x x).type => x.func pr.1 ∈ x.func pr.2)
  unfold mem_rel
  rw [mem_subset.mk_iff]
  simp only [prod_func, prod_bval]
  constructor
  · -- MP: Γ ≤ ⨆ (i,j), pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) → each conclusion
    intro H
    refine ⟨?_, ?_, ?_⟩
    · -- y ∈ x
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      -- goal: pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) ≤ y ∈ x
      have hyi : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ y =ᴮ x.func i :=
        inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).1
      have hbi : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ x.bval i :=
        inf_le_right.trans (inf_le_right.trans inf_le_left)
      calc pair y z =ᴮ pair (x.func i) (x.func j) ⊓
              (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
          ≤ y =ᴮ x.func i ⊓ x.bval i := le_inf hyi hbi
        _ ≤ y ∈ᴮ x := by
            rw [mem_unfold]; apply le_iSup_of_le i
            exact le_inf inf_le_right inf_le_left
    · -- z ∈ x
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      have hzj : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ z =ᴮ x.func j :=
        inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).2
      have hbj : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ x.bval j :=
        inf_le_right.trans (inf_le_right.trans inf_le_right)
      calc pair y z =ᴮ pair (x.func i) (x.func j) ⊓
              (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
          ≤ z =ᴮ x.func j ⊓ x.bval j := le_inf hzj hbj
        _ ≤ z ∈ᴮ x := by
            rw [mem_unfold]; apply le_iSup_of_le j
            exact le_inf inf_le_right inf_le_left
    · -- y ∈ z
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      -- goal: pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) ≤ y∈z
      set T := pair y z =ᴮ pair (x.func i) (x.func j) ⊓
        (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
      have hyi : T ≤ y =ᴮ x.func i := inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).1
      have hzj : T ≤ z =ᴮ x.func j := inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).2
      have hxixj : T ≤ x.func i ∈ᴮ x.func j := inf_le_right.trans inf_le_left
      -- y = xi, xi ∈ xj, xj = z  →  y ∈ z via mem_congr
      exact mem_congr (bv_symm hyi) (bv_symm hzj) hxixj
  · -- MPI: y∈x ∧ z∈x ∧ y∈z → ⨆ ij, ...
    intro ⟨Hy, Hz, Hyz⟩
    rw [mem_unfold] at Hy Hz
    -- Use iSup_inf_iSup to combine the two iSups, then bound elementwise
    apply le_trans (le_inf (le_inf Hy Hz) Hyz)
    -- goal: (⨆ i, bi⊓y=xi) ⊓ (⨆ j, bj⊓z=xj) ⊓ y∈z ≤ ⨆ (k,l), ...
    rw [show (⨆ i : x.type, x.bval i ⊓ y =ᴮ x.func i) ⊓
              (⨆ j : x.type, x.bval j ⊓ z =ᴮ x.func j) =
              ⨆ ij : x.type × x.type, (x.bval ij.1 ⊓ y =ᴮ x.func ij.1) ⊓
                (x.bval ij.2 ⊓ z =ᴮ x.func ij.2) from iSup_inf_iSup]
    rw [inf_comm]
    apply bv_cases_right; intro ⟨i, j⟩
    apply le_iSup_of_le (i, j)
    simp only [prod_func, prod_bval]
    -- After bv_cases_right intro ⟨i, j⟩ and rw [inf_comm], context is:
    -- y∈z ⊓ ((bi⊓y=xi) ⊓ (bj⊓z=xj)) ≤ pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj))
    -- Extract parts:
    have hbeq_y : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        y =ᴮ x.func i := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hbeq_z : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        z =ᴮ x.func j := inf_le_right.trans (inf_le_right.trans inf_le_right)
    have hbval_i : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        x.bval i := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hbval_j : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        x.bval j := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hyz : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        y ∈ᴮ z := inf_le_left
    refine le_inf (pair_eq_pair_iff.mpr ⟨hbeq_y, hbeq_z⟩)
      (le_inf (mem_congr hbeq_y hbeq_z hyz) (le_inf hbval_i hbval_j))

-- src/aleph_one.lean:286
@[simp] lemma B_congr_mem_rel : B_congr (mem_rel : bSet 𝔹 → bSet 𝔹) := by
  intro x y Γ H_eq
  -- Use prod_ext: both subsets of prod x x
  have H_sub_x : Γ ≤ mem_rel x ⊆ᴮ prod x x := subset.mk_subset
  have H_prod_eq : Γ ≤ prod x x =ᴮ prod y y := prod_congr H_eq H_eq
  have H_sub_y : Γ ≤ mem_rel y ⊆ᴮ prod x x :=
    poset_yoneda_inv Γ subst_congr_subset_right
      (le_inf subset.mk_subset (bv_symm H_prod_eq))
  apply prod_ext H_sub_x H_sub_y
  apply le_iInf; intro v; rw [← deduction]
  apply le_iInf; intro w; rw [← deduction]
  -- ctx: Γ ⊓ v ∈ x ⊓ w ∈ x
  apply le_inf
  · -- pair v w ∈ mem_rel x → pair v w ∈ mem_rel y  (forward direction)
    rw [← deduction]
    -- Goal: Γ ⊓ v ∈ x ⊓ w ∈ x ⊓ pair v w ∈ mem_rel x ≤ pair v w ∈ mem_rel y
    -- Abbreviate the context:
    apply (mem_mem_rel_iff (x := y) (y := v) (z := w)).mpr
    -- Need: ctx ≤ v ∈ y ∧ ctx ≤ w ∈ y ∧ ctx ≤ v ∈ w
    have ctx_le_x_eq_y : Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel x ≤ x =ᴮ y :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H_eq))
    have hpr := (mem_mem_rel_iff (Γ := Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel x)
      (x := x) (y := v) (z := w)).mp inf_le_right
    exact ⟨bv_rw'' ctx_le_x_eq_y hpr.1 B_ext_mem_right,
           bv_rw'' ctx_le_x_eq_y hpr.2.1 B_ext_mem_right,
           hpr.2.2⟩
  · -- pair v w ∈ mem_rel y → pair v w ∈ mem_rel x  (backward direction)
    rw [← deduction]
    apply (mem_mem_rel_iff (x := x) (y := v) (z := w)).mpr
    have ctx_le_y_eq_x : Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel y ≤ y =ᴮ x :=
      bv_symm (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H_eq)))
    have hpr := (mem_mem_rel_iff (Γ := Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel y)
      (x := y) (y := v) (z := w)).mp inf_le_right
    exact ⟨bv_rw'' ctx_le_y_eq_x hpr.1 B_ext_mem_right,
           bv_rw'' ctx_le_y_eq_x hpr.2.1 B_ext_mem_right,
           hpr.2.2⟩

-- src/aleph_one.lean:297
def prod_map (x y v w : bSet 𝔹) (f g : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun (pr : (prod (prod x v) (prod y w)).type) =>
    pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (v.func pr.1.2) (w.func pr.2.2) ∈ᴮ g)

-- src/aleph_one.lean:299
def prod_map_self (x y f : bSet 𝔹) : bSet 𝔹 :=
  prod_map x y x y f f

-- src/aleph_one.lean:302
lemma B_congr_prod_map_self_left_aux {y f x x' : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ x =ᴮ x') :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ prod_map_self x y f ⟹ z ∈ᴮ prod_map_self x' y f := by
  -- Goal: Γ ≤ ⨅ z, z ∈ prod_map_self x y f ⟹ z ∈ prod_map_self x' y f
  -- prod_map_self x y f = subset.mk χ where parent = prod(prod x x)(prod y y)
  -- Strategy: for each z, go through the iSup elements of prod_map_self x y f
  --   and produce corresponding elements for prod_map_self x' y f by reindexing
  apply le_iInf; intro z; rw [← deduction]
  -- ctx: Γ ⊓ z ∈ prod_map_self x y f
  -- unfold both sides
  show Γ ⊓ z ∈ᴮ prod_map_self x y f ≤ z ∈ᴮ prod_map_self x' y f
  -- Extract from iSup in prod_map_self x y f
  have Hmem_iff : Γ ⊓ z ∈ᴮ prod_map_self x y f ≤ z ∈ᴮ prod_map_self x y f := inf_le_right
  rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
    pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl] at Hmem_iff
  rw [mem_subset.mk_iff₂] at Hmem_iff
  apply le_trans (le_inf Hmem_iff le_rfl)
  apply bv_cases_left; intro pr
  obtain ⟨⟨i₁, i₂⟩, j₁, j₂⟩ := pr
  simp only [prod_func, prod_bval]
  -- ctx: ((x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)) ⊓
  --       (z=ᴮpair(pair xi₁ xi₂)(pair yj₁ yj₂) ⊓ (χ₁⊓χ₂)) ⊓ (Γ ⊓ z∈...)
  -- Need: ctx ≤ z ∈ prod_map_self x' y f
  -- bv_rw' on zeq: reduce to pair(xi₁ xi₂)(yj₁ yj₂) ∈ prod_map_self x' y f
  -- Then provide the witness directly via mem_subset.mk_iff₂.mpr
  -- xi₁ ∈ x' (via bv_rw'' Heq (xi₁∈x)): for the new index i₁', use mem_unfold + bv_cases_left
  -- To avoid index extraction, we stay in the iSup form and use bv_use
  rw [show prod_map_self x' y f = subset.mk (fun pr' : (prod (prod x' x') (prod y y)).type =>
    pair (x'.func pr'.1.1) (y.func pr'.2.1) ∈ᴮ f ⊓ pair (x'.func pr'.1.2) (y.func pr'.2.2) ∈ᴮ f) from rfl,
    mem_subset.mk_iff₂]
  -- Goal: ctx ≤ ⨆ pr', bval'(pr') ⊓ (z=ᴮfunc'(pr') ⊓ χ'(pr'))
  -- Ctx structure: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (zeq ⊓ (χ1⊓χ2)) ⊓ (Γ ⊓ z∈...)
  -- xi₁ ∈ x' (via mem_congr) → get i₁' via le_trans + bv_cases_left
  apply le_trans (b := (⨆ i₁' : x'.type, x'.bval i₁' ⊓ x.func i₁ =ᴮ x'.func i₁') ⊓ _)
  · apply le_inf
    · rw [← mem_unfold]
      -- prove ctx ≤ x.func i₁ ∈ᴮ x'
      exact mem_congr bv_refl (inf_le_right.trans (inf_le_left.trans H_eq))
        ((inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))).trans (mem_mk' x i₁))
    · exact le_rfl
  apply bv_cases_left; intro i₁'
  -- ctx1 = (x'.bval i₁' ⊓ xi₁=x'.func i₁') ⊓ ctx
  -- xi₂ ∈ x' → get i₂' via le_trans + bv_cases_left
  apply le_trans (b := (⨆ i₂' : x'.type, x'.bval i₂' ⊓ x.func i₂ =ᴮ x'.func i₂') ⊓ _)
  · apply le_inf
    · rw [← mem_unfold]
      -- prove ctx1 ≤ x.func i₂ ∈ᴮ x'
      exact mem_congr bv_refl (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans H_eq)))
        ((inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))).trans
          (mem_mk' x i₂))
    · exact le_rfl
  apply bv_cases_left; intro i₂'
  -- ctx2 = (x'.bval i₂' ⊓ xi₂=x'.func i₂') ⊓ ctx1
  -- ctx2 structure:
  --   (x'.bval i₂' ⊓ x.func i₂ =ᴮ x'.func i₂') ⊓
  --   ((x'.bval i₁' ⊓ x.func i₁ =ᴮ x'.func i₁') ⊓
  --    (((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (zeq ⊓ (χ1⊓χ2)) ⊓ (Γ ⊓ z∈...)))
  apply bv_use ((i₁', i₂'), j₁, j₂)
  simp only [prod_func, prod_bval]
  -- Extractions from ctx2 (after simp):
  --   x'.bval i₁' : ir.il.il
  --   xi₁=x'.func i₁' : ir.il.ir
  --   x'.bval i₂' : il.il
  --   xi₂=x'.func i₂' : il.ir
  --   xb1 : ir.ir.il.il.il
  --   xb2 : ir.ir.il.il.ir
  --   yb1 : ir.ir.il.ir.il
  --   yb2 : ir.ir.il.ir.ir
  --   zeq : ir.ir.ir.il
  --   χ1  : ir.ir.ir.ir.il
  --   χ2  : ir.ir.ir.ir.ir
  apply le_inf
  · -- bval': (x'.bval i₁' ⊓ x'.bval i₂') ⊓ (y.bval j₁ ⊓ y.bval j₂)
    apply le_inf (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))))
    · exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_right))))
  · apply le_inf
    · -- z =ᴮ pair(pair x'.func(i₁') x'.func(i₂'))(pair yj₁ yj₂)
      -- First prove z =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂), then rewrite xi₁ → x'.func i₁'
      apply bv_trans
      · -- zeq: ctx2 ≤ z =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
        exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_left)))
      · apply pair_eq_pair_iff.mpr; constructor
        · apply pair_eq_pair_iff.mpr
          -- Hi₁'eq: ir.il.ir, Hi₂'eq: il.ir
          exact ⟨inf_le_right.trans (inf_le_left.trans inf_le_right), inf_le_left.trans inf_le_right⟩
        · apply pair_eq_pair_iff.mpr; exact ⟨bv_refl, bv_refl⟩
    · apply le_inf
      · -- pair x'.func(i₁') yj₁ ∈ f
        exact bv_rw' (ϕ := fun v => pair v (y.func j₁) ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
          (H := bv_symm (inf_le_right.trans (inf_le_left.trans inf_le_right)))
          (H_new := inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))))
      · -- pair x'.func(i₂') yj₂ ∈ f
        exact bv_rw' (ϕ := fun v => pair v (y.func j₂) ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
          (H := bv_symm (inf_le_left.trans inf_le_right))
          (H_new := inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))))

-- src/aleph_one.lean:329
@[simp] lemma B_congr_prod_map_self_left {y f : bSet 𝔹} :
    B_congr (fun x : bSet 𝔹 => prod_map_self x y f) := by
  intro x x' Γ H_eq
  apply mem_ext
  · apply B_congr_prod_map_self_left_aux; exact H_eq
  · apply B_congr_prod_map_self_left_aux; exact bv_symm H_eq

-- src/aleph_one.lean:336


-- src/aleph_one.lean:379


-- src/aleph_one.lean:382


-- src/aleph_one.lean:391


-- src/aleph_one.lean:425


-- src/aleph_one.lean:437


-- ============================================================
-- src/aleph_one.lean:451-579: remaining well_ordering lemmas
-- ============================================================

-- src/aleph_one.lean:451


-- src/aleph_one.lean:461


-- src/aleph_one.lean:471


-- src/aleph_one.lean:503


-- src/aleph_one.lean:515


end well_ordering

-- ============================================================
-- src/aleph_one.lean:583-888: section a1
-- ============================================================

section a1

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:586
-- The comprehension predicate for a1


-- src/aleph_one.lean:612


-- src/aleph_one.lean:597: the predicate: a1_ψ v x holds when x is an ordinal injecting into ω
-- with induced epsilon relation on ω equal to v, and v ≠ ∅




-- src/aleph_one.lean:620
-- a1_func χ: the ordinal x such that a1_ψ (a1'.func χ) x holds


-- Convert a1'_AE to the form needed by AE_convert'


-- Spec for a1_func


-- src/aleph_one.lean:630


-- src/aleph_one.lean:632


-- src/aleph_one.lean:641


-- src/aleph_one.lean:643


-- src/aleph_one.lean:646


-- src/aleph_one.lean:655


-- src/aleph_one.lean:662


-- src/aleph_one.lean:679


-- src/aleph_one.lean:690


-- src/aleph_one.lean:700


-- src/aleph_one.lean:723


-- src/aleph_one.lean:746


-- src/aleph_one.lean:777
  -- (η=1)ᶜ

-- src/aleph_one.lean:802


-- src/aleph_one.lean:818


-- src/aleph_one.lean:826


-- src/aleph_one.lean:828


-- src/aleph_one.lean:834


-- src/aleph_one.lean:862


end a1

-- ============================================================
-- src/aleph_one.lean:890-926: final section
-- ============================================================

section

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:894


-- src/aleph_one.lean:905


-- src/aleph_one.lean:915


end

end bSet


end CohenSource_AlephOne


