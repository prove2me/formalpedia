-- Prove2me | Definitions.Def_CH_Cohen_Library10
-- name    : CH_Cohen_Library10
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T02:01:01.993853+00:00
-- url     : https://prove2.me/theorems/57c830aa-22bf-40ac-a688-5ebca351d4b8
-- title:
--   Boolean-valued set theory: ForcingCH, Zfc
-- statement:
--   This module provides auxiliary forcing and cardinal-comparison interfaces; the expanded set-theory language, its axiom sentences, and its CH formulas. These objects form the language and model interfaces used in the forcing and completeness arguments.
--
--   **Formalization Note** The module retains the structural normalization facts needed by these definitions and their constructor proofs. The principal forcing and model-existence assertions are separate theorem nodes.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/ForcingCH.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Zfc.lean

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
import Definitions.Def_CH_Cohen_Library09
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

/- Source module: Definitions.Flypitch4.ForcingCH -/
section CohenSource_ForcingCH
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/forcing_CH.lean (645 lines) — Task 21




set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Flypitch
open Lattice

universe u

open Set TopologicalSpace Cardinal

-- Local notation for Boolean implication / biimplication
local infix:65 " ⟹ " => Lattice.imp
local infix:50 " ⇔ " => Lattice.biimp
-- ≺ means "strictly smaller" (negation of larger_than via complement)
local infix:75 " ≺ " => (fun x y => (bSet.larger_than x y)ᶜ)
-- ≼ means "injects into"
local infix:75 " ≼ " => (fun x y => bSet.injects_into x y)

-- ℵ₁ as a pSet
noncomputable abbrev pSet_aleph1 : PSet.{u} := PSet.card_ex (Cardinal.aleph 1)

-- local ω shorthand
local notation "ω" => (bSet.omega)

attribute [local instance] Classical.propDecidable

-- ============================================================
-- namespace bSet
-- ============================================================

namespace bSet

-- ============================================================
-- section aleph_one (src lines 25-42)
-- ============================================================

section aleph_one

variable {𝔹 : Type*} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing_CH.lean:31


-- src/forcing_CH.lean:33


-- src/forcing_CH.lean:36


-- src/forcing_CH.lean:39


end aleph_one

-- ============================================================
-- section lemmas (src lines 44-353)
-- ============================================================

section lemmas

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing_CH.lean:51-53


-- src/forcing_CH.lean:55-62


-- src/forcing_CH.lean:64-77


-- src/forcing_CH.lean:79-81


-- src/forcing_CH.lean:82-102


-- src/forcing_CH.lean:104-113


-- src/forcing_CH.lean:115-124


-- src/forcing_CH.lean:128-169


-- src/forcing_CH.lean:171-191


-- ============================================================
-- section function_reflect (src lines 193-350)
-- ============================================================

section function_reflect

-- Private auxiliary for function_reflect_of_omega_closed.
-- We prove existence of the full sequence at the Prop level using Nat.rec.
-- This avoids the Classical.choose definitional reduction issue.




end function_reflect

end lemmas

end bSet

-- ============================================================
-- namespace collapse_algebra (src lines 356-645)
-- ============================================================

namespace collapse_algebra

open bSet Flypitch

-- The collapse Boolean algebra for forcing CH.
noncomputable def 𝔹_collapse : Type u :=
  CollapseAlgebra (pSet_aleph1 : PSet.{u}).Type
    (PSet.powerset PSet.omega : PSet.{u}).Type

 instance : Nonempty (PSet.powerset PSet.omega : PSet.{u}).Type := by
  simp only [PSet.powerset, PSet.Type]; exact ⟨Set.univ⟩

 instance : Nonempty ((pSet_aleph1 : PSet.{u}).Type →
    (PSet.powerset PSet.omega : PSet.{u}).Type) :=
  ⟨fun _ => Classical.arbitrary _⟩

noncomputable instance 𝔹_collapse_ncba :
    NontrivialCompleteBooleanAlgebra 𝔹_collapse :=
  collapseAlgebra_ncba (X := (pSet_aleph1 : PSet.{u}).Type)
    (Y := (PSet.powerset PSet.omega : PSet.{u}).Type)

-- Register the collapseSpace topology so RegularOpens lemmas work


-- ============================================================
-- Nonzero witness for dense omega-closed sets (src lines 377-388)
-- ============================================================

-- src/forcing_CH.lean:377-388


-- ============================================================
-- AE_of_check_func_check (src lines 371-444)
-- ============================================================

-- src/forcing_CH.lean:390-411: AE for check functions in collapse algebra


-- src/forcing_CH.lean:416-444


-- ============================================================
-- π_af definitions (src lines 446-551)
-- ============================================================

-- The cylinder set function for the collapse algebra:
-- π_af η S = {g : ℵ₁.Type → 𝒫(ω).Type | g(η) = S}


-- src/forcing_CH.lean:458-460


-- src/forcing_CH.lean:464-485


-- src/forcing_CH.lean:487-501


-- src/forcing_CH.lean:503-505


-- src/forcing_CH.lean:507-523


-- src/forcing_CH.lean:525-527


-- src/forcing_CH.lean:529-530


-- src/forcing_CH.lean:532-537


-- src/forcing_CH.lean:539-545


-- src/forcing_CH.lean:547


-- src/forcing_CH.lean:549-550


-- src/forcing_CH.lean:552


-- src/forcing_CH.lean:554


-- src/forcing_CH.lean:556-557




-- src/forcing_CH.lean:559-593
-- src/forcing_CH.lean:559-593


-- src/forcing_CH.lean:595-608


-- src/forcing_CH.lean:610-615


-- src/forcing_CH.lean:617-630


-- src/forcing_CH.lean:632-637
-- ≺ = (larger_than _ _)ᶜ
-- The statement: (check ℵ₁ ≺ 𝒫ω)ᶜ = larger_than (check ℵ₁) (𝒫ω)
-- Proof: by contradiction from aleph1_larger_than_continuum and continuum_le_continuum_check


-- ============================================================
-- The main theorems: CH_true and CH₂_true (src lines 639-644)
-- ============================================================

-- src/forcing_CH.lean:639


-- src/forcing_CH.lean:642


end collapse_algebra


end CohenSource_ForcingCH


/- Source module: Definitions.Flypitch4.Zfc -/
section CohenSource_Zfc
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/zfc.lean (552 lines) — Task 22 -/





set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Fol bSet

universe u

-- ============================================================
-- The language of ZFC (src/zfc.lean:32-46)
-- ============================================================

/-- Relation symbols of ZFC (just membership ∈). -/
inductive ZFC_rel : ℕ → Type 1
  | ε : ZFC_rel 2

/-- Function symbols of ZFC. -/
inductive ZFC_func : ℕ → Type 1
  | emptyset : ZFC_func 0
  | pr       : ZFC_func 2
  | ω        : ZFC_func 0
  | P        : ZFC_func 1
  | Union    : ZFC_func 1

/-- The language of ZFC set theory. -/
def L_ZFC : Language.{1} :=
  { functions := ZFC_func, relations := ZFC_rel }

-- ============================================================
-- The Boolean-valued V model (src/zfc.lean:48-113)
-- ============================================================

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

/-- Interpret L_ZFC function symbols in bSet β. -/
def bSet_model_fun_map : ∀ {n : ℕ}, L_ZFC.functions n → DVec (bSet β) n → bSet β
  | _, ZFC_func.emptyset, _  => bSet.empty
  | _, ZFC_func.pr, DVec.cons x (DVec.cons y DVec.nil) => pair x y
  | _, ZFC_func.ω, _ => bSet.omega
  | _, ZFC_func.P, DVec.cons x DVec.nil => bv_powerset x
  | _, ZFC_func.Union, DVec.cons x DVec.nil => bv_union x

/-- Interpret L_ZFC relation symbols in bSet β. -/
def bSet_model_rel_map : ∀ {n : ℕ}, L_ZFC.relations n → DVec (bSet β) n → β
  | _, ZFC_rel.ε, DVec.cons x (DVec.cons y DVec.nil) => x ∈ᴮ y

variable (β)

/-- The Boolean-valued model V(β) of ZFC. -/
noncomputable def V : bStructure L_ZFC β :=
  { carrier   := bSet β
    fun_map   := bSet_model_fun_map
    rel_map   := bSet_model_rel_map
    eq        := (· =ᴮ ·)
    eq_refl   := fun x => bv_eq_refl x
    eq_symm   := fun x y => bv_eq_symm
    eq_trans  := fun y => bv_eq_trans
    fun_congr := by
      intro n F
      cases F with
      | emptyset =>
        intro x y
        cases x; cases y
        simp [bSet_model_fun_map, DVec.map2, DVec.fInf]
      | ω =>
        intro x y
        cases x; cases y
        simp [bSet_model_fun_map, DVec.map2, DVec.fInf]
      | P =>
        intro x y
        match x, y with
        | DVec.cons a DVec.nil, DVec.cons b DVec.nil =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact bv_powerset_congr le_rfl
      | Union =>
        intro x y
        match x, y with
        | DVec.cons a DVec.nil, DVec.cons b DVec.nil =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact bv_union_congr le_rfl
      | pr =>
        intro x y
        match x, y with
        | DVec.cons a (DVec.cons b DVec.nil), DVec.cons c (DVec.cons d DVec.nil) =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact pair_congr inf_le_left inf_le_right
    rel_congr := by
      intro n R
      cases R with
      | ε =>
        intro x y
        match x, y with
        | DVec.cons a (DVec.cons b DVec.nil), DVec.cons c (DVec.cons d DVec.nil) =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_rel_map]
          -- goal: a =ᴮ c ⊓ b =ᴮ d ⊓ a ∈ᴮ b ≤ c ∈ᴮ d
          exact mem_congr (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right
  }

@[simp] lemma carrier_V : ↥(V β) = bSet β := rfl
@[simp] lemma V_forall {C : (V β) → β} : (⨅ (x : V β), C x) = ⨅ (x : bSet β), C x := rfl
@[simp] lemma V_exists {C : (V β) → β} : (⨆ (x : V β), C x) = ⨆ (x : bSet β), C x := rfl
@[simp] lemma V_eq {a b : V β} : (V β).eq a b = a =ᴮ b := rfl

instance V_β_nonempty : Nonempty (V β) := ⟨bSet.empty⟩

variable {β}

-- ============================================================
-- Bounded terms/formulas for L_ZFC (src/zfc.lean:115-140)
-- ============================================================

def emptyset' {n} : bounded_term L_ZFC n := bd_const ZFC_func.emptyset
notation "∅'" => emptyset'

def omega' {n} : bounded_term L_ZFC n := bd_const ZFC_func.ω
notation "ω'" => omega'

def Powerset {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFC_func.P) t
notation "P'" => Powerset

/-- Boolean membership formula: t₁ ∈ t₂ -/
def mem' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  @bounded_formula_of_relation L_ZFC 2 n ZFC_rel.ε t₁ t₂

/-- Bounded pair term -/
def pair' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  @bounded_term_of_function L_ZFC 2 n ZFC_func.pr t₁ t₂

/-- Bounded union term -/
def union' {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFC_func.Union) t
notation "⋃'" => union'

/-- Subset formula: t₁ ⊆ t₂ -/
def subset'' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_imp
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₁ ↑ᵇ' 1 # 0))
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₂ ↑ᵇ' 1 # 0)))

-- ============================================================
-- Simp lemmas for boolean_realize (src/zfc.lean:142-176)
-- ============================================================

@[simp] lemma boolean_realize_bounded_formula_mem' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (mem' t₁ t₂) DVec.nil =
    boolean_realize_bounded_term v t₁ DVec.nil ∈ᴮ
    boolean_realize_bounded_term v t₂ DVec.nil := by
  rfl

@[simp] lemma boolean_realize_bounded_term_Union' {n} {v : DVec (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (⋃' t) DVec.nil =
    bv_union (boolean_realize_bounded_term v t DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_term_Powerset' {n} {v : DVec (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (P' t) DVec.nil =
    bv_powerset (boolean_realize_bounded_term v t DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_term_omega' {n} {v : DVec (V β) n} :
    boolean_realize_bounded_term v ω' DVec.nil = bSet.omega := by
  rfl

@[simp] lemma boolean_realize_bounded_term_emptyset' {n} {v : DVec (V β) n} :
    boolean_realize_bounded_term v ∅' DVec.nil = bSet.empty := by
  rfl

@[simp] lemma boolean_realize_bounded_term_pair' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (pair' t₁ t₂) DVec.nil =
    pair (boolean_realize_bounded_term v t₁ DVec.nil)
         (boolean_realize_bounded_term v t₂ DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_formula_subset' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (subset'' t₁ t₂) DVec.nil =
    boolean_realize_bounded_term v t₁ DVec.nil ⊆ᴮ boolean_realize_bounded_term v t₂ DVec.nil := by
  simp only [subset'', boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term_subst_lift, V_forall]
  -- goal: ⨅ x : bSet β, imp (x ∈ brt t₁) (x ∈ brt t₂) = brt t₁ ⊆ᴮ brt t₂
  rw [subset_unfold']
  -- goal: ⨅ x : bSet β, imp (x ∈ brt t₁) (x ∈ brt t₂) = ⨅ (w : bSet β), w ∈ brt t₁ ⟹ w ∈ brt t₂
  -- These should be definitionally equal since imp = ⟹
  rfl

@[simp] lemma fin_0 {n : ℕ} : (0 : Fin (n + 1)).1 = 0 := rfl
@[simp] lemma fin_1 {n : ℕ} : (1 : Fin (n + 2)).1 = 1 := rfl
@[simp] lemma fin_2 {n : ℕ} : (2 : Fin (n + 3)).1 = 2 := rfl
@[simp] lemma fin_3 {n : ℕ} : (3 : Fin (n + 4)).1 = 3 := rfl

-- ============================================================
-- Ordinal predicates (src/zfc.lean:307-327)
-- ============================================================

def is_transitive_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
                 (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))

def epsilon_trichotomy_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
    (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
      (bd_or
        (bd_or (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
               (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))))

def epsilon_well_founded_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
    (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
      (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
          (bd_not (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))))))))

def ewo_f : bounded_formula L_ZFC 1 := bd_and epsilon_trichotomy_f epsilon_well_founded_f

def Ord_f : bounded_formula L_ZFC 1 := bd_and ewo_f is_transitive_f

@[simp] lemma Ord_f_is_Ord {x : V β} :
    boolean_realize_bounded_formula (DVec.cons x DVec.nil) Ord_f DVec.nil = Ord x := by
  simp only [Ord_f, ewo_f, epsilon_trichotomy_f, epsilon_well_founded_f, is_transitive_f,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_or,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_subset', boolean_realize_bounded_term_emptyset',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq]
  unfold bSet.Ord epsilon_well_orders epsilon_trichotomy epsilon_well_founded is_transitive
  rfl

-- ============================================================
-- The ZFC axioms as sentences (src/zfc.lean:179-382)
-- ============================================================

-- axiom of emptyset: ∀ x, x ∉ ∅
def axiom_of_emptyset : sentence L_ZFC :=
  bd_all (bd_not (mem' (bd_var ⟨0, by omega⟩) ∅'))



-- axiom of ordered pairs: ∀ x y z w, pair(x,y) = pair(z,w) ↔ x=z ∧ y=w
def axiom_of_ordered_pairs : sentence L_ZFC :=
  bd_all (bd_all (bd_all (bd_all
    (bd_biimp
      (bd_equal (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))
                (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
      (bd_and
        (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_equal (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)))))))



-- axiom of extensionality: ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y
def axiom_of_extensionality : sentence L_ZFC :=
  bd_all (bd_all
    (bd_imp
      (bd_all (bd_biimp
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))
      (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))))



-- axiom schema of strong collection (src/zfc.lean:208-211)
def axiom_of_collection {n} (ϕ : bounded_formula L_ZFC (n + 2)) : sentence L_ZFC :=
  bd_alls (n + 1) $
    bd_imp
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_ex (ϕ ↑ᶠᵇ' 1 # 2))))
      (bd_ex
        (bd_and
          (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
              (ϕ ↑ᶠᵇ' 2 # 2)))))
          (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
              (subst0_bounded_formula (ϕ ↑ᶠᵇ' 3 # 2) (bd_var ⟨1, by omega⟩))))))))










-- axiom of union: ∀ u x, x ∈ ⋃u ↔ ∃ y ∈ u, x ∈ y
def axiom_of_union : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, by omega⟩) (union' (bd_var ⟨1, by omega⟩)))
      (bd_ex (bd_and
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))))))


-- axiom of powerset: ∀ z y, y ∈ P(z) ↔ ∀ x ∈ y, x ∈ z
def axiom_of_powerset : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, by omega⟩) (Powerset (bd_var ⟨1, by omega⟩)))
      (bd_all (bd_imp
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))))))


-- axiom of infinity (src/zfc.lean:332-347)
def axiom_of_infinity : sentence L_ZFC :=
  bd_and
    (bd_and
      (bd_and
        (mem' ∅' ω')
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) ω')
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, by omega⟩) ω')
            (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))
      (bd_ex (bd_and Ord_f (bd_equal ω' (bd_var ⟨0, by omega⟩)))))
    (bd_all (bd_imp Ord_f (bd_imp
      (bd_and (mem' ∅' (bd_var ⟨0, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
            (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))
      (subset'' ω' (bd_var ⟨0, by omega⟩)))))


-- axiom of regularity: ∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y
def axiom_of_regularity : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
    (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (bd_not (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))))))


-- Zorn's lemma (src/zfc.lean:363-376)
def zorns_lemma : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
    (bd_imp
      (bd_all (bd_imp
        (bd_and (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
          (bd_all (bd_all (bd_imp
            (bd_and (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨2, by omega⟩))
                    (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩)))
            (bd_or (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
                   (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))))))
        (mem' (union' (bd_var ⟨0, by omega⟩)) (bd_var ⟨1, by omega⟩))))
      (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
          (bd_imp (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
            (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))))


-- ============================================================
-- The ZFC theory (src/zfc.lean:378-399)
-- ============================================================

/-- The theory ZFC: a set of L_ZFC-sentences. -/
def ZFC : SentTheory L_ZFC :=
  {axiom_of_emptyset, axiom_of_ordered_pairs, axiom_of_extensionality, axiom_of_union,
   axiom_of_powerset, axiom_of_infinity, axiom_of_regularity, zorns_lemma} ∪
  ⋃ (n : ℕ), axiom_of_collection '' (Set.univ : Set (bounded_formula L_ZFC (n + 2)))





-- ============================================================
-- Functional-relation formulas (src/zfc.lean:402-470)
-- ============================================================

def is_func_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (mem' (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨4, by omega⟩))
        (mem' (pair' (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨4, by omega⟩)))
      (bd_imp (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))
              (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))

@[simp] lemma realize_is_func_f {f : V β} :
    boolean_realize_bounded_formula (DVec.cons f DVec.nil) is_func_f DVec.nil = is_func f := by
  simp only [is_func_f, is_func, boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_and, boolean_realize_bounded_term_pair',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_eq]

def is_total'_f : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
      (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨2, by omega⟩)))))

@[simp] lemma realize_is_total'_f {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_total'_f DVec.nil =
    is_total x y f := by
  simp only [is_total'_f, is_total, boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_term_pair', boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists, V_eq]

def is_total'_f₂ : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨4, by omega⟩))
      (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨2, by omega⟩)))))

@[simp] lemma realize_is_total'_f₂ {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_total'_f₂ DVec.nil =
    is_total y x f := by
  simp only [is_total'_f₂, is_total, boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_term_pair', boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists, V_eq]

def is_func'_f : bounded_formula L_ZFC 3 :=
  bd_and (is_func_f.cast (by omega)) is_total'_f

def is_func'_f₂ : bounded_formula L_ZFC 3 :=
  bd_and (is_func_f.cast (by omega)) is_total'_f₂

@[simp] lemma realize_is_func'_f {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_func'_f DVec.nil =
    is_func' x y f := by
  simp only [is_func'_f, is_func', boolean_realize_bounded_formula_and,
             boolean_realize_cast_bounded_formula, DVec.trunc, realize_is_func_f,
             realize_is_total'_f]

@[simp] lemma realize_is_func'_f₂ {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_func'_f₂ DVec.nil =
    is_func' y x f := by
  simp only [is_func'_f₂, is_func', boolean_realize_bounded_formula_and,
             boolean_realize_cast_bounded_formula, DVec.trunc, realize_is_func_f,
             realize_is_total'_f₂]

/-- at_most_f [y, x] ↔ larger_than x y (surjection from subset of y onto x) -/
def at_most_f : bounded_formula L_ZFC 2 :=
  bd_ex (bd_ex
    (bd_and
      (bd_and
        (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨3, by omega⟩))
        (is_func'_f₂.cast (by omega)))
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
        (bd_ex (bd_and
          (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
          (mem' (pair' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨2, by omega⟩))))))))

@[simp] lemma realize_at_most_f {x y : V β} :
    boolean_realize_bounded_formula (DVec.cons y (DVec.cons x DVec.nil)) at_most_f DVec.nil =
    larger_than x y := by
  simp only [at_most_f, boolean_realize_bounded_formula, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_subset', boolean_realize_cast_bounded_formula,
             boolean_realize_bounded_term_pair', boolean_realize_bounded_term,
             DVec.trunc, DVec.nth, V_forall, V_exists, V_eq, realize_is_func'_f₂]
  unfold larger_than is_surj
  -- LHS and RHS are α-equivalent (bound var name difference only)
  rfl

def is_inj_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (bd_and
          (mem' (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨4, by omega⟩))
          (mem' (pair' (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨4, by omega⟩)))
        (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
      (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))))))

@[simp] lemma realize_is_inj_f (f : V β) :
    boolean_realize_bounded_formula (DVec.cons f DVec.nil) is_inj_f DVec.nil = is_inj f := by
  simp only [is_inj_f, is_inj, boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_and, boolean_realize_bounded_term_pair',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_eq]

def injects_into_f : bounded_formula L_ZFC 2 :=
  bd_ex (bd_and is_func'_f (is_inj_f.cast (by omega)))

@[simp] lemma realize_injects_into {x y : V β} :
    boolean_realize_bounded_formula (DVec.cons y (DVec.cons x DVec.nil)) injects_into_f DVec.nil =
    injects_into x y := by
  simp only [injects_into_f, boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_and,
             boolean_realize_cast_bounded_formula, DVec.trunc, realize_is_func'_f,
             realize_is_inj_f, V_exists]
  unfold injects_into
  rfl

def non_empty_f : bounded_formula L_ZFC 1 := bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅')

@[simp] lemma non_empty_f_is_non_empty {x : V β} :
    boolean_realize_bounded_formula (DVec.cons x DVec.nil) non_empty_f DVec.nil = not_empty x := by
  simp only [non_empty_f, not_empty, boolean_realize_bounded_formula_not,
             boolean_realize_bounded_formula, boolean_realize_bounded_term_emptyset',
             boolean_realize_bounded_term, DVec.nth, V_eq]
  rfl

-- ============================================================
-- The CH formula (src/zfc.lean:481-502)
-- ============================================================

/-- The continuum hypothesis as an L_ZFC sentence. -/
def CH_f : sentence L_ZFC :=
  bd_all (bd_imp Ord_f
    (bd_or
      (substmax_bounded_formula at_most_f ω')
      (subst0_bounded_formula at_most_f (Powerset omega'))))







-- ============================================================
-- CH is unprovable from ZFC (src/zfc.lean:508-536)
-- ============================================================

open PSet Cardinal

section CH_unprovable

local notation "𝔹" => 𝔹_cohen



instance V_𝔹_nonempty : Nonempty (V 𝔹) := ⟨bSet.empty⟩



end CH_unprovable

open collapse_algebra

section neg_CH_unprovable

instance V_𝔹_collapse_nonempty : Nonempty (V 𝔹_collapse) := ⟨bSet.empty⟩





end neg_CH_unprovable

-- ============================================================
-- CH as a first-order formula (src/zfc.lean:538-552)
-- ============================================================

section CH_formula_sec










end CH_formula_sec


end CohenSource_Zfc


