-- Prove2me | Definitions.Def_CH_Cohen_Library07
-- name    : CH_Cohen_Library07
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-26T01:54:41.073667+00:00
-- url     : https://prove2.me/theorems/4b5ca2f5-c76e-48ee-b040-8f42fb7c3d42
-- title:
--   Boolean-valued set theory: Collapse, Compactness, Completion
-- statement:
--   This module provides auxiliary partial-function and regular-open constructions; finite consistency and syntactic compactness interfaces; consistent extensions and complete theories. These objects form the language and model interfaces used in the forcing and completeness arguments.
--
--   **Formalization Note** The module retains the structural normalization facts needed by these definitions and their constructor proofs. The principal forcing and model-existence assertions are separate theorem nodes.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Collapse.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Compactness.lean; https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Completion.lean

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
import Definitions.Def_CH_Cohen_Library06
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

/- Source module: Definitions.Flypitch4.Collapse -/
section CohenSource_Collapse
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/collapse.lean — Part 1 (lines 1-450).
   Covers: top-level helpers (cardinal, ordinal, topological_space, propositional lemmas),
   PFun extension lemmas (inter/compatible/subfun/sup/pSup/singleton/extend_via/trivial_extension).
   Part 2 (lines 451-916) covers the collapse_poset structure and collapse_algebra.
   The `end Flypitch` at the bottom closes the namespace; Part 2 will reopen it.
-/








set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Cardinal PSet

universe u v

namespace Flypitch

/-! ## Preliminary order lemmas (src lines 9-14) -/





/-! ## Cardinal helpers (src lines 28-50).
    Helper lemmas used in the collapse algebra section.
    In Lean 4 / Mathlib 4: `cardinal.sum` → `Cardinal.sum`, `cardinal.lift` → `Cardinal.lift`,
    `cardinal.sup` → `iSup`. -/









/-! ## Ordinal helpers (src lines 52-70) -/





/-! ## Topological space helpers (src lines 72-84) -/



/-! ## Propositional lemmas (src lines 100-131) -/

@[simp] lemma iff_or_self_left {p q : Prop} : (p ↔ p ∨ q) ↔ (q → p) :=
  ⟨fun h hq => h.mpr (Or.inr hq), fun h => ⟨Or.inl, fun h' => h'.elim id h⟩⟩

@[simp] lemma iff_or_self_right {p q : Prop} : (p ↔ q ∨ p) ↔ (q → p) := by
  simp [or_comm]

@[simp] lemma and_iff_self_right {p q : Prop} : (p ∧ q ↔ p) ↔ (p → q) :=
  ⟨fun h hp => (h.mpr hp).2, fun h => ⟨And.left, fun hp => ⟨hp, h hp⟩⟩⟩

@[simp] lemma and_iff_self_left {p q : Prop} : (p ∧ q ↔ q) ↔ (q → p) := by
  rw [and_comm]; exact and_iff_self_right













/-! ## PFun extensions (src lines 162-543)

    In Lean 4, `pfun` is `PFun` in Mathlib. Key mappings:
    - `pfun.dom` → `PFun.Dom`
    - `pfun.fn` → `PFun.fn`
    - `pfun.ran` → `PFun.ran`

    Many lemmas from the Lean 3 `pfun` namespace are not in Mathlib 4.
    We define them here using the `CPFun` prefix to avoid clashes,
    and avoid defining type class instances on `α →. β` directly. -/

namespace CPFun

attribute [local instance] Classical.propDecidable

variable {ι : Sort*} {α : Type*} {β : Type*}

/-! ### Domain / function basics (src 166-197) -/



lemma mem_Dom_of_mem {f : α →. β} {x : α} {y : β} (h : y ∈ f x) : x ∈ PFun.Dom f :=
  (PFun.mem_dom f x).mpr ⟨y, h⟩



/-- `f.fn x h ∈ f x` -/
lemma fn_mem {f : α →. β} {x : α} (h : x ∈ PFun.Dom f) : PFun.fn f x h ∈ f x :=
  Part.get_mem h



/-- `f.fn x h = y ↔ y ∈ f x` -/
lemma fn_eq_iff_mem {f : α →. β} {x : α} {y : β} (h : x ∈ PFun.Dom f) :
    PFun.fn f x h = y ↔ y ∈ f x :=
  ⟨fun heq => heq ▸ fn_mem h, fun hy => Part.mem_unique (fn_mem h) hy⟩

/-- `fn_eq_of_mem: if y ∈ f x and h₂ : x ∈ Dom f, then f.fn x h₂ = y` -/
lemma fn_eq_of_mem {f : α →. β} {x : α} {y : β} (h1 : y ∈ f x) (h2 : x ∈ PFun.Dom f) :
    PFun.fn f x h2 = y :=
  (fn_eq_iff_mem h2).mpr h1





@[simp] lemma fn_lift (f : α → β) (x : α) :
    (f : α →. β).fn x trivial = f x := by
  simp [PFun.fn_apply, PFun.coe_val]

/-! ### Empty partial function (src 199-203) -/

/-- The empty partial function -/
def empty : α →. β := fun _ => Part.none

@[simp] lemma dom_empty : PFun.Dom (empty : α →. β) = ∅ := by
  simp [PFun.Dom, empty]

@[simp] lemma empty_def (x : α) : (empty : α →. β) x = Part.none := rfl



/-! ### Subfun / le order on PFun (src 287-321) -/

/-- f₁ ≤ f₂ (subfun): ∀ x y, y ∈ f₁ x → y ∈ f₂ x -/
def le (f₁ f₂ : α →. β) : Prop := ∀ x y, y ∈ f₁ x → y ∈ f₂ x











lemma le_lift {f : α →. β} {g : α → β} :
    le f (g : α →. β) ↔ ∀ x y, y ∈ f x → g x = y := by
  simp [le, eq_comm]

/-! ### Compatible (src 324-345) -/













/-! ### Intersection on PFun (src 278-284) -/

/-- The intersection of two partial functions: f₁ ∩ f₂.
    Domain: ∃ y, y ∈ f₁ x ∧ y ∈ f₂ x. Value: f₁(x). -/
noncomputable def pfunInter (f₁ f₂ : α →. β) : α →. β :=
  fun x => ⟨∃ y, y ∈ f₁ x ∧ y ∈ f₂ x,
            fun h => PFun.fn f₁ x (mem_Dom_of_mem (Classical.choose_spec h).1)⟩

@[simp] lemma mem_pfunInter {f₁ f₂ : α →. β} {x : α} {y : β} :
    y ∈ pfunInter f₁ f₂ x ↔ y ∈ f₁ x ∧ y ∈ f₂ x := by
  simp only [pfunInter, Part.mem_eq]
  constructor
  · rintro ⟨hex, rfl⟩
    -- hex : ∃ z, z ∈ f₁ x ∧ z ∈ f₂ x
    -- the Part.get value is PFun.fn f₁ x (mem_Dom_of_mem (Classical.choose_spec hex).1)
    have hcs := Classical.choose_spec hex
    have hd' : x ∈ PFun.Dom f₁ := mem_Dom_of_mem hcs.1
    constructor
    · exact fn_mem hd'
    · have hveq : PFun.fn f₁ x hd' = Classical.choose hex :=
        fn_eq_of_mem hcs.1 hd'
      rw [hveq]; exact hcs.2
  · rintro ⟨hy1, hy2⟩
    refine ⟨⟨y, hy1, hy2⟩, ?_⟩
    apply fn_eq_of_mem hy1







/-! ### Sup on PFun (src 351-400) -/

/-- The sup of f₁ and f₂: f₁ x if x ∈ Dom f₁, else f₂ x. -/
noncomputable def pfunSup (f₁ f₂ : α →. β) : α →. β :=
  fun a => if h : a ∈ PFun.Dom f₁ then f₁ a else f₂ a

lemma pfunSup_eq_of_mem {f₁ f₂ : α →. β} {x : α} (h : x ∈ PFun.Dom f₁) :
    pfunSup f₁ f₂ x = f₁ x := by
  simp only [pfunSup, dif_pos h]

lemma pfunSup_eq_of_nmem {f₁ f₂ : α →. β} {x : α} (h : x ∉ PFun.Dom f₁) :
    pfunSup f₁ f₂ x = f₂ x := by
  simp only [pfunSup, dif_neg h]

@[simp] lemma dom_pfunSup (f₁ f₂ : α →. β) :
    PFun.Dom (pfunSup f₁ f₂) = PFun.Dom f₁ ∪ PFun.Dom f₂ := by
  ext x
  simp only [PFun.Dom, Set.mem_setOf_eq, Set.mem_union]
  by_cases hx : x ∈ PFun.Dom f₁
  · simp only [pfunSup_eq_of_mem hx]; exact ⟨fun h => Or.inl hx, fun _ => hx⟩
  · simp only [pfunSup_eq_of_nmem hx]
    exact ⟨fun h => Or.inr (mem_Dom_of_mem (Part.get_mem h)),
           fun h => h.elim (absurd · hx) id⟩

















/-! ### Indexed Sup on PFun (src 405-450) -/

/-- The indexed sup of a family of partial functions. Uses Classical.choose. -/
noncomputable def pSup {ι : Type*} (f : ι → α →. β) : α →. β :=
  fun x => if h : ∃ i, x ∈ PFun.Dom (f i)
           then f (Classical.choose h) x
           else Part.none





@[simp] lemma dom_pSup {ι : Type*} (f : ι → α →. β) :
    PFun.Dom (pSup f) = ⋃ (i : ι), PFun.Dom (f i) := by
  ext x
  simp only [PFun.Dom, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hx
    -- (pSup f x).Dom
    by_cases hex : ∃ i, x ∈ PFun.Dom (f i)
    · -- pSup f x = f (Classical.choose hex) x
      have key : pSup f x = f (Classical.choose hex) x := dif_pos hex
      rw [key] at hx
      exact ⟨Classical.choose hex, mem_Dom_of_mem (Part.get_mem hx)⟩
    · exfalso
      have hkey : pSup f x = Part.none := by simp only [pSup, dif_neg hex]
      rw [hkey] at hx; exact hx
  · rintro ⟨i, hi⟩
    have hex : ∃ j, x ∈ PFun.Dom (f j) := ⟨i, hi⟩
    have key : pSup f x = f (Classical.choose hex) x := dif_pos hex
    rw [key]
    exact Classical.choose_spec hex









/-! ### Additional Sup lemmas (src 453-470) -/







/-! ### singleton PFun (src 489-509) -/

/-- A partial function with one element in its domain. Port of pfun.singleton (src line 489). -/
def singleton (x : α) (y : β) : α →. β :=
  fun a => ⟨a = x, fun _ => y⟩

@[simp] lemma fn_singleton {x x' : α} {y : β} (H_a : x' = x) :
    PFun.fn (singleton x y) x' H_a = y := rfl

@[simp] lemma mem_singleton {x x' : α} {y y' : β} :
    y' ∈ singleton x y x' ↔ x = x' ∧ y = y' := by
  simp only [singleton, Part.mem_mk_iff]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h.symm, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

@[simp] lemma singleton_eq_some {x : α} {y : β} : singleton x y x = Part.some y := by
  simp [singleton, Part.eq_some_iff]

@[simp] lemma dom_singleton {x : α} {y : β} : PFun.Dom (singleton x y) = {x} := by
  ext x'; simp [singleton, PFun.Dom]

lemma mk_dom_singleton {x : α} {y : β} : #(PFun.Dom (singleton x y)) = 1 := by simp

/-! ### extend_via and trivial_extension (src 512-541) -/

















/-! ### pfunRan: the range of a partial function (src 472-484) -/









end CPFun

end Flypitch

/-! ## Section collapse_poset (src lines 545-766)
    Port of `section collapse_poset`. -/

namespace Flypitch

open CPFun Set TopologicalSpace Cardinal Flypitch.Regular

/-! ### CollapsePoset structure (src lines 547-621) -/

/-- The collapse poset: finite partial functions from X to Y with domain of cardinality < κ.
    Port of `collapse_poset` (src line 547). -/
structure CollapsePoset (X Y : Type u) (κ : Cardinal.{u}) : Type u where
  f    : X →. Y
  Hc   : #(PFun.Dom f) < κ

namespace CollapsePoset

variable {X Y : Type u} {κ : Cardinal.{u}}

/-- The empty collapse poset. Port of collapse_poset.empty (src line 551). -/
def empty {α β : Type u} {κ : Cardinal} (h : 0 < κ) : CollapsePoset α β κ :=
  { f := CPFun.empty, Hc := by simp [h] }











/-- The principal open set associated with a collapse poset.
    Port of collapse_poset.principal_open (src line 580). -/
def principalOpen (p : CollapsePoset X Y κ) : Set (X → Y) :=
  {f | CPFun.le p.f (f : X →. Y)}

@[simp] lemma principalOpen_empty (h : 0 < κ) :
    principalOpen (empty h : CollapsePoset X Y κ) = Set.univ := by
  ext f; simp [principalOpen, empty, CPFun.le, CPFun.empty]

lemma mem_principalOpen_iff {p : CollapsePoset X Y κ} {f : X → Y} :
    f ∈ principalOpen p ↔ ∀ x y, y ∈ p.f x → f x = y := by
  simp [principalOpen, CPFun.le_lift]

lemma mem_principalOpen_iff' {p : CollapsePoset X Y κ} {f : X → Y} :
    f ∈ principalOpen p ↔ ∀ (x : X) (H_x : x ∈ PFun.Dom p.f), f x = PFun.fn p.f x H_x := by
  rw [mem_principalOpen_iff]
  apply forall_congr'; intro x
  constructor
  · intro H Hx; apply H; exact CPFun.fn_mem Hx
  · intro H y hy
    rw [H (CPFun.mem_Dom_of_mem hy)]
    exact CPFun.fn_eq_of_mem hy _

lemma mem_compl_principalOpen_iff {p : CollapsePoset X Y κ} {f : X → Y} :
    f ∈ (principalOpen p)ᶜ ↔ ∃ x, ∃ H_x : x ∈ PFun.Dom p.f, f x ≠ PFun.fn p.f x H_x := by
  rw [Set.mem_compl_iff, mem_principalOpen_iff']
  push Not
  rfl







end CollapsePoset

/-! ### collapse_space: the topology on X → Y (src lines 633-766) -/

/-- The collapse space topology: generated by principal opens.
    Port of collapse_space (src line 633). -/
def collapseSpace (X Y : Type u) : TopologicalSpace (X → Y) :=
  TopologicalSpace.generateFrom
    (Set.image (CollapsePoset.principalOpen (κ := Order.succ ℵ₀)) Set.univ)

section CollapseSpaceLemmas

variable {X Y : Type u}

local instance collapseSpaceInst : TopologicalSpace (X → Y) := collapseSpace X Y

@[simp] lemma principalOpen_isOpen {p : CollapsePoset X Y (Order.succ ℵ₀)} :
    IsOpen (CollapsePoset.principalOpen p) :=
  TopologicalSpace.GenerateOpen.basic _ (Set.mem_image_of_mem _ trivial)

lemma aleph0_lt_aleph0_succ : ℵ₀ < Order.succ (ℵ₀ : Cardinal) :=
  Order.lt_succ ℵ₀



lemma one_lt_aleph0_succ : 1 < Order.succ (ℵ₀ : Cardinal) :=
  lt_trans Cardinal.one_lt_aleph0 aleph0_lt_aleph0_succ



/-- singleton collapse poset. Port of singleton_collapse_poset (src line 651). -/
noncomputable def singletonCollapsePoset (x : X) (y : Y) (hκ : 1 < κ) :
    CollapsePoset X Y κ :=
  { f := CPFun.singleton x y,
    Hc := by simp [CPFun.mk_dom_singleton]; exact hκ }

lemma singletonCollapsePoset_principalOpen' {x : X} {y : Y} {hκ : 1 < κ} :
    CollapsePoset.principalOpen (singletonCollapsePoset x y hκ) = {g : X → Y | g x = y} := by
  ext g
  simp only [Set.mem_setOf_eq, CollapsePoset.mem_principalOpen_iff, CPFun.mem_singleton,
             singletonCollapsePoset]
  constructor
  · intro H; exact H x y ⟨rfl, rfl⟩
  · rintro H x' y' ⟨rfl, rfl⟩; exact H

@[simp] lemma singletonCollapsePoset_principalOpen {x : X} {y : Y}
    {hκ : 1 < Order.succ (ℵ₀ : Cardinal)} :
    CollapsePoset.principalOpen (singletonCollapsePoset x y hκ) = {g : X → Y | g x = y} :=
  singletonCollapsePoset_principalOpen'

lemma compl_principalOpen_isUnion (hκ : 1 < κ) (p : CollapsePoset X Y κ) :
    ∃ (ι : Type u) (s : ι → CollapsePoset X Y κ),
      ⋃ i : ι, CollapsePoset.principalOpen (s i) = (CollapsePoset.principalOpen p)ᶜ := by
  use {pr : X × Y // ∃ H_mem : pr.1 ∈ PFun.Dom p.f, pr.2 ≠ PFun.fn p.f pr.1 H_mem}
  use fun s => singletonCollapsePoset s.val.1 s.val.2 hκ
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨⟨x, z⟩, H_mem, H_neq⟩, H_in⟩
    rw [singletonCollapsePoset_principalOpen'] at H_in
    simp only [Set.mem_setOf_eq] at H_in
    rw [CollapsePoset.mem_compl_principalOpen_iff]
    exact ⟨x, H_mem, by rw [H_in]; exact H_neq⟩
  · intro H
    rw [CollapsePoset.mem_compl_principalOpen_iff] at H
    rcases H with ⟨x, H_mem, H_neq⟩
    exact ⟨⟨⟨x, g x⟩, H_mem, H_neq⟩, by
      rw [singletonCollapsePoset_principalOpen']; simp⟩

@[simp] lemma principalOpen_isClosed {p : CollapsePoset X Y (Order.succ ℵ₀)} :
    IsClosed (CollapsePoset.principalOpen p) := by
  rcases compl_principalOpen_isUnion one_lt_aleph0_succ p with ⟨_, s, Hu⟩
  rw [← isOpen_compl_iff, ← Hu]
  exact isOpen_iUnion (fun i => principalOpen_isOpen)

@[simp] lemma principalOpen_isRegular {p : CollapsePoset X Y (Order.succ ℵ₀)} :
    IsRegularOpen (CollapsePoset.principalOpen p) :=
  isRegularOpen_of_isClopen ⟨principalOpen_isClosed, principalOpen_isOpen⟩







@[simp] lemma isRegular_singletonPrincipalOpen {x : X} {y : Y} :
    IsRegularOpen (CollapsePoset.principalOpen
      (singletonCollapsePoset x y one_lt_aleph0_succ)) :=
  principalOpen_isRegular

@[simp] lemma isRegular_setOf {x : X} {y : Y} :
    IsRegularOpen {g : X → Y | g x = y} := by
  rw [← singletonCollapsePoset_principalOpen (hκ := one_lt_aleph0_succ)]
  exact isRegular_singletonPrincipalOpen



end CollapseSpaceLemmas

/-! ## Section omega_closed_dense_subset (src lines 768-797) -/

section OmegaClosedDense

variable {α : Type*} [NontrivialCompleteBooleanAlgebra α]











end OmegaClosedDense

/-! ## Section collapse_algebra (src lines 800-812) -/

/-- The collapse algebra: regular opens of X → Y with the collapse topology.
    Port of collapse_algebra (src line 805). -/
noncomputable def CollapseAlgebra (X Y : Type u) : Type u :=
  @RegularOpens (X → Y) (collapseSpace X Y)

variable {X Y : Type u}

/-- CollapseAlgebra is a NontrivialCompleteBooleanAlgebra when X → Y is nonempty.
    Port of collapse_algebra_boolean_algebra (src line 809). -/
noncomputable instance collapseAlgebra_ncba [Nonempty (X → Y)] :
    NontrivialCompleteBooleanAlgebra (CollapseAlgebra X Y) :=
  @RegularOpens.instNontrivialCBA (X → Y) (collapseSpace X Y) ‹_›

/-! ## Section collapse_poset_dense (src lines 814-906) -/

section CollapsePosetDense



/-- Inclusion of a collapse poset into the collapse algebra.
    Port of collapse_poset.inclusion (src line 817). -/
noncomputable def collapseInclusion (p : CollapsePoset X Y (Order.succ ℵ₀)) :
    CollapseAlgebra X Y :=
  ⟨CollapsePoset.principalOpen p, principalOpen_isRegular⟩

local notation "ι" => collapseInclusion











end CollapsePosetDense

/-! ## Final: collapse_boolean_algebra (src lines 910-916) -/



end Flypitch


end CohenSource_Collapse


/- Source module: Definitions.Flypitch4.Compactness -/
section CohenSource_Compactness
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/compactness.lean -/



set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace Fol

universe u v

variable {L : Language.{u}}

/-! ## list_except -/



/-! ## image_lift -/





/-! ## proof_compactness -/

/-- Any proof from a set of formulas is provable from a finite subset. -/
lemma proof_compactness {ψ : formula L} {T : Set (formula L)} :
    (T ⊢' ψ) → ∃ Γ : Finset (formula L), (↑Γ : Set (formula L)) ⊢' ψ ∧ ↑Γ ⊆ T := by
  haveI : DecidableEq (formula L) := fun x y => Classical.propDecidable _
  intro ⟨P⟩
  induction P with
  | axm h =>
    rename_i _ A₀
    exact ⟨{A₀}, ⟨prf.axm (by simp)⟩, by simp [h]⟩
  | impI _ ih =>
    obtain ⟨Γ, H, K⟩ := ih
    rename_i _ A₀ _ _
    refine ⟨Γ \ {A₀}, impI' (weakening' ?_ H), ?_⟩
    · simp only [Finset.coe_sdiff, Finset.coe_singleton]
      exact Set.subset_insert_diff_singleton A₀ ↑Γ
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton] at hx
      rcases K (Finset.mem_coe.mpr hx.1) with rfl | h
      · exact absurd rfl hx.2
      · exact h
  | impE _ _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, H₁, K₁⟩ := ih₁
    obtain ⟨Γ₂, H₂, K₂⟩ := ih₂
    refine ⟨Γ₁ ∪ Γ₂, ?_, ?_⟩
    · apply impE' _
      · exact weakening' (by simp only [Finset.coe_union]; exact Set.subset_union_left) H₁
      · exact weakening' (by simp only [Finset.coe_union]; exact Set.subset_union_right) H₂
    · simp only [Finset.coe_union]; exact Set.union_subset K₁ K₂
  | falsumE _ ih =>
    obtain ⟨Γ, H, K⟩ := ih
    rename_i _ A₀ _
    refine ⟨Γ \ {∼A₀}, falsumE' (weakening' ?_ H), ?_⟩
    · simp only [Finset.coe_sdiff, Finset.coe_singleton]
      exact Set.subset_insert_diff_singleton (∼A₀) ↑Γ
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton] at hx
      rcases K (Finset.mem_coe.mpr hx.1) with rfl | h
      · exact absurd rfl hx.2
      · exact h
  | allI _ ih =>
    obtain ⟨Γ, H, K⟩ := ih
    rw [Finset.subset_set_image_iff] at K
    obtain ⟨Γ', K', hΓ⟩ := K
    subst hΓ
    rw [Finset.coe_image] at H
    exact ⟨Γ', allI' H, K'⟩
  | allE₂ _ _ _ ih =>
    obtain ⟨Γ, H, K⟩ := ih
    exact ⟨Γ, allE₂' H, K⟩
  | ref =>
    exact ⟨∅, ref' _ _, by simp⟩
  | subst₂ _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, H₁, K₁⟩ := ih₁
    obtain ⟨Γ₂, H₂, K₂⟩ := ih₂
    refine ⟨Γ₁ ∪ Γ₂, ?_, ?_⟩
    · apply subst₂' _ _ _
      · exact weakening' (by simp only [Finset.coe_union]; exact Set.subset_union_left) H₁
      · exact weakening' (by simp only [Finset.coe_union]; exact Set.subset_union_right) H₂
    · simp only [Finset.coe_union]; exact Set.union_subset K₁ K₂

/-- Any proof from a sentence theory is provable from a finite sub-theory. -/
lemma theory_proof_compactness {T : SentTheory L} {ψ : sentence L} (hψ : T ⊢ₛ' ψ) :
    ∃ Γ : Finset (sentence L), (SentTheory.sprovable (↑Γ) ψ) ∧ (↑Γ : SentTheory L) ⊆ T := by
  haveI : DecidableEq (sentence L) := fun x y => Classical.propDecidable _
  haveI : DecidableEq (formula L) := fun x y => Classical.propDecidable _
  rcases proof_compactness hψ with ⟨Γ, H, K⟩
  rw [Finset.subset_set_image_iff] at K
  obtain ⟨Γ', K', hΓ⟩ := K
  subst hΓ
  rw [Finset.coe_image] at H
  exact ⟨Γ', H, K'⟩



/-! ## sprf_by_cases -/



/-! ## is_consistent_union -/



end Fol


end CohenSource_Compactness


/- Source module: Definitions.Flypitch4.Completion -/
section CohenSource_Completion
set_option autoImplicit false
/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/completion.lean — every consistent theory extends to a complete one -/




set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace Fol

universe u v

variable {L : Language.{u}}

/-! ## Helper lemmas at the sentence level -/

/-- A sentence-level axiom rule: if ψ ∈ T (as a SentTheory), then T ⊢ₛ' ψ -/
lemma saxm' {T : SentTheory L} {ψ : sentence L} (h : ψ ∈ T) : T ⊢ₛ' ψ :=
  ⟨prf.axm (Set.mem_image_of_mem _ h)⟩



/-- snot_and_self: from T ⊢ₛ' ψ and T ⊢ₛ' ∼ᵇψ, derive T ⊢ₛ' bd_falsum -/
lemma snot_and_self'' {T : SentTheory L} {ψ : sentence L}
    (H₁ : T ⊢ₛ' ψ) (H₂ : T ⊢ₛ' bd_not ψ) : T ⊢ₛ' bd_falsum :=
  -- bd_not ψ = bd_imp ψ bd_falsum, so (bd_not ψ).fst = ψ.fst ⟹ ⊥'
  impE' _ H₂ H₁





/-! ## Helper: (insert ψ T).fst = insert ψ.fst T.fst -/

 lemma sentTheory_insert_fst (ψ : sentence L) (T : SentTheory L) :
    (insert ψ T).fst = insert ψ.fst T.fst := by
  simp [SentTheory.fst, Set.image_insert_eq]

 lemma sentTheory_insert_bd_not_fst (ψ : sentence L) (T : SentTheory L) :
    (insert (bd_not ψ) T).fst = insert (∼ψ.fst) T.fst := by
  simp only [SentTheory.fst, Set.image_insert_eq, bounded_preformula.fst_bd_not]

/-! ## consis_not_of_not_provable and inconsis_not_of_provable -/

/-- If T ⊬ₛ' f, then T ∪ {∼ᵇf} is consistent -/
lemma consis_not_of_not_provable {T : SentTheory L} {f : sentence L}
    (h : ¬ T ⊢ₛ' f) : (insert (bd_not f) T).is_consistent := by
  simp only [SentTheory.is_consistent]
  intro hc
  apply h
  rw [sentTheory_insert_bd_not_fst] at hc
  exact falsumE' hc



/-- If T ∪ {∼ᵇf} is inconsistent, then T ⊢ₛ' f -/
lemma provable_of_inconsis_not {T : SentTheory L} {f : sentence L}
    (h : ¬ (insert (bd_not f) T).is_consistent) : T ⊢ₛ' f := by
  by_contra hnot
  exact h (consis_not_of_not_provable hnot)

/-! ## can_extend: one of T ∪ {ψ} or T ∪ {∼ᵇψ} is consistent -/

/-- Given a consistent theory T and a sentence ψ, either T ∪ {ψ} or T ∪ {∼ᵇψ} is consistent -/
lemma can_extend (T : SentTheory L) (ψ : sentence L) (h : T.is_consistent) :
    (insert ψ T).is_consistent ∨ (insert (bd_not ψ) T).is_consistent := by
  by_contra hall
  simp only [not_or] at hall
  obtain ⟨H1, H2⟩ := hall
  have hnotpsi : T ⊢ₛ' bd_not ψ := by
    simp only [SentTheory.is_consistent, not_not] at H1
    rw [sentTheory_insert_fst] at H1
    simp only [SentTheory.sprovable, SentTheory.fst, bd_not, bounded_preformula.fst]
    exact impI' H1
  have hpsi : T ⊢ₛ' ψ := provable_of_inconsis_not H2
  exact h (snot_and_self'' hpsi hnotpsi)

/-! ## Theory_over: the poset of consistent extensions of T -/

/-- Theory_over T hT: the subtype of SentTheory L consisting of consistent theories ⊇ T -/
def Theory_over (T : SentTheory L) (hT : T.is_consistent) : Type u :=
  { T' : SentTheory L // T ⊆ T' ∧ T'.is_consistent }

/-- T itself is a Theory_over T hT -/
def over_self (T : SentTheory L) (hT : T.is_consistent) : Theory_over T hT :=
  ⟨T, le_refl _, hT⟩

/-- Subset order on Theory_over T hT -/
def Theory_over_subset {T : SentTheory L} {hT : T.is_consistent} :
    Theory_over T hT → Theory_over T hT → Prop :=
  fun T1 T2 => T1.val ⊆ T2.val

instance {T : SentTheory L} {hT : T.is_consistent} : HasSubset (Theory_over T hT) :=
  ⟨Theory_over_subset⟩

instance {T : SentTheory L} {hT : T.is_consistent} : Nonempty (Theory_over T hT) :=
  ⟨over_self T hT⟩

/-! ## consis_limit: the limit of a chain is consistent -/

-- Helper: Theory_over_subset is transitive


-- Helper: move from one theory's fst to another's via subset
 lemma TO_fst_subset {T : SentTheory L} {hT : T.is_consistent}
    {a b : Theory_over T hT} (h : Theory_over_subset a b)
    {f : formula L} (hf : f ∈ a.val.fst) : f ∈ b.val.fst := by
  simp only [SentTheory.fst, Set.mem_image] at hf ⊢
  obtain ⟨s, hs, rfl⟩ := hf
  exact ⟨s, h hs, rfl⟩

/-- The union of a chain of consistent extensions of T is consistent -/
lemma consis_limit {T : SentTheory L} {hT : T.is_consistent}
    (Ts : Set (Theory_over T hT)) (h_chain : IsChain Theory_over_subset Ts) :
    (T ∪ ⋃₀ (Subtype.val '' Ts)).is_consistent := by
  simp only [SentTheory.is_consistent]
  intro h_inconsis
  by_cases hne : Ts.Nonempty
  · haveI : DecidableEq (formula L) := fun x y => Classical.propDecidable _
    obtain ⟨Γ, H_prov, H_sub⟩ := proof_compactness h_inconsis
    -- Each formula in Γ is in T.fst or in some T_f ∈ Ts
    have h_wit : ∀ f ∈ (Γ : Set (formula L)), f ∈ T.fst ∨
        ∃ Tf : Theory_over T hT, Tf ∈ Ts ∧ f ∈ Tf.val.fst := by
      intro f hf
      rcases H_sub hf with ⟨s, hs | ⟨t, ⟨Tf, hTf, rfl⟩, hst⟩, rfl⟩
      · exact Or.inl ⟨s, hs, rfl⟩
      · exact Or.inr ⟨Tf, hTf, ⟨s, hst, rfl⟩⟩
    -- Key: ∃ T_max ∈ Ts, (Γ : Set (formula L)) ⊆ T_max.val.fst
    -- By Finset.induction on Γ, merging witnesses using the chain
    have key : ∀ (S : Finset (formula L)),
        (∀ f ∈ (S : Set (formula L)), f ∈ T.fst ∨
          ∃ Tf : Theory_over T hT, Tf ∈ Ts ∧ f ∈ Tf.val.fst) →
        ∃ T_max : Theory_over T hT, T_max ∈ Ts ∧
          (S : Set (formula L)) ⊆ T_max.val.fst := by
      intro S
      induction S using Finset.induction with
      | empty =>
          intro _; obtain ⟨m, hm⟩ := hne; exact ⟨m, hm, by simp⟩
      | insert a s hnotmem ih =>
          intro hfw
          have hfw_s : ∀ g ∈ (s : Set (formula L)), g ∈ T.fst ∨
              ∃ Tf : Theory_over T hT, Tf ∈ Ts ∧ g ∈ Tf.val.fst :=
            fun g hg => hfw g (Set.mem_of_mem_of_subset hg
              (Finset.coe_subset.mpr (Finset.subset_insert a s)))
          obtain ⟨T_prev, hT_prev, hs_sub⟩ := ih hfw_s
          rcases hfw a (Finset.mem_coe.mpr (Finset.mem_insert_self a s)) with haT | ⟨Tf, hTf, haTf⟩
          · -- a ∈ T.fst ⊆ T_prev.fst (since T ⊆ T_prev)
            refine ⟨T_prev, hT_prev, by
              simp only [Finset.coe_insert]
              intro g hg
              rcases Set.mem_insert_iff.mp hg with rfl | hg'
              · simp only [SentTheory.fst, Set.mem_image] at haT ⊢
                obtain ⟨s', hs', rfl⟩ := haT
                exact ⟨s', T_prev.property.1 hs', rfl⟩
              · exact hs_sub hg'⟩
          · -- a ∈ Tf.fst; merge T_prev and Tf using the chain
            rcases eq_or_ne T_prev Tf with rfl | hne_TPTf
            · -- T_prev = Tf
              exact ⟨T_prev, hT_prev, by
                simp only [Finset.coe_insert]
                intro g hg
                rcases Set.mem_insert_iff.mp hg with rfl | hg'
                · exact haTf
                · exact hs_sub hg'⟩
            · -- T_prev ≠ Tf: use chain to compare
              rcases h_chain hT_prev hTf hne_TPTf with h | h
              · -- Theory_over_subset T_prev Tf: Tf is bigger
                exact ⟨Tf, hTf, by
                  simp only [Finset.coe_insert]
                  intro g hg
                  rcases Set.mem_insert_iff.mp hg with rfl | hg'
                  · exact haTf
                  · exact TO_fst_subset h (hs_sub hg')⟩
              · -- Theory_over_subset Tf T_prev: T_prev is bigger
                exact ⟨T_prev, hT_prev, by
                  simp only [Finset.coe_insert]
                  intro g hg
                  rcases Set.mem_insert_iff.mp hg with rfl | hg'
                  · exact TO_fst_subset h haTf
                  · exact hs_sub hg'⟩
    obtain ⟨T_max, _, hΓ_sub⟩ := key Γ h_wit
    exact T_max.property.2 (weakening' hΓ_sub H_prov)
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    apply hT
    have : (T ∪ ⋃₀ ((fun a : Theory_over T hT => a.val) '' (∅ : Set (Theory_over T hT)))).fst =
        T.fst := by simp [SentTheory.fst]
    exact this ▸ h_inconsis

/-! ## limit_theory: build the limit as a Theory_over -/

/-- Given a chain of consistent extensions, their union is a consistent extension -/
noncomputable def limit_theory {T : SentTheory L} {hT : T.is_consistent}
    (Ts : Set (Theory_over T hT)) (h_chain : IsChain Theory_over_subset Ts) :
    Σ' (T_lim : Theory_over T hT), ∀ T' ∈ Ts, T'.val ⊆ T_lim.val := by
  refine ⟨⟨T ∪ ⋃₀ (Subtype.val '' Ts), ?_, consis_limit Ts h_chain⟩, ?_⟩
  · exact Set.subset_union_left
  · intro T' hT' ψ hψ
    apply Set.mem_union_right
    refine ⟨T'.val, ?_, hψ⟩
    exact Set.mem_image_of_mem Subtype.val hT'

/-! ## can_use_zorn -/

/-- The poset of theories over T satisfies Zorn's hypotheses -/
lemma can_use_zorn {T : SentTheory L} {hT : T.is_consistent} :
    (∀ c : Set (Theory_over T hT), IsChain Theory_over_subset c →
      ∃ ub : Theory_over T hT, ∀ a ∈ c, a ⊆ ub) ∧
    (∀ (a b c : Theory_over T hT),
      Theory_over_subset a b → Theory_over_subset b c → Theory_over_subset a c) :=
  ⟨fun c h_chain => ⟨(limit_theory c h_chain).fst, (limit_theory c h_chain).snd⟩,
   fun _a _b _c hab hbc => fun x hx => hbc (hab hx)⟩

/-! ## maximal_extension -/

/-- Given a consistent theory T, there is a maximal consistent extension of T -/
noncomputable def maximal_extension (T : SentTheory L) (hT : T.is_consistent) :
    Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max := by
  have htrans : ∀ {a b c : Theory_over T hT},
      Theory_over_subset a b → Theory_over_subset b c → Theory_over_subset a c :=
    fun hab hbc => can_use_zorn.2 _ _ _ hab hbc
  have h_zorn : ∃ m : Theory_over T hT, ∀ a : Theory_over T hT,
      Theory_over_subset m a → Theory_over_subset a m :=
    @exists_maximal_of_chains_bounded (Theory_over T hT) Theory_over_subset
      can_use_zorn.1 @htrans
  exact ⟨h_zorn.choose, fun T' hT1 => h_zorn.choose_spec T' (fun x hx => hT1 hx)⟩

/-! ## cannot_extend_maximal_extension -/

/-- A maximal extension cannot be consistently extended by any new sentence -/
lemma cannot_extend_maximal_extension {T : SentTheory L} {hT : T.is_consistent}
    (T_max' : Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max)
    (ψ : sentence L)
    (H : (insert ψ T_max'.fst.val).is_consistent)
    (H1 : ψ ∉ T_max'.fst.val) : False := by
  have T_over_T : T ⊆ T_max'.fst.val := T_max'.fst.property.1
  let T_bad : Theory_over T hT :=
    ⟨insert ψ T_max'.fst.val,
     fun x hx => Set.mem_insert_of_mem ψ (T_over_T hx),
     H⟩
  have h_sub : Theory_over_subset T_max'.fst T_bad :=
    fun x hx => Set.mem_insert_of_mem ψ hx
  have h_max : Theory_over_subset T_bad T_max'.fst := T_max'.snd T_bad h_sub
  exact H1 (h_max (Set.mem_insert ψ T_max'.fst.val))

/-! ## is_complete for SentTheory -/

/-- A SentTheory is complete if it is consistent and every sentence or its negation is in it -/
def SentTheory.is_complete (T : SentTheory L) : Prop :=
  T.is_consistent ∧ ∀ ψ : sentence L, ψ ∈ T ∨ bd_not ψ ∈ T

/-! ## complete_maximal_extension_of_consis -/

/-- The maximal extension of a consistent theory is complete -/
lemma complete_maximal_extension_of_consis {T : SentTheory L} {hT : T.is_consistent} :
    (maximal_extension T hT).fst.val.is_complete := by
  refine ⟨(maximal_extension T hT).fst.property.right, ?_⟩
  intro ψ
  by_cases hmem : ψ ∈ (maximal_extension T hT).fst.val
  · exact Or.inl hmem
  · apply Or.inr
    by_contra hnot
    have hT_max_consis := (maximal_extension T hT).fst.property.right
    rcases can_extend (maximal_extension T hT).fst.val ψ hT_max_consis with h | h
    · exact cannot_extend_maximal_extension _ ψ h hmem
    · exact cannot_extend_maximal_extension _ (bd_not ψ) h hnot

/-! ## completion_of_consis -/

/-- Every consistent theory has a complete extension -/
noncomputable def completion_of_consis (T : SentTheory L) (h_consis : T.is_consistent) :
    Σ' (T' : Theory_over T h_consis), T'.val.is_complete :=
  ⟨(maximal_extension T h_consis).fst, complete_maximal_extension_of_consis⟩

end Fol


end CohenSource_Completion


