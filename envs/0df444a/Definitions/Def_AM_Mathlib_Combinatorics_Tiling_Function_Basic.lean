-- Prove2me | Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
-- name    : AM_Mathlib_Combinatorics_Tiling_Function_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T05:55:09.036622+00:00
-- url     : https://prove2.me/theorems/67fd9a43-ddb1-4090-bb7f-7261995d7f8a
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from jsm28/AperiodicMonotilesLean contributors (see pinned LICENSE and source headers)'s pinned Periodicity and isohedrality of tilings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective


set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
namespace DiscreteTiling
open Function
open scoped Pointwise
variable {G X Y ιₚ : Type*} [Group G] [MulAction G X] [MulAction G Y]
universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ α β γ : Type*}
variable {H : Subgroup G}
variable [EquivLike Eᵤ ιᵤ' ιᵤ]
section
variable (Y ps α H) in
/-- A `TileSetFunction ps α H` is a function from `TileSet ps ιₜ` to `α` that is invariant under
change or permutation of index type `ιₜ` (within the same universe) and under the action of group
elements in `H`. -/
@[ext] structure TileSetFunction where
  /-- The function.  Use the coercion to a function rather than using `toFun` directly. -/
  toFun : {ιₜ : Type u} → TileSet ps ιₜ → α
  /-- The function is invariant under reindexing. -/
  reindex_eq' : ∀ {ιₜ ιₜ' : Type u} (f : ιₜ ≃ ιₜ') (t : TileSet ps ιₜ),
    toFun (t.reindex f.symm) = toFun t
  /-- The function is invariant under the group action within the subgroup `H`. -/
  smul_eq : ∀ {ιₜ : Type u} {g : G} (t : TileSet ps ιₜ), g ∈ H → toFun (g • t) = toFun t
variable (Y ps α H) in
/-- A `VarTileSetFunction Y ps α H` is a function from `Y` and `TileSet ps ιₜ` to `α` that is
invariant under change or permutation of index type `ιₜ` (within the same universe) and under the
action (on both arguments) of group elements in `H`. -/
@[ext] structure VarTileSetFunction where
  /-- The function.  Use the coercion to a function rather than using `toFun` directly. -/
  toFun : {ιₜ : Type u} → Y → TileSet ps ιₜ → α
  /-- The function is invariant under reindexing. -/
  reindex_eq' : ∀ {ιₜ ιₜ' : Type u} (f : ιₜ ≃ ιₜ') (y : Y) (t : TileSet ps ιₜ),
    toFun y (t.reindex f.symm) = toFun y t
  /-- The function is invariant under the group action within the subgroup `H`. -/
  smul_eq : ∀ {ιₜ : Type u} {g : G} (y : Y) (t : TileSet ps ιₜ), g ∈ H →
    toFun (g • y) (g • t) = toFun y t
end
namespace TileSetFunction
instance : CoeFun (TileSetFunction ps α H) (fun _ ↦ {ιₜ : Type*} → TileSet ps ιₜ → α) where
  coe := toFun
attribute [coe] toFun
attribute [simp] smul_eq
@[simp] lemma reindex_eq (f : TileSetFunction ps α H) (t : TileSet ps ιᵤ) (e : Eᵤ) :
    f (t.reindex e) = f t :=
  f.reindex_eq' (EquivLike.toEquiv e).symm t
@[simp] lemma reindex_eq_of_bijective (f : TileSetFunction ps α H) (t : TileSet ps ιᵤ)
    {e : ιᵤ' → ιᵤ} (h : Bijective e) : f (t.reindex e) = f t :=
  f.reindex_eq t <| Equiv.ofBijective e h
@[simp, norm_cast] lemma coe_inj {f₁ f₂ : TileSetFunction ps α H} :
    (@f₁ : {ιₜ : Type*} → TileSet ps ιₜ → α) = f₂ ↔ f₁ = f₂ :=
  TileSetFunction.ext_iff.symm
variable (ps H) in
/-- The constant `TileSetFunction`. -/
protected def const (a : α) : TileSetFunction ps α H :=
  ⟨fun {ιₜ} ↦ const (TileSet ps ιₜ) a, by simp, by simp⟩
variable (H) in
@[simp] lemma const_apply (a : α) (t : TileSet ps ιₜ) : TileSetFunction.const ps H a t = a := rfl
instance [Nonempty α] : Nonempty (TileSetFunction ps α H) :=
  ⟨TileSetFunction.const ps H <| Classical.arbitrary _⟩
protected def comp (f : TileSetFunction ps α H) (fab : α → β) : TileSetFunction ps β H :=
  ⟨fab ∘ f.toFun, by simp, fun _ hg ↦ by simp [hg]⟩
@[simp] lemma comp_apply (f : TileSetFunction ps α H) (fab : α → β) (t : TileSet ps ιₜ) :
    f.comp fab t = fab (f t) :=
  rfl
protected def comp₂ (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H) (fabg : α → β → γ) :
    TileSetFunction ps γ H :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ fabg (f t) (f' t), by simp, fun _ hg ↦ by simp [hg]⟩
@[simp] lemma comp₂_apply (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H)
    (fabg : α → β → γ) (t : TileSet ps ιₜ) : f.comp₂ f' fabg t = fabg (f t) (f' t) :=
  rfl
protected def ofLE {H' : Subgroup G} (h : H' ≤ H) :
    TileSetFunction ps α H ↪ TileSetFunction ps α H' where
  toFun f := ⟨f.toFun, by simp, fun _ hg ↦ by simp [SetLike.le_def.1 h hg]⟩
  inj' f f' h := by simpa using h
@[simp] lemma ofLE_apply (f : TileSetFunction ps α H) {H' : Subgroup G} (h : H' ≤ H)
    (t : TileSet ps ιₜ) : f.ofLE h t = f t :=
  rfl
variable (ps) in
@[simp] lemma ofLE_const (a : α) {H' : Subgroup G} (h : H' ≤ H) :
    (TileSetFunction.const ps H a).ofLE h = TileSetFunction.const ps H' a :=
  rfl
end TileSetFunction
namespace VarTileSetFunction
instance : CoeFun (VarTileSetFunction Y ps α H) (fun _ ↦ {ιₜ : Type*} → Y → TileSet ps ιₜ → α) where
  coe := toFun
attribute [coe] toFun
attribute [simp] smul_eq
@[simp] lemma reindex_eq (f : VarTileSetFunction Y ps α H) (y : Y) (t : TileSet ps ιᵤ) (e : Eᵤ) :
    f y (t.reindex e) = f y t :=
  f.reindex_eq' (EquivLike.toEquiv e).symm y t
@[simp] lemma reindex_eq_of_bijective (f : VarTileSetFunction Y ps α H) (y : Y) (t : TileSet ps ιᵤ)
    {e : ιᵤ' → ιᵤ} (h : Bijective e) : f y (t.reindex e) = f y t :=
  f.reindex_eq y t <| Equiv.ofBijective e h
@[simp, norm_cast] lemma coe_inj {f₁ f₂ : VarTileSetFunction Y ps α H} :
    (@f₁ : {ιₜ : Type*} → Y → TileSet ps ιₜ → α) = f₂ ↔ f₁ = f₂ :=
  VarTileSetFunction.ext_iff.symm
variable (Y ps H) in
/-- The constant `VarTileSetFunction`. -/
protected def const (a : α) : VarTileSetFunction Y ps α H :=
  ⟨fun {ιₜ} ↦ const Y (const (TileSet ps ιₜ) a), by simp, by simp⟩
variable (H) in
@[simp] lemma const_apply (a : α) (y : Y) (t : TileSet ps ιₜ) :
    VarTileSetFunction.const Y ps H a y t = a :=
  rfl
instance [Nonempty α] : Nonempty (VarTileSetFunction Y ps α H) :=
  ⟨VarTileSetFunction.const Y ps H <| Classical.arbitrary _⟩
protected def comp (f : VarTileSetFunction Y ps α H) (fab : α → β) : VarTileSetFunction Y ps β H :=
  ⟨fun y ↦ fab ∘ (f.toFun y), by simp, fun _ _ hg ↦ by simp [hg]⟩
@[simp] lemma comp_apply (f : VarTileSetFunction Y ps α H) (fab : α → β) (y : Y)
    (t : TileSet ps ιₜ) : f.comp fab y t = fab (f y t) :=
  rfl
protected def comp₂ (f : VarTileSetFunction Y ps α H) (f' : VarTileSetFunction Y ps β H)
    (fabg : α → β → γ) : VarTileSetFunction Y ps γ H :=
  ⟨fun {ιₜ : Type*} (y : Y) (t : TileSet ps ιₜ) ↦ fabg (f y t) (f' y t),
   by simp,
   fun _ _ hg ↦ by simp [hg]⟩
@[simp] lemma comp₂_apply (f : VarTileSetFunction Y ps α H) (f' : VarTileSetFunction Y ps β H)
    (fabg : α → β → γ) (y : Y) (t : TileSet ps ιₜ) : f.comp₂ f' fabg y t = fabg (f y t) (f' y t) :=
  rfl
protected def ofLE (f : VarTileSetFunction Y ps α H) {H' : Subgroup G} (h : H' ≤ H) :
    VarTileSetFunction Y ps α H' :=
  ⟨f.toFun, by simp, fun _ _ hg ↦ by simp [SetLike.le_def.1 h hg]⟩
@[simp] lemma ofLE_apply (f : VarTileSetFunction Y ps α H) {H' : Subgroup G} (h : H' ≤ H)
    (y : Y) (t : TileSet ps ιₜ) : f.ofLE h y t = f y t :=
  rfl
variable (Y ps) in
@[simp] lemma ofLE_const (a : α) {H' : Subgroup G} (h : H' ≤ H) :
    (VarTileSetFunction.const Y ps H a).ofLE h = VarTileSetFunction.const Y ps H' a :=
  rfl
def toTileSetFunction (f : VarTileSetFunction Y ps α H) (y : Y) :
    TileSetFunction ps α (H ⊓ MulAction.stabilizer G y) :=
  ⟨f.toFun y,
   by simp,
   fun {ιₜ} {g} t hg ↦ by
     nth_rewrite 1 [← MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hg).2]
     rw [smul_eq _ _ _ (Subgroup.mem_inf.1 hg).1]⟩
@[simp] lemma toTileSetFunction_apply (f : VarTileSetFunction Y ps α H) (y : Y)
    (t : TileSet ps ιₜ) : f.toTileSetFunction y t = f y t :=
  rfl
variable (ps H) in
@[simp] lemma toTileSetFunction_const (a : α) (y : Y) :
    (VarTileSetFunction.const Y ps H a).toTileSetFunction y = TileSetFunction.const ps _ a :=
  rfl
end VarTileSetFunction
namespace TileSetFunction
variable (Y) in
/-- Converting a `TileSetFunction ps α H` to a `VarTileSetFunction Y ps α H` that ignores its
first argument. -/
def toVarTileSetFunction (f : TileSetFunction ps α H) : VarTileSetFunction Y ps α H :=
  ⟨fun {ιₜ} ↦ const Y f.toFun, by simp, fun _ _ hg ↦ by simp [hg]⟩
end TileSetFunction
end DiscreteTiling


