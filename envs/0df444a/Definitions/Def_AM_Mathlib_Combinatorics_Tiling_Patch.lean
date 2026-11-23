-- Prove2me | Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
-- name    : AM_Mathlib_Combinatorics_Tiling_Patch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:12:16.06194+00:00
-- url     : https://prove2.me/theorems/99e436d0-88f8-49fd-952d-dbf715e38902
-- title:
--   Patch
-- statement:
--   Definitions and structural lemmas for Patch, from jsm28/AperiodicMonotilesLean contributors (see pinned LICENSE and source headers)'s pinned Periodicity and isohedrality of tilings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_apply
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_const
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_toTileSetFunction
public import Theorems.Thm_DiscreteTiling_TileSet_DisjointOn_reindex_of_injective
public import Theorems.Thm_DiscreteTiling_TileSet_Disjoint_reindex_of_injective
public import Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersectionsOn_reindex_of_injective
public import Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersections_reindex_of_injective
public import Theorems.Thm_DiscreteTiling_TileSet_card_reindex_of_equivLike
public import Theorems.Thm_DiscreteTiling_TileSet_card_smul
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_empty
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_of_subsingleton
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_univ_iff
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.card_reindex_of_equivLike
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_empty
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_univ_iff
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_apply
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction


set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
namespace DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
namespace TileSet
protected def subtype (t : TileSet ps ιₜ) (p : ιₜ → Prop) : TileSet ps (Subtype p) :=
  t.reindex Subtype.val
@[simp] lemma coe_subtype (t : TileSet ps ιₜ) (p : ιₜ → Prop) : ↑(t.subtype p) = ↑t ∘ Subtype.val :=
  rfl
@[simp] lemma subtype_apply (t : TileSet ps ιₜ) (p : ιₜ → Prop) (i : Subtype p) :
    t.subtype p i = t i :=
  rfl
protected lemma Disjoint.subtype {t : TileSet ps ιₜ} (hd : t.Disjoint) (p : ιₜ → Prop) :
    (t.subtype p).Disjoint :=
  TileSet.Disjoint.reindex_of_injective hd Subtype.val_injective
protected lemma FiniteIntersections.subtype {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) (p : ιₜ → Prop) :
    (t.subtype p).FiniteIntersections :=
  FiniteIntersections.reindex_of_injective hfi Subtype.val_injective
protected lemma FiniteDistinctIntersections.subtype {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersections) (p : ιₜ → Prop) :
    (t.subtype p).FiniteDistinctIntersections :=
  FiniteDistinctIntersections.reindex hfi
def patch (t : TileSet ps ιₜ) (s : Set X) :
    TileSet ps (Subtype (fun i ↦ (s ∩ t i).Nonempty)) :=
  t.subtype _
@[simp] lemma coe_patch (t : TileSet ps ιₜ) (s : Set X) : ↑(t.patch s) = ↑t ∘ Subtype.val :=
  t.coe_subtype _
@[simp] lemma patch_apply (t : TileSet ps ιₜ) (s : Set X) (i) :
    t.patch s i = t i :=
  t.subtype_apply _ _
lemma patch_reindex_subtypeEquiv (t : TileSet ps ιₜ) (s : Set X) (e : ιₜ' ≃ ιₜ) :
    (t.patch s).reindex (Equiv.subtypeEquiv e fun _ ↦ Iff.rfl) = (t.reindex e).patch s :=
  rfl
@[simp] lemma card_patch_reindex_of_equivLike (t : TileSet ps ιᵤ) (s : Set X) (e : Eᵤ) :
    ((t.reindex e).patch s).card = (t.patch s).card := by
  change ((t.reindex (e : ιᵤ' ≃ ιᵤ)).patch s).card = _
  rw [← patch_reindex_subtypeEquiv]
  exact card_reindex_of_equivLike _ _
def smulPatchEquiv (g : G) (t : TileSet ps ιₜ) (s : Set X) :
    {i // (g • s ∩ ((g • t) i)).Nonempty} ≃ {i // (s ∩ t i).Nonempty} :=
  Equiv.subtypeEquivRight (by simp)
lemma smul_patch (g : G) (t : TileSet ps ιₜ) (s : Set X) :
    (g • (t.patch s)).reindex (smulPatchEquiv g t s) = (g • t).patch (g • s) :=
  rfl
@[simp] lemma card_smul_patch (g : G) (t : TileSet ps ιₜ) (s : Set X) :
    ((g • t).patch (g • s)).card = g • (t.patch s).card := by
  rw [← smul_patch, ← card_smul, card_reindex_of_equivLike]
lemma Disjoint.patch {t : TileSet ps ιₜ} (hd : TileSet.Disjoint t) (s : Set X) :
    TileSet.Disjoint (t.patch s) :=
  TileSet.Disjoint.subtype hd _
protected lemma FiniteIntersections.patch {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) (s : Set X) :
    (t.patch s).FiniteIntersections :=
  FiniteIntersections.subtype hfi _
protected lemma FiniteDistinctIntersections.patch {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersections) (s : Set X) :
    (t.patch s).FiniteDistinctIntersections :=
  FiniteDistinctIntersections.subtype hfi _
def patchPatchEquiv (t : TileSet ps ιₜ) {s₁ s₂ : Set X} (h : s₂ ⊆ s₁) :
    {i // (s₂ ∩ t.patch s₁ i).Nonempty} ≃ {i // (s₂ ∩ t i).Nonempty} where
  toFun i := ⟨↑↑i, by exact i.property⟩
  invFun i := ⟨⟨↑i, i.property.mono <| by gcongr⟩, i.property⟩
  left_inv := by simp [LeftInverse]
  right_inv := by simp [Function.RightInverse, LeftInverse]
end TileSet
end DiscreteTiling


