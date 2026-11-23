-- Prove2me | Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
-- name    : AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T05:56:46.420797+00:00
-- url     : https://prove2.me/theorems/e557a42e-62a2-4d3b-8927-222a069afcbb
-- title:
--   Disjoint
-- statement:
--   Definitions and structural lemmas for Disjoint, from jsm28/AperiodicMonotilesLean contributors (see pinned LICENSE and source headers)'s pinned Periodicity and isohedrality of tilings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_apply
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_const
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_toTileSetFunction
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_mem_def
public import Theorems.Thm_DiscreteTiling_TileSet_mem_inv_smul_iff_smul_mem
public import Theorems.Thm_DiscreteTiling_TileSet_mem_of_mem_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_mem_smul_apply_iff_smul_inv_mem
public import Theorems.Thm_DiscreteTiling_TileSet_mem_smul_iff_smul_inv_mem
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
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_apply
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction


set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
namespace DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' F : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
namespace TileSet
protected def Disjoint : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j),
   by
     intro ιₜ ιₜ' f t
     simp only [eq_iff_iff]
     convert EquivLike.pairwise_comp_iff f.symm _
     rfl,
   by simp [TileSet.smul_apply]⟩
protected lemma disjoint_iff {t : TileSet ps ιₜ} :
    t.Disjoint ↔ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j) :=
  Iff.rfl
@[simp] lemma disjoint_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    t.Disjoint := by
  simp [TileSet.disjoint_iff, Subsingleton.pairwise]
protected def DisjointOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ Pairwise fun i j ↦
     Disjoint ((t i : Set X) ∩ s) ((t j : Set X) ∩ s),
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     convert EquivLike.pairwise_comp_iff f.symm _
     rfl,
   by simp [TileSet.smul_apply, ← Set.smul_set_inter]⟩
protected lemma disjointOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    t.DisjointOn s ↔ Pairwise fun i j ↦ Disjoint ((t i : Set X) ∩ s) ((t j : Set X) ∩ s) :=
  Iff.rfl
@[simp] lemma disjointOn_of_subsingleton [Subsingleton ιₜ] (s : Set X) (t : TileSet ps ιₜ) :
    t.DisjointOn s := by
  simp [TileSet.disjointOn_iff, Subsingleton.pairwise]
lemma DisjointOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ} (hd : t.DisjointOn s₂)
    (hs : s₁ ⊆ s₂) : t.DisjointOn s₁ :=
  fun _ _ h ↦ Set.disjoint_of_subset (Set.inter_subset_inter_right _ hs)
    (Set.inter_subset_inter_right _ hs) (hd h)
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma disjointOn_empty (t : TileSet ps ιₜ) : t.DisjointOn ∅ := by
  simp [TileSet.DisjointOn, Pairwise]
@[simp] lemma disjointOn_univ_iff {t : TileSet ps ιₜ} :
    t.DisjointOn Set.univ ↔ t.Disjoint := by
  simp [TileSet.Disjoint, TileSet.DisjointOn]
def FiniteIntersections : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ ∀ x, {i | x ∈ t i}.Finite,
   by
     intro ιₜ ιₜ' f t
     refine forall_congr ?_
     simp only [eq_iff_iff]
     intro x
     convert Set.finite_image_iff (Set.injOn_of_injective (EquivLike.injective f)) using 2
     exact Equiv.setOfPred_apply_symm_eq_image_setOfPred f fun i ↦ x ∈ t i,
   by
     intro ιₜ g t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ by simpa using h (g • x), fun h ↦ fun x ↦ ?_⟩
     convert h (g⁻¹ • x) using 2
     ext i
     exact mem_smul_apply_iff_smul_inv_mem⟩
@[simp] lemma finiteIntersections_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    t.FiniteIntersections :=
  fun _ ↦ Set.subsingleton_of_subsingleton.finite
def FiniteIntersectionsOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ ∀ x ∈ s, {i | x ∈ t i}.Finite,
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     refine forall₂_congr (fun x _ ↦ ?_)
     convert Set.finite_image_iff (Set.injOn_of_injective (EquivLike.injective f)) using 2
     exact Equiv.setOfPred_apply_symm_eq_image_setOfPred f fun i ↦ x ∈ t i,
   by
     intro ιₜ g s t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ by simpa using h (g • x), fun h ↦ fun x hx ↦ ?_⟩
     convert h (g⁻¹ • x) (Set.mem_smul_set_iff_inv_smul_mem.1 hx) using 2
     ext i
     exact mem_smul_apply_iff_smul_inv_mem⟩
@[simp] lemma finiteIntersectionsOn_of_subsingleton [Subsingleton ιₜ] (s : Set X)
    (t : TileSet ps ιₜ) : t.FiniteIntersectionsOn s :=
  fun _ _ ↦ Set.subsingleton_of_subsingleton.finite
lemma FiniteIntersectionsOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersectionsOn s₂) (hs : s₁ ⊆ s₂) :
    t.FiniteIntersectionsOn s₁ :=
  fun x hx ↦ hfi x (Set.mem_of_mem_of_subset hx hs)
@[simp] lemma finiteIntersectionsOn_empty (t : TileSet ps ιₜ) :
    t.FiniteIntersectionsOn ∅ := by
  simp [TileSet.FiniteIntersectionsOn]
@[simp] lemma finiteIntersectionsOn_univ_iff {t : TileSet ps ιₜ} :
    t.FiniteIntersectionsOn Set.univ ↔ t.FiniteIntersections := by
  simp [TileSet.FiniteIntersections, TileSet.FiniteIntersectionsOn]
def FiniteDistinctIntersections : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ ∀ x, {pt | pt ∈ t ∧ x ∈ pt}.Finite,
   by simp,
   by
     intro ιₜ g t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ ?_, fun h ↦ fun x ↦ ?_⟩
     · convert h (g • x) using 0
       convert (Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g))).symm using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
         PlacedTile.mem_inv_smul_iff_smul_mem]
     · convert h (g⁻¹ • x) using 0
       convert Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g)) using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem]⟩
lemma FiniteDistinctIntersections.reindex {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersections) {e : ιₜ' → ιₜ} :
    (t.reindex e).FiniteDistinctIntersections := by
  refine fun x ↦ Set.Finite.subset (hfi x) ?_
  simp only [Set.ofPred_subset_ofPred, and_imp]
  exact fun _ h hx ↦ ⟨mem_of_mem_reindex h, hx⟩
lemma FiniteIntersections.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.FiniteIntersections) : t.FiniteDistinctIntersections := by
  intro x
  convert Set.Finite.image t (h x) using 1
  ext pt
  simp only [Set.mem_ofPred_eq, Set.mem_image, TileSet.mem_def]
  refine ⟨fun ⟨⟨i, hi⟩, hx⟩ ↦ ?_, fun ⟨i, ⟨hx, hi⟩⟩ ↦ ?_⟩
  · subst hi
    exact ⟨i, hx, rfl⟩
  · subst hi
    exact ⟨⟨i, rfl⟩, hx⟩
@[simp] lemma finiteDistinctIntersections_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (finiteIntersections_of_subsingleton t)
def FiniteDistinctIntersectionsOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ ∀ x ∈ s, {pt | pt ∈ t ∧ x ∈ pt}.Finite,
   by simp,
   by
     intro ιₜ g s t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x hx ↦ ?_, fun h ↦ fun x hx ↦ ?_⟩
     · convert h (g • x) (by simp [hx]) using 0
       convert (Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g))).symm using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
         PlacedTile.mem_inv_smul_iff_smul_mem]
     · convert h (g⁻¹ • x) (Set.mem_smul_set_iff_inv_smul_mem.1 hx) using 0
       convert Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g)) using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem]⟩
lemma FiniteDistinctIntersectionsOn.reindex {s : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersectionsOn s) {e : ιₜ' → ιₜ} :
    (t.reindex e).FiniteDistinctIntersectionsOn s := by
  refine fun x hx ↦ Set.Finite.subset (hfi x hx) ?_
  simp only [Set.ofPred_subset_ofPred, and_imp]
  exact fun _ h hx ↦ ⟨mem_of_mem_reindex h, hx⟩
end TileSet
end DiscreteTiling


