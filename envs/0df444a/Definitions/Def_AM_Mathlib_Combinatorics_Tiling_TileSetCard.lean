-- Prove2me | Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
-- name    : AM_Mathlib_Combinatorics_Tiling_TileSetCard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T05:55:12.442108+00:00
-- url     : https://prove2.me/theorems/81cc2e23-7d90-4cd2-9580-080ec6439e21
-- title:
--   Tile Set Card
-- statement:
--   Definitions and structural lemmas for Tile Set Card, from jsm28/AperiodicMonotilesLean contributors (see pinned LICENSE and source headers)'s pinned Periodicity and isohedrality of tilings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSetCard.lean

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Mathlib.SetTheory.Cardinal.Basic
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_injective
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
open scoped Cardinal Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ E F : Type*}
universe u v
variable {ιᵤ ιᵤ' : Type u} [EquivLike E ιᵤ' ιᵤ] [FunLike F ιᵤ' ιᵤ] [EmbeddingLike F ιᵤ' ιᵤ]
variable (ps) in
/-- A `TileSetCard ps` associates a `Cardinal` to each `PlacedTile ps`. This is a separate
definition rather than just using plain functions because of the action by `G`. The main
definition used for tilings is `TileSet`, which uses indexed families; this definition is
intended for use cases where it is convenient for `TileSet`s related by reindexing to be
equal. -/
@[ext] structure TileSetCard where
  /-- The number of each tile. Use the coercion to a function rather than using `tilesCard`
      directly. -/
  tilesCard : PlacedTile ps → Cardinal.{v}
namespace TileSetCard
instance : Inhabited (TileSetCard ps) := ⟨⟨0⟩⟩
instance : CoeFun (TileSetCard ps) (fun _ ↦ PlacedTile ps → Cardinal) where
  coe := tilesCard
attribute [coe] tilesCard
@[simp, norm_cast] lemma coe_inj {t₁ t₂ : TileSetCard ps} :
    (t₁ : PlacedTile ps → Cardinal) = t₂ ↔ t₁ = t₂ :=
  TileSetCard.ext_iff.symm
lemma coe_injective :
    Injective (TileSetCard.tilesCard : TileSetCard ps → PlacedTile ps → Cardinal) :=
  fun _ _ ↦ coe_inj.1
instance : Max (TileSetCard ps) :=
  ⟨fun t₁ t₂ ↦ ⟨↑t₁ ⊔ ↑t₂⟩⟩
instance : Min (TileSetCard ps) :=
  ⟨fun t₁ t₂ ↦ ⟨↑t₁ ⊓ ↑t₂⟩⟩
instance : PartialOrder (TileSetCard ps) :=
  PartialOrder.lift _ coe_injective
instance : DistribLattice (TileSetCard ps) :=
  coe_injective.distribLattice _ Iff.rfl Iff.rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
instance : MulAction G (TileSetCard ps) where
  smul g t := ⟨fun pt ↦ t (g⁻¹ • pt)⟩
  one_smul t := TileSetCard.ext <| funext <| fun pt ↦ by
    change t _ = _
    simp
  mul_smul g₁ g₂ t := TileSetCard.ext <| funext <| fun pt ↦ by
    change t _ = t _
    convert rfl using 2
    rw [mul_inv_rev, mul_smul]
end TileSetCard
namespace TileSet
protected def card (t : TileSet ps ιₜ) : TileSetCard ps :=
  ⟨fun pt ↦ #(t ⁻¹' {pt})⟩
end TileSet
end DiscreteTiling


