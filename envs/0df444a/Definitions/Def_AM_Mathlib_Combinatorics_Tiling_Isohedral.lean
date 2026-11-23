-- Prove2me | Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
-- name    : AM_Mathlib_Combinatorics_Tiling_Isohedral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:02:58.241797+00:00
-- url     : https://prove2.me/theorems/45572b07-070e-41c8-baca-4fadaabf8e89
-- title:
--   Isohedral
-- statement:
--   Definitions and structural lemmas for Isohedral, from jsm28/AperiodicMonotilesLean contributors (see pinned LICENSE and source headers)'s pinned Periodicity and isohedrality of tilings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_apply
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_const
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_toTileSetFunction
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_empty
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_of_subsingleton
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_univ_iff
public import Theorems.Thm_DiscreteTiling_TileSet_mem_smul_iff_smul_inv_mem
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_mem_symmetryGroup_smul_iff
public import Theorems.Thm_DiscreteTiling_TileSet_smul_mem_of_mem_of_mem_symmetryGroup
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
public import Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_reindex_iff_of_surjective
public import Theorems.Thm_P2M_DiscreteTiling_TileSet_mem_symmetryGroup_smul_iff__0ea417755de9
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
attribute [local simp] DiscreteTiling.TileSet.unionEqUniv_reindex_iff_of_surjective
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
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
namespace TileSet
instance (t : TileSet ps ιₜ) : SMul t.symmetryGroup (t : Set (PlacedTile ps)) where
  smul g pt := ⟨(g : G) • ↑pt, smul_mem_of_mem_of_mem_symmetryGroup g.property pt.property⟩
lemma coe_symmetryGroup_smul (t : TileSet ps ιₜ) (g : t.symmetryGroup)
    (pt : (t : Set (PlacedTile ps))) : ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) =
      g • (pt : PlacedTile ps) :=
  rfl
instance (t : TileSet ps ιₜ) : MulAction t.symmetryGroup (t : Set (PlacedTile ps)) where
  __ : SMul t.symmetryGroup (t : Set (PlacedTile ps)) := inferInstance
  one_smul pt := by
    simp [Subtype.ext_iff, coe_symmetryGroup_smul]
  mul_smul x y pt := by
    simp [Subtype.ext_iff, coe_symmetryGroup_smul, mul_smul]
def smulOrbitEquiv (g : G) (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient (g • t).symmetryGroup
      ((g • t : TileSet ps ιₜ) : Set (PlacedTile ps)) ≃
        MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps)) where
  toFun pt := Quotient.liftOn' pt
    (fun x ↦ ⟦⟨g⁻¹ • ↑x, mem_smul_iff_smul_inv_mem.1 x.property⟩⟧)
    (fun x y h ↦ by
      convert Quotient.eq''.2 ?_
      rw [MulAction.orbitRel_apply] at h ⊢
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff] at h
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff]
      rcases h with ⟨a, ha, haa⟩
      change a • (y : PlacedTile ps) = x at haa
      refine ⟨g⁻¹ * a * g, mem_symmetryGroup_smul_iff'.1 ha, ?_⟩
      change (g⁻¹ * a * g) • (g⁻¹ • (y : PlacedTile ps)) = g⁻¹ • ↑x
      simpa [mul_smul] using haa)
  invFun pt := Quotient.liftOn' pt
    (fun x ↦ ⟦⟨g • ↑x, (smul_mem_smul_iff g).2 x.property⟩⟧)
    (fun x y h ↦ by
      convert Quotient.eq''.2 ?_
      rw [MulAction.orbitRel_apply] at h ⊢
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff] at h
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff]
      rcases h with ⟨a, ha, haa⟩
      change a • (y : PlacedTile ps) = x at haa
      refine ⟨g * a * g⁻¹, (mem_symmetryGroup_smul_iff g).2 ha, ?_⟩
      change (g * a * g⁻¹) • (g • (y : PlacedTile ps)) = g • ↑x
      simpa [mul_smul] using haa)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert rfl
    simp
  right_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert rfl
    simp
def isohedralNumber : TileSetFunction ps Cardinal ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦
    #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))),
  by
    refine fun {ιₜ ιₜ'} (f t) ↦
      Cardinal.eq.2 ⟨Quotient.congr (Equiv.setCongr (by simp)) fun x y ↦ ?_⟩
    simp_rw [MulAction.orbitRel_apply]
    simp only [MulAction.mem_orbit_iff, Subtype.exists, symmetryGroup_reindex,
               Equiv.setCongr_apply, Subtype.ext_iff]
    exact Iff.rfl,
  fun {ιₜ g} (t _) ↦ Cardinal.eq.2 ⟨smulOrbitEquiv g t⟩⟩
def isohedralNumberNat : TileSetFunction ps ℕ ⊤ := isohedralNumber.comp Cardinal.toNat
def subMulActionTilePoint (t : TileSet ps ιₜ) :
    SubMulAction t.symmetryGroup (Prod (t : Set (PlacedTile ps)) X) where
  carrier := {x | x.2 ∈ (x.1 : PlacedTile ps)}
  smul_mem' g x h := by
    rcases x with ⟨pt, x⟩
    simp only [Prod.smul_mk, Set.mem_ofPred_eq, coe_symmetryGroup_smul, Subgroup.smul_def] at h ⊢
    exact (PlacedTile.smul_mem_smul_iff ↑g).2 h
instance (t : TileSet ps ιₜ) : MulAction t.symmetryGroup
    {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} :=
  SubMulAction.SMulMemClass.toMulAction (S' := subMulActionTilePoint t)
def quotientPlacedTileOfquotientTilePoint (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} →
        MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps)) :=
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  Quot.mapRight (MulAction.orbitRel_le_fst _ _ _) ∘
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  (Quotient.congrRight <| Setoid.ext_iff.1 <|
    SubMulAction.orbitRel_of_subMul t.subMulActionTilePoint)
def quotientPointOfquotientTilePoint (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} →
        MulAction.orbitRel.Quotient t.symmetryGroup X :=
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  Quot.mapRight (MulAction.orbitRel_le_snd _ _ _) ∘
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  (Quotient.congrRight <| Setoid.ext_iff.1 <|
    SubMulAction.orbitRel_of_subMul t.subMulActionTilePoint)
end TileSet
namespace Protoset
variable {H : Subgroup G}
variable (ιₜ) in
/-- The minimum number of orbits of tiles in any `TileSet ps ιₜ` that satisfies the property `p`. -/
def isohedralNumber (p : TileSetFunction ps Prop H) : Cardinal :=
  ⨅ (t : {x : TileSet ps ιₜ // p x}), TileSet.isohedralNumber (t : TileSet ps ιₜ)
variable (ιₜ) in
/-- The minimum number of orbits of tiles in any `TileSet ps ιₜ` that satisfies the property `p`,
as a natural number; zero if infinite or if no such `TileSet` exists. -/
def isohedralNumberNat (p : TileSetFunction ps Prop H) : ℕ :=
  Cardinal.toNat <| isohedralNumber ιₜ p
end Protoset
end DiscreteTiling


