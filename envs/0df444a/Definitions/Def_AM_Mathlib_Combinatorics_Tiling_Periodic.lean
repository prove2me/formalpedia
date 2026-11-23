-- Prove2me | Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
-- name    : AM_Mathlib_Combinatorics_Tiling_Periodic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:06:22.697576+00:00
-- url     : https://prove2.me/theorems/76eb58c4-07b2-488f-ab6c-2581555c1b85
-- title:
--   Periodic
-- statement:
--   Definitions and structural lemmas for Periodic, from jsm28/AperiodicMonotilesLean contributors (see pinned LICENSE and source headers)'s pinned Periodicity and isohedrality of tilings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
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
public import Theorems.Thm_DiscreteTiling_TileSet_isTilingOf_empty
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_mem_symmetryGroup_smul_iff
public import Theorems.Thm_DiscreteTiling_TileSet_quotientPlacedTileOfquotientTilePoint_apply_mk
public import Theorems.Thm_DiscreteTiling_TileSet_quotientPointOfquotientTilePoint_apply_mk
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_smul
public import Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_reindex_iff_of_surjective
public import Theorems.Thm_P2M_DiscreteTiling_TileSet_mem_symmetryGroup_smul_iff__0ea417755de9
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_empty
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_univ_iff
attribute [local simp] DiscreteTiling.TileSet.isTilingOf_empty
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.quotientPlacedTileOfquotientTilePoint_apply_mk
attribute [local simp] DiscreteTiling.TileSet.quotientPointOfquotientTilePoint_apply_mk
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
open scoped Cardinal Nat Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
namespace TileSet
def StronglyPeriodic : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ Finite <| MulAction.orbitRel.Quotient t.symmetryGroup X,
   by
     refine fun {ιₜ ιₜ'} (f t) ↦ ?_
     simp only [eq_iff_iff]
     refine Equiv.finite_iff (Quotient.congrRight fun x y ↦ ?_)
     simp [MulAction.orbitRel_apply, MulAction.mem_orbit_iff],
   by
     refine fun {ιₜ g} (t _) ↦ ?_
     simp only [eq_iff_iff]
     refine Equiv.finite_iff (Quotient.congr (MulAction.toPerm g⁻¹) fun x y ↦ ?_)
     simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.exists,
       MulAction.toPerm_apply]
     refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
     · rcases ha with ⟨ha, rfl⟩
       rw [mem_symmetryGroup_smul_iff'] at ha
       exact ⟨g⁻¹ * a * g, ha, by simp [mul_smul]⟩
     · rcases ha with ⟨ha, ha'⟩
       rw [← mem_symmetryGroup_smul_iff g] at ha
       simp only [Subgroup.mk_smul] at ha'
       exact ⟨g * a * g⁻¹, ha, by simp [mul_smul, ha']⟩⟩
def WeaklyPeriodic (n : ℕ) : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦
     ∃ f : (Fin n → Multiplicative ℤ) →* t.symmetryGroup, Injective f,
   by
     refine fun {ιₜ ιₜ'} (e t) ↦ ?_
     simp only [eq_iff_iff]
     refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
     · refine ⟨(MulEquiv.subgroupCongr (t.symmetryGroup_reindex e.symm)).toMonoidHom.comp f, ?_⟩
       simpa [Injective] using hf
     · refine ⟨(MulEquiv.subgroupCongr (t.symmetryGroup_reindex e.symm).symm).toMonoidHom.comp f,
               ?_⟩
       simpa [Injective] using hf,
   by
     refine fun {ιₜ g} (t _) ↦ ?_
     simp only [eq_iff_iff]
     refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
     · refine ⟨((MulEquiv.subgroupCongr (t.symmetryGroup_smul g)).trans
         (Subgroup.equivSMul _ _).symm).toMonoidHom.comp f, ?_⟩
       simpa [Injective] using hf
     · refine ⟨((Subgroup.equivSMul _ _).trans
         (MulEquiv.subgroupCongr (t.symmetryGroup_smul g).symm)).toMonoidHom.comp f, ?_⟩
       simpa [Injective] using hf⟩
end TileSet
namespace Protoset
variable {H : Subgroup G}
variable (ιₜ) in
/-- Whether `ps` is weakly aperiodic (for `TileSet ps ιₜ` that satisfy the property `p`); that is,
whether it has such a `TileSet`, but none is strongly periodic. -/
def WeaklyAperiodic (p : TileSetFunction ps Prop H) : Prop :=
  (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, p t → ¬ t.StronglyPeriodic
variable (ιₜ) in
/-- Whether `ps` is strongly aperiodic (for `TileSet ps ιₜ` that satisfy the property `p`); that
is, whether it has such a `TileSet`, but none is weakly periodic. -/
def StronglyAperiodic (p : TileSetFunction ps Prop H) : Prop :=
  (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, p t → ¬ t.WeaklyPeriodic 1
end Protoset
end DiscreteTiling


