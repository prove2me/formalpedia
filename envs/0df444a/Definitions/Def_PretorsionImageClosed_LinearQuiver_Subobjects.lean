-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
-- name    : PretorsionImageClosed_LinearQuiver_Subobjects
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:06:39.933521+00:00
-- url     : https://prove2.me/theorems/c27e317d-6414-5fc8-9bf1-06e6719e6ae9
-- title:
--   Subobjects
-- statement:
--   Definitions and structural lemmas for Subobjects, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_comp
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_id
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_hom_ext_coord
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
def scalarHom (a d : Fin n) (r : k) : interval k a d ⟶ interval k a d where
  app i := ConcreteCategory.ofHom (r • (LinearMap.id : intervalSpace k a d i →ₗ[k] intervalSpace k a d i))
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k a d i) => ?_
    change r • inclusionOrZero k _ _ x = inclusionOrZero k _ _ (r • x)
    rw [map_smul]
theorem coord_scalarHom (a d : Fin n) (r : k) (i : Fin n) :
    coord (scalarHom a d r) i = r * coord (𝟙 (interval k a d)) i := by
  rw [coord_id]
  unfold coord
  change ((r • unit k a d i : intervalSpace k a d i) : k) = _
  rw [Submodule.coe_smul, unit_val, smul_eq_mul]
theorem scalarHom_comp_scalarHom (a d : Fin n) (r s : k) :
    scalarHom a d r ≫ scalarHom a d s = scalarHom a d (r * s) := by
  apply hom_ext_coord
  intro i
  rw [coord_comp, coord_scalarHom, coord_scalarHom, coord_scalarHom, coord_id]
  split_ifs <;> ring
theorem scalarHom_one (a d : Fin n) : scalarHom a d (1 : k) = 𝟙 _ := by
  apply hom_ext_coord
  intro i
  rw [coord_scalarHom, one_mul]
def scalarIso (a d : Fin n) {r : k} (hr : r ≠ 0) : interval k a d ≅ interval k a d where
  hom := scalarHom a d r
  inv := scalarHom a d r⁻¹
  hom_inv_id := by rw [scalarHom_comp_scalarHom, mul_inv_cancel₀ hr, scalarHom_one]
  inv_hom_id := by rw [scalarHom_comp_scalarHom, inv_mul_cancel₀ hr, scalarHom_one]
def suffix (a d ℓ : Fin n) (h : a ≤ ℓ) : Subobject (interval k a d) :=
  Subobject.mk (intervalIncl k d h)
end LinearQuiver
end PretorsionImageClosed


