-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:13.278663+00:00
-- url     : https://prove2.me/theorems/a4a89db3-b7ef-49b9-a437-0bc8aa34de29
-- title:
--   Val Units A
-- statement:
--   Definitions and structural lemmas for Val Units A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsA.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vOn_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe


set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K} in
theorem coe_units_ne_zero (x : Kˣ) : ((x : K) : PadicAlgCl p) ≠ 0 := fun h => x.ne_zero (Subtype.ext h)
variable {p K} in
theorem norm_units_pos (x : Kˣ) : 0 < ‖((x : K) : PadicAlgCl p)‖ := norm_pos_iff.2 (coe_units_ne_zero x)
theorem vK_spec (x : Kˣ) : (vK p K x : ℝ) = - (eK p K * Real.logb p ‖((x : K) : PadicAlgCl p)‖) := by
  unfold vK
  rw [vOn_spec, vbar_apply]
  show (eK p K : ℝ) * - Real.logb p ‖((x : K) : PadicAlgCl p)‖ = _
  ring
theorem vK_one : vK p K 1 = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec]; simp
theorem vK_mul (x y : Kˣ) : vK p K (x * y) = vK p K x + vK p K y := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add, vK_spec, vK_spec, vK_spec, Units.val_mul, MulMemClass.coe_mul, norm_mul,
    Real.logb_mul (norm_units_pos x).ne' (norm_units_pos y).ne']
  ring
def vKHom : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (vK p K x)
  map_one' := by rw [vK_one]; rfl
  map_mul' x y := by rw [vK_mul]; rfl
variable {K L}
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


