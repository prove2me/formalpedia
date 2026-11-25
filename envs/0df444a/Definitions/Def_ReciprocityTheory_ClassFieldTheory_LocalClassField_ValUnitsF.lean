-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsF
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsF
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:44.439308+00:00
-- url     : https://prove2.me/theorems/95d3813c-e7eb-482a-ac9e-1fcc1807266d
-- title:
--   Val Units F
-- statement:
--   Definitions and structural lemmas for Val Units F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsF.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
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
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
theorem rpow_neg_div_nonneg (i : ℕ) : 0 ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _
def UKi (i : ℕ) : Subgroup Kˣ where
  carrier := {x | x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K)}
  one_mem' := ⟨(UK p K).one_mem, by
    show ‖(((1 : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    simp only [Units.val_one, OneMemClass.coe_one, sub_self, norm_zero]
    exact rpow_neg_div_nonneg p K i⟩
  mul_mem' := fun {x y} hx hy => ⟨(UK p K).mul_mem hx.1 hy.1, by
    have hx1 : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx.1
    have h : (((x * y : Kˣ) : K) : PadicAlgCl p) - 1 =
        ((x : K) : PadicAlgCl p) * (((y : K) : PadicAlgCl p) - 1) + (((x : K) : PadicAlgCl p) - 1) := by
      rw [Units.val_mul, MulMemClass.coe_mul]; ring
    show ‖(((x * y : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    rw [h]
    refine (PadicAlgCl.isNonarchimedean p _ _).trans (max_le ?_ hx.2)
    rw [norm_mul, hx1, one_mul]; exact hy.2⟩
  inv_mem' := fun {x} hx => ⟨(UK p K).inv_mem hx.1, by
    have hx1 : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx.1
    have hx0 := coe_units_ne_zero x
    have h : (((x⁻¹ : Kˣ) : K) : PadicAlgCl p) - 1 =
        - ((((x : K) : PadicAlgCl p) - 1) * ((x : K) : PadicAlgCl p)⁻¹) := by
      rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      field_simp
      ring
    show ‖(((x⁻¹ : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    rw [h, norm_neg, norm_mul, norm_inv, hx1, inv_one, mul_one]; exact hx.2⟩
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


