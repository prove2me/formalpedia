-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ea40934c-a951-5bbf-bd5c-cb16c4c05bf3

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral
import Theorems.Thm_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped Classical

namespace FACT

variable (F : Type) [Field F] [NumberField F]

scoped instance : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))
scoped instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
scoped instance : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := inferInstance
scoped instance : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
scoped instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
scoped instance : LocallyCompactSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := inferInstance

theorem continuous_archEntries : Continuous (archEntries F) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

namespace IsArchTestFactor

private theorem _root_.FACT.IsArchTestFactor.continuous {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) :
    Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := h
  have : fa = Φ ∘ archEntries F := funext hfa
  rw [this]
  exact hΦ.continuous.comp (continuous_archEntries F)

end IsArchTestFactor
p2m_export "FACT" "IsArchTestFactor.continuous"

theorem IsArchTestFactor.const_mul {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) (c : ℂ) :
    IsArchTestFactor F (fun x => c * fa x) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩ := h
  refine ⟨⟨fun M => c * Φ M, contDiff_const.mul hΦ, fun x => by show c * fa x = c * Φ (archEntries F x); rw [hfa]⟩, ?_⟩
  exact hsupp.mul_left

end FACT
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv.FACT"

open FACT in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (f f' : AdelicGL2 (𝓞 F) F → ℂ) (tys tys' : ArchTypeFamily F)
    (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hf' : IsFactorizableTestFn F f') (hbf' : IsArchBiFinite F tys' f') :
    ∃ tys'' : ArchTypeFamily F,
      IsFactorizableTestFn F (rightConv F f' (fun x => f x⁻¹)) ∧
      IsArchBiFinite F tys'' (rightConv F f' (fun x => f x⁻¹)) := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨hfc', hfs'⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f' hf'
  obtain ⟨tys'', hb⟩ := AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv F f f' tys tys' hfc hfs hbf hfc' hfs' hbf'
  refine ⟨tys'', ?_, hb⟩
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  obtain ⟨fa', ff', hfa', hff', hf'eq⟩ := hf'

  letI mA : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  letI mF : MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := borel _
  haveI : BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := ⟨rfl⟩
  set μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haar with hμa
  set μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := Measure.haar with hμf
  obtain ⟨c, hc, hsplit⟩ := NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral F μa μf
  set Ca : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun x => ∫ a, fa' (x * a) * fa a⁻¹ ∂μa with hCa
  set Cf : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ := fun x => ∫ b, ff' (x * b) * ff b⁻¹ ∂μf with hCf
  have hconv : rightConv F f' (fun x => f x⁻¹) =
      fun z => ((c : ℂ) * Ca (glArch (𝓞 F) F z)) * Cf (glFin (𝓞 F) F z) := by
    funext z
    have hint : (fun y => f' (z * y) * f y⁻¹) =
        fun y => (fun a => fa' (glArch (𝓞 F) F z * a) * fa a⁻¹) (glArch (𝓞 F) F y) *
          (fun b => ff' (glFin (𝓞 F) F z * b) * ff b⁻¹) (glFin (𝓞 F) F y) := by
      funext y
      simp only [hf'eq, hfeq, map_mul, map_inv]
      ring
    rw [rightConv_apply]
    show (∫ y, f' (z * y) * f y⁻¹ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) = _
    rw [hint]
    have hs := hsplit (fun a => fa' (glArch (𝓞 F) F z * a) * fa a⁻¹) (fun b => ff' (glFin (𝓞 F) F z * b) * ff b⁻¹)
    rw [hs]
    simp only [hCa, hCf]
    ring
  rw [hconv]
  refine ⟨fun x => (c : ℂ) * Ca x, Cf, ?_, ?_, fun z => rfl⟩
  · have h1 := AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport F μa fa'
      (fun a => fa a⁻¹) hfa' ((IsArchTestFactor.continuous F hfa).comp continuous_inv)
      (hfa.2.comp_homeomorph (Homeomorph.inv _))
    exact IsArchTestFactor.const_mul F h1 c
  · exact AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport F μf ff'
      (fun b => ff b⁻¹) hff' (hff.2.comp_homeomorph (Homeomorph.inv _))

end S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv (solution)
