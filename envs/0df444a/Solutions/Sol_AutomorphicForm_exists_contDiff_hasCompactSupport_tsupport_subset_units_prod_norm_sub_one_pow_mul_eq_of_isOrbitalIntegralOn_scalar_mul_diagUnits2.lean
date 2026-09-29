-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/036996d5-23a4-5ed6-87c1-06278960d264

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_pow_mul_integral_integral_unipotentGL2_eq_of_isArchTestFactor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure] :
    ∃ Φ : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φ p ≠ 0 →
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
          IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ Ca,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (u z : (InfiniteAdeleRing K)ˣ), (∀ w : InfinitePlace K, (u : InfiniteAdeleRing K) w ≠ 1) →
        ∀ (τ : Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
          (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
              ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
                ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa I →
            ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
              Φ ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K (z : InfiniteAdeleRing K)] := by
  classical
  letI mA : MeasurableSpace (InfiniteAdeleRing K) := borel _
  haveI : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩
  let lam : Measure (InfiniteAdeleRing K) := Measure.addHaar
  let Kc : Subgroup (GL (Fin 2) (InfiniteAdeleRing K)) :=
    ⨅ w : InfinitePlace K, (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w)
  letI mK : MeasurableSpace Kc := borel _
  haveI : BorelSpace Kc := ⟨rfl⟩
  have hKc : IsCompact (Kc : Set (GL (Fin 2) (InfiniteAdeleRing K))) :=
    (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup K).2
  haveI : CompactSpace Kc := isCompact_iff_compactSpace.mp hKc
  let K₀ : TopologicalSpace.PositiveCompacts Kc := ⟨⟨Set.univ, isCompact_univ⟩, by simp [interior_univ]⟩
  let κ : Measure Kc := Measure.haarMeasure K₀
  obtain ⟨c, hc, hdesc⟩ :=
    AutomorphicForm.exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
      K ν hν lam ρ κ inferInstance
  obtain ⟨Φ, hΦ, hΦc, hΦu, ⟨Ca, hCa, hCamem⟩, hwin⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_pow_mul_integral_integral_unipotentGL2_eq_of_isArchTestFactor
      K lam κ inferInstance fa hfa
  refine ⟨fun p => (c : ℂ) * Φ p, contDiff_const.mul hΦ, hΦc.mul_left, fun p hp => hΦu p ?_, ⟨Ca, hCa, fun p hp => ?_⟩, ?_⟩
  · intro h
    exact hp (show (c : ℂ) * Φ p = 0 by rw [h, mul_zero])
  · exact hCamem p ((tsupport_mul_subset_right (f := fun _ : Fin 2 → mixedEmbedding.mixedSpace K => (c : ℂ)) (g := Φ)) hp)
  · intro u z hu τ hτ I hI
    show _ = (c : ℂ) * Φ _
    rw [hdesc fa hfa u z hu τ hτ I hI, ← hwin u z, mul_assoc]

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2 (solution)
