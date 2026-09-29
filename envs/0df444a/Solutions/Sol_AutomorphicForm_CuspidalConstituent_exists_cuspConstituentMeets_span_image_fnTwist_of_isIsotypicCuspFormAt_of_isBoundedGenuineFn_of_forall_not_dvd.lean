-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_cuspConstituentMeets_span_image_fnTwist_of_isIsotypicCuspFormAt_of_isBoundedGenuineFn_of_forall_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/25a87da6-2650-5b34-aaa8-739785f0bc2c

import Mathlib
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist
import Theorems.Thm_LanglandsTunnell_exists_smoothCuspRealizationAt_fnTwist_gaussSumFn_centreCut
import Theorems.Thm_LanglandsTunnell_isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_cuspConstituentMeets_span_image_fnTwist_of_isIsotypicCuspFormAt_of_isBoundedGenuineFn_of_forall_not_dvd
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace P2mS28R7m

variable (F : Type) [Field F] [NumberField F]

theorem glArch_finLift (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : glArch (𝓞 F) F (GaussTwist.finLift g) = 1 := by
  ext i j
  rw [Units.val_one]
  rfl

theorem gaussTrans_mem_finiteAdelicGL2Subgroup (𝔣 : Ideal (𝓞 F)) (u : GaussTwist.GaussIndex F 𝔣) :
    GaussTwist.gaussTrans F 𝔣 u ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact glArch_finLift F _

theorem gaussSumFn_eq_sum_smul_rightTranslate (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    GaussTwist.gaussSumFn F η 𝔣 φ = ∑ u : GaussTwist.GaussIndex F 𝔣,
      GaussTwist.gaussWt F η 𝔣 u • rightTranslate F (GaussTwist.gaussTrans F 𝔣 u) φ := by
  funext g
  rw [GaussTwist.gaussSumFn_apply, Finset.sum_apply]
  rfl

theorem gaussSumFn_mem {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hV : IsCuspSubrep F pins ξ V) (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ V) : GaussTwist.gaussSumFn F η 𝔣 φ ∈ V := by
  rw [gaussSumFn_eq_sum_smul_rightTranslate]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _
    (hV.rightTranslate_fin_mem _ (gaussTrans_mem_finiteAdelicGL2Subgroup F 𝔣 u) φ hφ)

variable {F}

theorem isLsXiFunction_gaussSumFn {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) : IsLsXiFunction (𝓞 F) F Z ξ (GaussTwist.gaussSumFn F η 𝔣 φ) where
  left_invariant γ g := by
    simp only [GaussTwist.gaussSumFn_apply, mul_assoc, hφ.left_invariant]
  central_transform z g := by
    simp only [GaussTwist.gaussSumFn_apply, mul_assoc, hφ.central_transform, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring

end P2mS28R7m

end

open P2mS28R7m in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSN : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ¬ v.asIdeal ∣ N) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφV : φ ∈ V) (hφ0 : φ ≠ 0)
    (hφ : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ)
    (hbg : IsBoundedGenuineFn F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (NumberField.StandardAddChar.stdAddChar F) φ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (𝔣 : Ideal (𝓞 F)) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      (twistedCentralChar F _ ξ η)
      (Submodule.span ℂ ((fun φ => fnTwist F η φ) '' (V : Set (AdelicGL2 (𝓞 F) F → ℂ)))) ∧
    ∃ 𝔣₀ : Ideal (𝓞 F), 𝔣₀ ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣₀ ∧
      ∃ Ψ' : HeckeEigensystem F ℂ,
        Ψ'.level = N * 𝔣₀ ^ 2 ∧
        (∀ v : HeightOneSpectrum (𝓞 F),
          Ψ'.a v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * Ψ.a v ∧
          Ψ'.b v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) ^ 2 * Ψ.b v) ∧
        ∀ S' : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ S' → (∀ v, v ∉ S' → ¬ v.asIdeal ∣ 𝔣₀) →
          CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F))
            (twistedCentralChar F _ ξ η) (N * 𝔣₀ ^ 2) S' Ψ'
            (Submodule.span ℂ ((fun φ => fnTwist F η φ) '' (V : Set (AdelicGL2 (𝓞 F) F → ℂ)))) := by
  classical
  refine ⟨AutomorphicForm.CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist F _ _ _ _ ξ η hη V hV, ?_⟩

  let Ψ₀ : HeckeEigensystem F ℂ := ⟨N, hN, Ψ.a, Ψ.b⟩
  let R : SmoothCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Ψ₀.toRawCentral :=
    { toFun := φ
      exists_ne_zero := Function.ne_iff.mp hφ0
      centralChar := ξ
      smoothCusp := hφ.smoothCusp
      level_invariant := hφ.level_invariant
      exceptionalSet := S
      hecke_eigen := hφ.hecke_eigen
      central_eigen := hφ.central_eigen }
  have hR : IsBoundedGenuineCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) (NumberField.StandardAddChar.stdAddChar F) Ψ₀.toRawCentral R := hbg
  obtain ⟨𝔣₀, h𝔣₀, hmod₀, -, Φ', hlev, hab, R₁, hR₁fun, hR₁bg⟩ :=
    LanglandsTunnell.exists_smoothCuspRealizationAt_fnTwist_gaussSumFn_centreCut F c u d₁ d₂ T hc hd₁ Ψ₀ R hR η hη 𝔣 hmod
  refine ⟨𝔣₀, h𝔣₀, hmod₀, Φ', hlev, hab, fun S' hSS' hS'𝔣 => ⟨R₁.toFun, ?_, ?_, ?_⟩⟩
  ·
    rw [hR₁fun]
    exact Submodule.subset_span ⟨_, gaussSumFn_mem F hV.1 η 𝔣₀ hφV, rfl⟩
  · obtain ⟨g, hg⟩ := R₁.exists_ne_zero
    exact Function.ne_iff.mpr ⟨g, hg⟩
  ·
    obtain ⟨⟨haut₁, hcusp₁⟩, hkf₁⟩ := R₁.smoothCusp
    have hcont : Continuous R₁.toFun := hR₁bg.1
    refine ⟨⟨⟨?_, hcusp₁⟩, hkf₁⟩, hcont, ?_, ?_, ?_⟩
    ·
      letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).mS
      have h₁ := (lsXiMemberAt_iff (𝓞 F) F _ _ _ _ R₁.toFun).mp haut₁

      have hφaut := (lsXiMemberAt_iff (𝓞 F) F _ _ _ _ φ).mp hφ.smoothCusp.1.1
      refine (lsXiMemberAt_iff (𝓞 F) F _ _ _ _ R₁.toFun).mpr ⟨?_, h₁.2⟩
      rw [hR₁fun]
      exact isLsXiFunction_fnTwist F η hη.isIdeleClassChar (isLsXiFunction_gaussSumFn η 𝔣₀ hφaut.1)
    ·
      intro g k hk
      have hlev' : Φ'.toRawCentral.level = N * 𝔣₀ ^ 2 := hlev
      have := R₁.level_invariant g k (by rw [hlev']; exact hk)
      exact this
    ·
      intro v hvS'
      have hvS : v ∉ S := fun h => hvS' (hSS' h)
      have hvN : ¬ v.asIdeal ∣ N := hSN v hvS
      have hv𝔣 : ¬ v.asIdeal ∣ 𝔣₀ := hS'𝔣 v hvS'
      have hvdvd : ¬ v.asIdeal ∣ N * 𝔣₀ ^ 2 := by
        intro h
        rcases (v.prime.dvd_mul).mp h with h | h
        · exact hvN h
        · exact hv𝔣 (v.prime.dvd_of_dvd_pow h)
      have heig := LanglandsTunnell.isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn F N η 𝔣₀ hmod₀ v hvdvd hφ.level_invariant (hφ.hecke_eigen v hvS)
      rw [(hab v).1, hR₁fun]
      exact heig
    ·
      intro v hvS' g
      have hvS : v ∉ S := fun h => hvS' (hSS' h)
      have hgen : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).gen v = heckeGen (𝓞 F) F v := rfl
      have hRφ : R.toFun = φ := rfl
      rw [hR₁fun, hRφ, hgen, fnTwist_apply, fnTwist_apply, chiDet_centralScalar_mul]
      have hG : GaussTwist.gaussSumFn F η 𝔣₀ φ (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) * g) =
          Ψ.toRawCentral.b v * GaussTwist.gaussSumFn F η 𝔣₀ φ g := by
        simp only [GaussTwist.gaussSumFn_apply, mul_assoc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        have hce := hφ.central_eigen v hvS (g * GaussTwist.gaussTrans F 𝔣₀ w)
        rw [hgen] at hce
        rw [hce]
        ring
      have hb : Φ'.toRawCentral.b v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) ^ 2 * Ψ.toRawCentral.b v := by
        show (HeckeEigensystem.cNorm v)⁻¹ * Φ'.b v = _ ^ 2 * ((HeckeEigensystem.cNorm v)⁻¹ * Ψ.b v)
        rw [(hab v).2]
        show _ * (_ * Ψ.b v) = _
        ring
      rw [hG, hb]
      ring

end S_AutomorphicForm_CuspidalConstituent_exists_cuspConstituentMeets_span_image_fnTwist_of_isIsotypicCuspFormAt_of_isBoundedGenuineFn_of_forall_not_dvd
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_cuspConstituentMeets_span_image_fnTwist_of_isIsotypicCuspFormAt_of_isBoundedGenuineFn_of_forall_not_dvd (solution)
