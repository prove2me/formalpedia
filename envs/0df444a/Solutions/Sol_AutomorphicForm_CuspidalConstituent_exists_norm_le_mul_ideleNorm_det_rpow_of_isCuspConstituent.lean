-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/77f77bf6-93da-54d3-8666-00cc1daeb3f9

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm~det_centralScalar P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"
open AutomorphicForm.CuspidalConstituent NumberField.TateGlobal
open scoped NNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 centralScalar finiteAdelicGL2Subgroup lsXiMemberAt_iff ArchTypeFamily archCutSubmodule exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc"
p2m_open "AutomorphicForm~det_centralScalar"

namespace RegBdd

variable (K : Type) [Field K] [NumberField K]

theorem rightTranslate_one (φ : AdelicGL2 (𝓞 K) K → ℂ) : rightTranslate K 1 φ = φ := by
  funext x; simp [rightTranslate]

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K)).det = _
  rw [Matrix.det_fin_two]
  simp

theorem main
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖y g‖ ≤ M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) := by

  obtain ⟨x', hx', α, hα, -, -, hyeq⟩ :=
    exists_eq_rightConv_of_mem_cut K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys y hy

  have hx'V : x' ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx').1).1
  obtain ⟨hx'cont, hx'sm⟩ :=
    continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K _ _ _ ξ x' (hV.1.le hx'V)
  have hx'cusp := (hx'sm 1).1
  rw [rightTranslate_one] at hx'cusp
  obtain ⟨M, hM⟩ := exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc K c u d₁ d₂ T hd hcov ξ x' hx'cusp hx'cont
    α hα 1 1 one_pos

  have hyV : y ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1
  obtain ⟨-, hysm⟩ :=
    continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K _ _ _ ξ y (hV.1.le hyV)
  have hycusp := (hysm 1).1
  rw [rightTranslate_one] at hycusp
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  have hls := ((lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ y).mp hycusp.1).1
  have hcent : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g :=
    fun z g => hls.central_transform ⟨z, Subgroup.mem_top z⟩ g

  obtain ⟨sec, -, hsec, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
  refine ⟨M, fun g => ?_⟩
  set r : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det g) with hr_def
  have hr : 0 < r := ideleNorm_pos _
  have hρpos : 0 < r ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hr _
  have hρne : (⟨r ^ (-(1 / 2 : ℝ)), hρpos.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    exact hρpos.ne' h'
  set ρ : ℝ≥0ˣ := Units.mk0 (⟨r ^ (-(1 / 2 : ℝ)), hρpos.le⟩ : ℝ≥0) hρne with hρ
  set z : (AdeleRing (𝓞 K) K)ˣ := sec ρ with hz_def
  have hz : ideleNorm K z = r ^ (-(1 / 2 : ℝ)) := by
    rw [hz_def, hsec]; rfl
  have hdet : ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * g)) = 1 := by
    rw [map_mul, det_centralScalar, ideleNorm_mul, ideleNorm_mul, hz, ← hr_def, ← Real.rpow_add hr,
      show (-(1 / 2 : ℝ)) + -(1 / 2 : ℝ) = -1 by ring, Real.rpow_neg_one, inv_mul_cancel₀ hr.ne']
  have hb := hM (centralScalar (𝓞 K) K z * g) ⟨le_of_eq hdet.symm, le_of_eq hdet⟩
  rw [← hyeq, hcent z g, norm_mul, hξ z, hz] at hb
  have hpow : ((r ^ (-(1 / 2 : ℝ))) ^ w₀ : ℝ) = (r ^ (w₀ / 2))⁻¹ := by
    rw [← Real.rpow_mul hr.le, ← Real.rpow_neg hr.le]
    congr 1
    ring
  have hpos : 0 < r ^ (w₀ / 2) := Real.rpow_pos_of_pos hr _
  rw [hpow] at hb
  calc ‖y g‖ = r ^ (w₀ / 2) * ((r ^ (w₀ / 2))⁻¹ * ‖y g‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ ≤ r ^ (w₀ / 2) * M := mul_le_mul_of_nonneg_left hb hpos.le
    _ = M * r ^ (w₀ / 2) := mul_comm _ _

end RegBdd

end AutomorphicForm

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖y g‖ ≤ M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) :=
  AutomorphicForm.RegBdd.main K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV y hy w₀ hξ

end S_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent (solution)
