-- Prove2me | solution 1 for AutomorphicForm.exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/00d06986-1508-57d1-8df9-2a525edccfde

import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family_of_unitary
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass"
p2m_attr_erase "instance" "instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

namespace BoundMSkeleton

theorem rpow_le_pow_mul_one_add_pow {x H k₂ e : ℝ} {N : ℕ}
    (hx0 : 0 ≤ x) (hxle : x ≤ k₂ * H) (hH : 0 ≤ H) (he0 : 0 ≤ e) (heN : e ≤ N) :
    x ^ e ≤ (max 1 k₂) ^ N * (1 + H) ^ N := by
  have hy1 : (1 : ℝ) ≤ max 1 k₂ * (1 + H) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ max 1 k₂ * (1 + H) := by
        apply mul_le_mul (le_max_left _ _) (by linarith) zero_le_one (le_trans zero_le_one (le_max_left _ _))
  have hxy : x ≤ max 1 k₂ * (1 + H) := by
    calc x ≤ k₂ * H := hxle
      _ ≤ max 1 k₂ * H := by apply mul_le_mul_of_nonneg_right (le_max_right _ _) hH
      _ ≤ max 1 k₂ * (1 + H) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (le_trans zero_le_one (le_max_left _ _))
  calc x ^ e ≤ (max 1 k₂ * (1 + H)) ^ e := Real.rpow_le_rpow hx0 hxy he0
    _ ≤ (max 1 k₂ * (1 + H)) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 heN
    _ = (max 1 k₂) ^ N * (1 + H) ^ N := by
      rw [Real.rpow_natCast, mul_pow]

theorem rpow_le_max_of_nonpos {x m e emin : ℝ}
    (hm : 0 < m) (hmx : m ≤ x) (he : e ≤ 0) (hemin : emin ≤ e) :
    x ^ e ≤ max 1 (m ^ emin) := by
  have h1 : x ^ e ≤ m ^ e := Real.rpow_le_rpow_of_nonpos hm hmx he
  rcases le_or_gt 1 m with hm1 | hm1
  · calc x ^ e ≤ m ^ e := h1
      _ ≤ m ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 he
      _ = 1 := Real.rpow_zero m
      _ ≤ max 1 (m ^ emin) := le_max_left _ _
  · calc x ^ e ≤ m ^ e := h1
      _ ≤ m ^ emin := Real.rpow_le_rpow_of_exponent_ge hm hm1.le hemin
      _ ≤ max 1 (m ^ emin) := le_max_right _ _

theorem rpow_le_const_mul_one_add_pow {x H k₂ m e emin : ℝ} {N : ℕ}
    (hm : 0 < m) (hmx : m ≤ x) (hxle : x ≤ k₂ * H) (hH : 0 ≤ H) (hemin : emin ≤ e) (heN : e ≤ N) :
    x ^ e ≤ ((max 1 k₂) ^ N + max 1 (m ^ emin)) * (1 + H) ^ N := by
  have hx0 : 0 ≤ x := le_trans hm.le hmx
  have hH1 : (1 : ℝ) ≤ (1 + H) ^ N := one_le_pow₀ (by linarith)
  have hA : 0 ≤ (max 1 k₂) ^ N := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) N
  have hB : 0 ≤ max 1 (m ^ emin) := le_trans zero_le_one (le_max_left _ _)
  rcases le_or_gt 0 e with he | he
  · calc x ^ e ≤ (max 1 k₂) ^ N * (1 + H) ^ N := rpow_le_pow_mul_one_add_pow hx0 hxle hH he heN
      _ ≤ ((max 1 k₂) ^ N + max 1 (m ^ emin)) * (1 + H) ^ N := by
        apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one hH1); linarith
  · calc x ^ e ≤ max 1 (m ^ emin) := rpow_le_max_of_nonpos hm hmx he.le hemin
      _ ≤ max 1 (m ^ emin) * (1 + H) ^ N := le_mul_of_one_le_right hB hH1
      _ ≤ ((max 1 k₂) ^ N + max 1 (m ^ emin)) * (1 + H) ^ N := by
        apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one hH1); linarith

end BoundMSkeleton

namespace BoundMSkeleton

open AutomorphicForm NumberField

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem isUnitaryChar_one : IsUnitaryChar R K (1 : (AdeleRing R K)ˣ →* ℂˣ) := by
  intro x; simp

theorem norm_etaFst_unitary {μ : (AdeleRing R K)ˣ →* ℂˣ} (hμ : IsUnitaryChar R K μ)
    (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (s : ℂ) (x : (AdeleRing R K)ˣ) :
    ‖((etaFst μ α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (s.re + 1 / 2) :=
  norm_etaFst_apply_of_unitary hμ α hα s x

theorem norm_etaSnd_unitary {ν : (AdeleRing R K)ˣ →* ℂˣ} (hν : IsUnitaryChar R K ν)
    (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (s : ℂ) (x : (AdeleRing R K)ˣ) :
    ‖((etaSnd ν α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (-(s.re + 1 / 2)) := by
  rw [etaSnd_apply, Units.val_mul, norm_mul, hν x, one_mul, norm_cpowChar_apply]
  congr 1
  rw [Complex.neg_re, re_add_half]

theorem norm_apply_borel_mul_eq (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing R K)ˣ →* ℂˣ} (hμ : IsUnitaryChar R K μ) (hν : IsUnitaryChar R K ν)
    {s : ℂ} {f : AdelicGL2 R K → ℂ}
    (hf : IsInducedSection R K (etaFst μ α hα s) (etaSnd ν α hα s) f)
    (b : ↥(adelicBorel R K)) (g : AdelicGL2 R K) :
    ‖f ((b : AdelicGL2 R K) * g)‖ =
      (((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)) ^ (s.re + 1 / 2) * ‖f g‖ := by
  obtain ⟨b, hb⟩ := b
  rw [hf b hb g, norm_mul, norm_mul, norm_etaFst_unitary hμ, norm_etaSnd_unitary hν,
    Real.rpow_neg (hα _).le, Real.div_rpow (hα _).le (hα _).le]
  ring

end BoundMSkeleton

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (_hne : μ ≠ ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    ∃ (a : ℝ) (s₀ : ℂ) (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ), a < 1 / 2 ∧ s₀ ≠ 1 / 2 ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => G s g) {s : ℂ | a < s.re}) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        G s g = (s - s₀) * (φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
          unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2)
        ({s : ℂ | a < s.re} ×ˢ Set.univ) ∧
      (∀ (c u : ℝ) (t : AdelicGL2 (𝓞 F) F) (C : Set ℂ), 0 < c → IsCompact C → C ⊆ {s : ℂ | a < s.re} →
        ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ integralWindowedSiegelSet F c u,
          ‖G s (g * t)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N) := by
  intro α hα μ ν hμ hν hμF hνF hne φ hφ hφK hφf hφjc hφhol
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  obtain ⟨a, s₀, Mreg, ha, hs₀, _hs₀re, hMan, hMeq, hMco, _hMind⟩ :=
    AutomorphicForm.exists_analyticOnNhd_sub_mul_weylIntertwiningIntegral_isInducedSection_of_ne_of_isArchKFinite_family
      F hα μ ν hμ hν hμF hνF hne φ hφ hφK hφf hφjc hφhol
  obtain ⟨Wnc, hWan, hWeq, hWco, _hWbd⟩ :=
    AutomorphicForm.exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family_of_unitary
      F hα μ ν hμ hν hμF hνF φ hφ hφK hφf hφjc hφhol
  set a' : ℝ := max a (1 / 4) with ha'
  have ha'a : a ≤ a' := le_max_left _ _
  have ha'0 : (0 : ℝ) < a' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨a', s₀, fun s g => (s - s₀) * φ s g + Mreg s g + (s - s₀) * Wnc s g, ?_, hs₀, ?_, ?_, ?_, ?_⟩
  ·
    exact max_lt ha (by norm_num)
  ·
    intro g
    have hU : IsOpen {s : ℂ | a' < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h1 : AnalyticOnNhd ℂ (fun s : ℂ => (s - s₀) * φ s g) {s : ℂ | a' < s.re} :=
      (((differentiable_id.sub_const _).mul (hφhol g)).differentiableOn).analyticOnNhd hU
    have h2 : AnalyticOnNhd ℂ (fun s : ℂ => Mreg s g) {s : ℂ | a' < s.re} :=
      (hMan g).mono (fun s hs => lt_of_le_of_lt ha'a hs)
    have h3 : AnalyticOnNhd ℂ (fun s : ℂ => (s - s₀) * Wnc s g) {s : ℂ | a' < s.re} :=
      (((differentiable_id.sub_const _).differentiableOn).analyticOnNhd hU).mul
        ((hWan g).mono (fun s hs => lt_trans ha'0 hs))
    exact (h1.add h2).add h3
  ·
    intro s g hs
    have hCT :=
      AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
        F hα μ ν hμ hν s hs (φ s) (hφ s)
        (hφjc.comp (Continuous.prodMk_right s)) g
    have hM := hMeq s g hs
    have hW := hWeq s g hs
    simp only at hCT hW
    show (s - s₀) * φ s g + Mreg s g + (s - s₀) * Wnc s g = _
    rw [hM, hW, hCT]
    ring
  ·
    have hφc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => (p.1 - s₀) * φ p.1 p.2)
        ({s : ℂ | a' < s.re} ×ˢ Set.univ) :=
      ((continuous_fst.sub continuous_const).mul hφjc).continuousOn
    have hM' : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2)
        ({s : ℂ | a' < s.re} ×ˢ Set.univ) :=
      hMco.mono (Set.prod_mono (fun s hs => lt_of_le_of_lt ha'a hs) le_rfl)
    have hW' : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => (p.1 - s₀) * Wnc p.1 p.2)
        ({s : ℂ | a' < s.re} ×ˢ Set.univ) :=
      ((continuous_fst.sub continuous_const).continuousOn).mul
        (hWco.mono (Set.prod_mono (fun s hs => lt_trans ha'0 hs) le_rfl))
    exact (hφc.add hM').add hW'
  ·
    intro c u t C hc hC hCsub
    obtain ⟨k₁, k₂, Ω, hk₁, hk₁₂, hΩ, hdec⟩ :=
      AutomorphicForm.exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2 F t
    have hk₂ : 0 < k₂ := lt_of_lt_of_le hk₁ hk₁₂
    obtain ⟨S₁, hS₁⟩ := (hC.prod hΩ).exists_bound_of_continuousOn
      (f := fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2) hφjc.continuousOn
    obtain ⟨S₂, hS₂⟩ := (hC.prod hΩ).exists_bound_of_continuousOn
      (f := fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2)
      (hMco.mono (Set.prod_mono (fun s hs => lt_of_le_of_lt ha'a (hCsub hs)) (Set.subset_univ _)))
    obtain ⟨S₃, hS₃⟩ := hC.exists_bound_of_continuousOn
      (f := fun s : ℂ => s - s₀) (continuous_id.sub continuous_const).continuousOn
    obtain ⟨σM, hσM⟩ := hC.exists_bound_of_continuousOn (f := fun s : ℂ => s.re)
      Complex.continuous_re.continuousOn
    have hm : 0 < k₁ * c := mul_pos hk₁ hc
    obtain ⟨M₀, hM₀⟩ := _hWbd C Ω (k₁ * c) 0 hC (fun s hs => lt_trans ha'0 (hCsub hs)) hΩ hm
    set N : ℕ := Nat.ceil (σM + 1 / 2) with hN
    set K₁ : ℝ := (max 1 k₂) ^ N + max 1 ((k₁ * c) ^ (-(σM + 1 / 2))) with hK₁
    refine ⟨((max S₃ 0) * (max S₁ 0) + max S₂ 0) * K₁ + (max S₃ 0) * (max M₀ 0), N, ?_⟩
    intro s hs g hg
    obtain ⟨b, ω, hω, hgt_eq, hlow, hupp⟩ := hdec g hg.1
    have hcH : c ≤ archHeight F (glArch (𝓞 F) F g) := hg.2.1
    set H : ℝ := archHeight F (glArch (𝓞 F) F g) with hHdef
    have hH0 : 0 ≤ H := le_trans hc.le hcH
    have hP : (1 : ℝ) ≤ (1 + H) ^ N := one_le_pow₀ (by linarith)
    set x : ℝ := ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ) with hxdef
    have hlow' : k₁ * H ≤ x := hlow
    have hupp' : x ≤ k₂ * H := hupp
    have hmx : k₁ * c ≤ x := le_trans (mul_le_mul_of_nonneg_left hcH hk₁.le) hlow'
    have hx0 : 0 ≤ x := le_trans hm.le hmx

    have hσ : |s.re| ≤ σM := by simpa [Real.norm_eq_abs] using hσM s hs
    have hσ' := abs_le.mp hσ
    have hNge : σM + 1 / 2 ≤ (N : ℝ) := Nat.le_ceil _
    have he₁ : x ^ (s.re + 1 / 2) ≤ K₁ * (1 + H) ^ N :=
      BoundMSkeleton.rpow_le_const_mul_one_add_pow hm hmx hupp' hH0 (by linarith) (by linarith)
    have he₂ : x ^ ((-s).re + 1 / 2) ≤ K₁ * (1 + H) ^ N :=
      BoundMSkeleton.rpow_le_const_mul_one_add_pow hm hmx hupp' hH0
        (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith)

    have hφn : ‖φ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ = x ^ (s.re + 1 / 2) * ‖φ s ω‖ :=
      BoundMSkeleton.norm_apply_borel_mul_eq α hα hμ hν (hφ s) b ω
    have hMn : ‖Mreg s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ = x ^ ((-s).re + 1 / 2) * ‖Mreg s ω‖ :=
      BoundMSkeleton.norm_apply_borel_mul_eq α hα hν hμ (_hMind s (lt_of_le_of_lt ha'a (hCsub hs))) b ω
    have hWn : ‖Wnc s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ max M₀ 0 * (1 + H) ^ N := by
      have h := hM₀ s hs b ω hω hmx
      rw [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h
      exact le_trans (le_trans h (le_max_left _ _)) (le_mul_of_one_le_right (le_max_right _ _) hP)
    have h3 : ‖s - s₀‖ ≤ max S₃ 0 := le_trans (hS₃ s hs) (le_max_left _ _)
    have h1 : ‖φ s ω‖ ≤ max S₁ 0 := le_trans (hS₁ (s, ω) ⟨hs, hω⟩) (le_max_left _ _)
    have h2 : ‖Mreg s ω‖ ≤ max S₂ 0 := le_trans (hS₂ (s, ω) ⟨hs, hω⟩) (le_max_left _ _)
    have hK₁0 : 0 ≤ K₁ * (1 + H) ^ N :=
      mul_nonneg (add_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) N)
        (le_trans zero_le_one (le_max_left _ _))) (le_trans zero_le_one hP)
    show ‖(s - s₀) * φ s (g * t) + Mreg s (g * t) + (s - s₀) * Wnc s (g * t)‖ ≤ _
    rw [hgt_eq]
    calc ‖(s - s₀) * φ s (↑b * ω) + Mreg s (↑b * ω) + (s - s₀) * Wnc s (↑b * ω)‖
        ≤ ‖(s - s₀) * φ s (↑b * ω)‖ + ‖Mreg s (↑b * ω)‖ + ‖(s - s₀) * Wnc s (↑b * ω)‖ :=
          norm_add₃_le
      _ = ‖s - s₀‖ * (x ^ (s.re + 1 / 2) * ‖φ s ω‖) + x ^ ((-s).re + 1 / 2) * ‖Mreg s ω‖
            + ‖s - s₀‖ * ‖Wnc s (↑b * ω)‖ := by
          rw [norm_mul, norm_mul, hφn, hMn]
      _ ≤ max S₃ 0 * ((K₁ * (1 + H) ^ N) * max S₁ 0) + (K₁ * (1 + H) ^ N) * max S₂ 0
            + max S₃ 0 * (max M₀ 0 * (1 + H) ^ N) := by
          gcongr
      _ = (((max S₃ 0) * (max S₁ 0) + max S₂ 0) * K₁ + (max S₃ 0) * (max M₀ 0)) * (1 + H) ^ N := by
          ring

end S_AutomorphicForm_exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family (solution)
