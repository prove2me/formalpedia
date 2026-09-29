-- Prove2me | solution 1 for AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/60ac7aeb-5ba8-573f-a55d-27a38cb02fb0

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_le_of_isFundamentalDomain_of_pos
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul"
p2m_attr_erase "simp" "M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm AutomorphicForm.CuspidalSpectrum AutomorphicForm.CuspidalConstituent
open NumberField.TateGlobal NumberField.AdelicHeight

noncomputable section

namespace CuspDecayProof

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

theorem ideal_ne_bot_of_forall_dvd_mem (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) : N ≠ ⊥ := by
  classical
  intro hbot
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S := fun v => hN v (by rw [hbot]; exact dvd_zero _)
  have hMpos : 0 < ∏ v ∈ S, Ideal.absNorm v.asIdeal := by
    refine Finset.prod_pos fun v _ => Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (∏ v ∈ S, Ideal.absNorm v.asIdeal + 1)

  have hptop : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro htop
    have h1 : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = 1 := by rw [htop, Ideal.absNorm_top]
    rw [Ideal.absNorm_span_singleton] at h1
    have hn : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
      rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap]
    rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at h1
    have hr : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
    exact hp.one_lt.ne' (Nat.pow_eq_one.mp h1 |>.resolve_right hr.ne')
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hptop
  have h𝔪bot : 𝔪 ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hp.ne_zero (by exact_mod_cast hle)
  let v₀ : HeightOneSpectrum (𝓞 K) := ⟨𝔪, h𝔪.isPrime, h𝔪bot⟩

  have hpmem : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_span_singleton_self _)
  have hdvd : (Ideal.absNorm 𝔪 : ℤ) ∣ (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
    have := Ideal.absNorm_dvd_norm_of_mem hpmem
    rwa [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at this
  have hdvd' : Ideal.absNorm 𝔪 ∣ p ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Nat.cast_pow] at hdvd
    exact Int.natCast_dvd_natCast.mp hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk'
    exact h𝔪.ne_top hk'
  have hp_le : p ≤ Ideal.absNorm 𝔪 := by
    rw [hk']
    exact Nat.le_self_pow hk0 p

  have hdvM : Ideal.absNorm v₀.asIdeal ∣ ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal) (hall v₀)
  have hle' : Ideal.absNorm 𝔪 ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal := Nat.le_of_dvd hMpos hdvM
  omega

theorem combine_bounds {X : Type} (H : X → ℝ) (hH : ∀ x, 0 < H x) (u : X → ℝ) (hu : ∀ x, 0 ≤ u x)
    (k : ℕ) (H₀ Cst M : ℝ)
    (h1 : ∀ x, H₀ ≤ H x → u x ≤ Cst * (H x)⁻¹ ^ k) (h2 : ∀ x, u x ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, u x ≤ C * (H x)⁻¹ ^ k := by
  set H₁ : ℝ := max H₀ 1 with hH₁
  have hH₁pos : 0 < H₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max (max Cst (M * H₁ ^ k)) 0, le_max_right _ _, fun x => ?_⟩
  have hpow : 0 ≤ (H x)⁻¹ ^ k := pow_nonneg (inv_nonneg.mpr (hH x).le) k
  by_cases hx : H₁ ≤ H x
  · calc u x ≤ Cst * (H x)⁻¹ ^ k := h1 x (le_trans (le_max_left _ _) hx)
      _ ≤ max (max Cst (M * H₁ ^ k)) 0 * (H x)⁻¹ ^ k :=
        mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hpow
  · have hlt : H x < H₁ := lt_of_not_ge hx
    have hM : 0 ≤ M := le_trans (hu x) (h2 x)
    have hinv : H₁⁻¹ ≤ (H x)⁻¹ := by
      rw [inv_le_inv₀ hH₁pos (hH x)]; exact hlt.le
    have hk : (H₁ ^ k)⁻¹ ≤ (H x)⁻¹ ^ k := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (inv_nonneg.mpr hH₁pos.le) hinv k
    have hH₁k : 0 < H₁ ^ k := pow_pos hH₁pos k
    calc u x ≤ M := h2 x
      _ = M * H₁ ^ k * (H₁ ^ k)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hH₁k.ne', mul_one]
      _ ≤ M * H₁ ^ k * (H x)⁻¹ ^ k := mul_le_mul_of_nonneg_left hk (mul_nonneg hM hH₁k.le)
      _ ≤ max (max Cst (M * H₁ ^ k)) 0 * (H x)⁻¹ ^ k :=
        mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) hpow

end CuspDecayProof

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

open CuspDecayProof in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K) (π : HeckeEigensystem K ℂ)
    (b : AdelicGL2 (𝓞 K) K → ℂ)
    (hb : b ∈ isotypicCuspSubmodule K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ‖b g‖ ≤ C * (NumberField.AdelicHeight.adelicHeight K g)⁻¹ ^ k := by
  intro k
  classical
  have hN0 : N ≠ ⊥ := CuspDecayProof.ideal_ne_bot_of_forall_dvd_mem K N SK hN

  obtain ⟨T, c, hc, u, hcovall⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov := hcovall 1 2 two_pos one_le_two

  obtain ⟨-, -, -, hΦS, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ

  have hbW := AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_le_of_isFundamentalDomain_of_pos
    K α β hα hαβ _ hFD ξK N hN0 SK tysK π c u 1 2 T hc one_pos hb

  obtain ⟨f, hf, n, lam, hlam, ψ, hψ, hbsum⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
      K c u 1 2 T one_lt_two hcov ξK N hN0 SK tysK π b hbW

  set Wd : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u 1 2 with hWd
  have hψmem : ∀ i, ψ i ∈ cuspMemberSubmodule K Wd ξK := by
    intro i
    have h := (Submodule.mem_inf.mp (hψ i).1).1
    refine (Submodule.span_le.mpr ?_) h
    intro φ hφ
    exact ⟨hφ.smoothCusp, hφ.continuous⟩
  set x' : AdelicGL2 (𝓞 K) K → ℂ := ∑ i, (lam i)⁻¹ • ψ i with hx'
  have hx'mem : x' ∈ cuspMemberSubmodule K Wd ξK :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hψmem i)
  have hx'c : Continuous x' := hx'mem.2
  have hx'cusp := hx'mem.1.1

  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  have hint : ∀ (i : Fin n) (g : AdelicGL2 (𝓞 K) K),
      Integrable (fun x => ψ i (g * x) * f x) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro i g
    refine Continuous.integrable_of_hasCompactSupport ?_ (hfs.mul_left)
    exact ((hψmem i).2.comp (continuous_mul_left g)).mul hfc
  have hbx : b = rightConv K x' f := by
    funext g
    rw [hbsum, Finset.sum_apply]
    simp only [rightConv, hx', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finset_sum _ (fun i _ => (hint i g).const_mul ((lam i)⁻¹))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    have heig := congrFun (hψ i).2 g
    simp only [rightConv, Pi.smul_apply, smul_eq_mul] at heig
    rw [heig, ← mul_assoc, inv_mul_cancel₀ (hlam i), one_mul]

  obtain ⟨H₀, Cst, hdec⟩ :=
    AutomorphicForm.exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc K c u 1 2 T one_lt_two
      hcov ξK x' hx'cusp hx'c f hf α β hα k
  obtain ⟨M, hM⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc K c u 1 2 T one_lt_two hcov ξK x'
      hx'cusp hx'c f hf α β hα

  obtain ⟨C, hC0, hC⟩ := CuspDecayProof.combine_bounds
    (X := {g : AdelicGL2 (𝓞 K) K // ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (fun g => adelicHeight K g.1) (fun g => adelicHeight_pos g.1) (fun g => ‖b g.1‖) (fun g => norm_nonneg _)
    k H₀ Cst M
    (fun g hg => by rw [hbx]; exact hdec g.1 g.2 hg)
    (fun g => by rw [hbx]; exact hM g.1 g.2)
  exact ⟨C, hC0, fun g hg => hC ⟨g, hg⟩⟩

end
end S_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule (solution)
