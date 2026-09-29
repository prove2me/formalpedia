-- Prove2me | solution 1 for AutomorphicForm.exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2ffae9ec-2628-5eb7-917d-15d9c0d5f45b

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
import Theorems.Thm_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

namespace NPrimeReduction

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open NumberField.AdelicLevel LocalGL2 HeckeIntegralSeam AdelicDock

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem mem_U_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F h = 1)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    have hlocal : ∀ w, IsLocalLevelOne (𝓞 F) F w N
          (finComponent (𝓞 F) F w (glFin (𝓞 F) F h) : Matrix (Fin 2) (Fin 2) _)
        ∧ IsLocalLevelOne (𝓞 F) F w N
          ((finComponent (𝓞 F) F w (glFin (𝓞 F) F h))⁻¹ : GL (Fin 2) _) := by
      intro w
      exact (mem_localLevelOne_iff (𝓞 F) F w (finComponent (𝓞 F) F w (glFin (𝓞 F) F h))).mp
        (hfin w)
    constructor
    · exact ⟨⟨fun i j w => (hlocal w).1.integral i j, fun w => (hlocal w).1.lowerLeft⟩,
        fun w => by
          rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
          exact (hlocal w).1.lowerRight⟩
    · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · have := (hlocal w).2.integral i j
        rwa [← map_inv] at this
      · have := (hlocal w).2.lowerLeft
        rwa [← map_inv] at this
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
        have := (hlocal w).2.lowerRight
        rwa [← map_inv] at this
  · exact (mem_finiteAdelicGL2Subgroup_iff F h).mpr harch

private theorem components_of_mem_U {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hh : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    glArch (𝓞 F) F h = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  refine ⟨(mem_finiteAdelicGL2Subgroup_iff F h).mp h2, fun w => ?_⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  rw [mem_localLevelOne_iff]
  obtain ⟨ha, hb⟩ := h1
  constructor
  · exact ⟨fun i j => ha.integral i j w, ha.lowerLeft w, by
      have := ha.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩
  · rw [← map_inv]
    exact ⟨fun i j => hb.integral i j w, hb.lowerLeft w, by
      have := hb.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩

private theorem comp_self (z : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = z := by
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem comp_of_ne (z : GL (Fin 2) (v.adicCompletion F)) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = 1 := by
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

private theorem isLocalLevelOne_top {N : Ideal (𝓞 F)}
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)} (hm : IsLocalLevelOne (𝓞 F) F v N m) :
    IsLocalLevelOne (𝓞 F) F v ⊤ m := by
  refine ⟨hm.integral, ?_, ?_⟩
  · rw [idealBound_top]
    exact hm.lowerLeft.trans (idealBound_le_one N v)
  · rw [idealBound_top]
    exact hm.lowerRight.trans (idealBound_le_one N v)

private theorem mem_localLevelOne_top {N : Ideal (𝓞 F)} {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ localLevelOne (𝓞 F) F v N) : k ∈ localLevelOne (𝓞 F) F v ⊤ := by
  rw [mem_localLevelOne_iff] at hk ⊢
  exact ⟨isLocalLevelOne_top F v hk.1, isLocalLevelOne_top F v hk.2⟩

private theorem mem_top_of_mem {N : Ideal (𝓞 F)} {g : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hg : g ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    g ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨harch, hfin⟩ := components_of_mem_U F hg
  exact mem_U_of_components F harch fun w => mem_localLevelOne_top F w (hfin w)

private theorem not_dvd_top : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 F)) := fun h =>
  v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h))

omit [NumberField F] in
private theorem ne_bot_of_not_dvd {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) : N ≠ ⊥ := by
  rintro rfl
  exact hv (dvd_zero _)

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) : IsLocalLevelOne (𝓞 F) F v N m := by
  have hb : idealBound (𝓞 F) N v = 1 := idealBound_eq_one_of_not_dvd (ne_bot_of_not_dvd F v hv) hv
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hm 1 1) (one_mem _))

private theorem mem_localLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      i j ∈ v.adicCompletionIntegers F) :
    k ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_of_integral F v hv hk, isLocalLevelOne_of_integral F v hv hk'⟩

private noncomputable abbrev wc (w : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (w.adicCompletion F) :=
  finComponent (𝓞 F) F w (glFin (𝓞 F) F (weyl (𝓞 F) F))

private theorem weyl_mul_self : weyl (𝓞 F) F * weyl (𝓞 F) F = 1 :=
  Units.ext (by simp [weyl, Matrix.one_fin_two])

private theorem wc_mul_self (w : HeightOneSpectrum (𝓞 F)) : wc F w * wc F w = 1 := by
  simp only [wc, ← map_mul, weyl_mul_self, map_one]

private theorem weyl_entry_mem (w : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    (wc F w : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j ∈ w.adicCompletionIntegers F := by
  rw [finComponent_apply, glFin_apply]
  fin_cases i <;> fin_cases j <;> simp [weyl] <;>
    first
      | exact zero_mem_integralFiniteAdeles w
      | exact one_mem_integralFiniteAdeles w

private theorem wc_mem {N : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} (hw : ¬ w.asIdeal ∣ N) :
    wc F w ∈ localLevelOne (𝓞 F) F w N := by
  refine mem_localLevelOne_of_integral F w hw (weyl_entry_mem F w) fun i j => ?_
  rw [inv_eq_of_mul_eq_one_right (wc_mul_self F w)]
  exact weyl_entry_mem F w i j

private theorem comp_conj (w : HeightOneSpectrum (𝓞 F)) (h : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F ((weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F))
      = (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w := by
  simp only [wc, map_mul, map_inv]

private theorem mem_P_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hU : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (hconj : ∀ w : HeightOneSpectrum (𝓞 F),
      (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hU
  refine Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 F) F N).mpr ⟨h1, ?_⟩, h2⟩
  have harch : glArch (𝓞 F) F h = 1 := (components_of_mem_U F hU).1
  have hz : (weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F ?_ fun w => ?_
    · simp only [map_mul, map_inv, harch, mul_one, inv_mul_cancel]
    · rw [comp_conj]
      exact hconj w
  refine Subgroup.mem_map.mpr ⟨(weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F, (Subgroup.mem_inf.mp hz).1, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem components_of_mem_P {N : Ideal (𝓞 F)} {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (w : HeightOneSpectrum (𝓞 F)) :
    (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p) * wc F w ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hp
  obtain ⟨-, hmap⟩ := (mem_principalLevel_iff (𝓞 F) F N).mp h1
  obtain ⟨z, hz, hzp⟩ := Subgroup.mem_map.mp hmap
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzp
  have hz' : (weyl (𝓞 F) F)⁻¹ * p * weyl (𝓞 F) F = z := by
    rw [← hzp]; group
  have harch : glArch (𝓞 F) F p = 1 := (mem_finiteAdelicGL2Subgroup_iff F p).mp h2
  have hzU : z ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine Subgroup.mem_inf.mpr ⟨hz, (mem_finiteAdelicGL2Subgroup_iff F z).mpr ?_⟩
    rw [← hz']
    simp only [map_mul, map_inv, harch, mul_one, inv_mul_cancel]
  rw [← comp_conj, hz']
  exact (components_of_mem_U F hzU).2 w

private theorem P_le_U (N : Ideal (𝓞 F)) :
    principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ≤ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
  inf_le_inf_right _ (principalLevel_le_levelOne (𝓞 F) F N)

section Weyl

private theorem wc_inv : (wc F v)⁻¹ = wc F v :=
  inv_eq_of_mul_eq_one_right (wc_mul_self F v)

private theorem wc_coe :
    ((wc F v : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![0, 1; 1, 0] := by
  ext i j
  rw [finComponent_apply, glFin_apply]
  fin_cases i <;> fin_cases j <;> simp [weyl] <;> rfl

private theorem wc_conj_coe (m : GL (Fin 2) (v.adicCompletion F)) :
    (((wc F v)⁻¹ * m * wc F v : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1,
            (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0;
          (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1,
            (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0] := by
  rw [wc_inv, Units.val_mul, Units.val_mul, wc_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem integral_of_four {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (h00 : m 0 0 ∈ v.adicCompletionIntegers F) (h01 : m 0 1 ∈ v.adicCompletionIntegers F)
    (h10 : m 1 0 ∈ v.adicCompletionIntegers F) (h11 : m 1 1 ∈ v.adicCompletionIntegers F) :
    ∀ i j, m i j ∈ v.adicCompletionIntegers F := by
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

private theorem wc_conj_inv (k : GL (Fin 2) (v.adicCompletion F)) :
    ((wc F v)⁻¹ * k * wc F v : GL (Fin 2) (v.adicCompletion F))⁻¹ = (wc F v)⁻¹ * k⁻¹ * wc F v := by
  group

end Weyl

private theorem wc_conj_mem_top {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ localLevelOne (𝓞 F) F v ⊤) : (wc F v)⁻¹ * k * wc F v ∈ localLevelOne (𝓞 F) F v ⊤ := by
  have hk' := (mem_localLevelOne_iff (𝓞 F) F v _).mp hk
  refine mem_localLevelOne_of_integral F v (not_dvd_top F v) ?_ ?_
  · rw [wc_conj_coe]
    exact integral_of_four F v (by simpa using hk'.1.integral 1 1) (by simpa using hk'.1.integral 1 0)
      (by simpa using hk'.1.integral 0 1) (by simpa using hk'.1.integral 0 0)
  · rw [wc_conj_inv, wc_conj_coe]
    exact integral_of_four F v (by simpa using hk'.2.integral 1 1) (by simpa using hk'.2.integral 1 0)
      (by simpa using hk'.2.integral 0 1) (by simpa using hk'.2.integral 0 0)

private theorem mem_inf_principal_top {D : Ideal (𝓞 F)} {x : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hx : x ∈ levelOne (𝓞 F) F D ⊓ finiteAdelicGL2Subgroup F) :
    x ∈ levelOne (𝓞 F) F D ⊓ principalLevel (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  have hP : x ∈ principalLevel (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F :=
    mem_P_of_components F (mem_top_of_mem F hx) fun w =>
      wc_conj_mem_top F w ((components_of_mem_U F (mem_top_of_mem F hx)).2 w)
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h1, (Subgroup.mem_inf.mp hP).1⟩, h2⟩

private theorem exists_notMem (SK : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ w : HeightOneSpectrum (𝓞 F), w ∉ SK := by
  have key : ∀ p : Nat.Primes, ∃ w : HeightOneSpectrum (𝓞 F),
      w.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {((p : ℕ) : ℤ)} := by
    intro p
    have hp : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {((p : ℕ) : ℤ)})
      (⊥ : Ideal (𝓞 F)) (Ideal.comap_bot_le_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int)
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int] at hQc
      exact hp.ne_zero (Ideal.span_singleton_eq_bot.mp hQc.symm)
    exact ⟨⟨Q, hQ, hQ0⟩, hQc⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro p q hpq
    have h := hf p
    rw [hpq, hf q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    exact Subtype.ext (by simpa using h'.symm)
  haveI : Infinite (HeightOneSpectrum (𝓞 F)) := Infinite.of_injective f hinj
  exact Infinite.exists_notMem_finset SK

private theorem eq_top_of_forall_not_dvd {E : Ideal (𝓞 F)} (hE : E ≠ ⊥)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), ¬ w.asIdeal ∣ E) : E = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal E hne
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact hE (le_bot_iff.mp hle)
  exact h ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.mpr hle)

private theorem eq_or_dvd_of_dvd_mul_pow {D : Ideal (𝓞 F)} {c : ℕ} {w : HeightOneSpectrum (𝓞 F)}
    (hw : w.asIdeal ∣ D * v.asIdeal ^ c) : w.asIdeal ∣ D ∨ w = v := by
  refine (w.prime.dvd_or_dvd hw).imp id fun h => ?_
  exact HeightOneSpectrum.ext (associated_iff_eq.mp (w.prime.associated_of_dvd v.prime (w.prime.dvd_of_dvd_pow h)))

end NPrimeReduction

open AutomorphicForm

private theorem reduce
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (π : HeckeEigensystem K ℂ) (tys : ArchTypeFamily K) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    T ⊆ SK → ∀ (D E : Ideal (𝓞 K)) (φ : AdelicGL2 (𝓞 K) K → ℂ), D ≠ ⊥ →
      (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ D → w ∈ SK) → E ≠ ⊥ →
      (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ E → w ∈ T) →
      IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ (D * E) SK π φ →
      (∀ g : AdelicGL2 (𝓞 K) K,
        ∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K E ⊓ finiteAdelicGL2Subgroup K, φ (g * x) = φ g) →
      φ ∈ archCutSubmodule K tys → φ ≠ 0 →
      ∃ (N'' : Ideal (𝓞 K)) (φ' : AdelicGL2 (𝓞 K) K → ℂ),
        N'' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N'' → v ∈ SK) ∧
        IsIsotypicCuspFormAt K
          (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N'' SK π φ' ∧
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ x ∈ levelOne (𝓞 K) K N'' ⊓ finiteAdelicGL2Subgroup K, φ' (g * x) = φ' g) ∧
        φ' ≠ 0 := by
  classical
  refine Finset.induction_on T ?_ ?_
  · intro _ D E φ hD0 hDS hE0 hET hiso hinv htys hφ0
    have hE : E = ⊤ := NPrimeReduction.eq_top_of_forall_not_dvd K hE0 fun w hw =>
      Finset.notMem_empty w (hET w hw)
    subst hE
    rw [Ideal.mul_top] at hiso
    exact ⟨D, φ, hD0, hDS, hiso, fun g x hx => hinv g x (NPrimeReduction.mem_inf_principal_top K hx), hφ0⟩
  · intro v T hvT ih hT D E φ hD0 hDS hE0 hET hiso hinv htys hφ0
    have hvSK : v ∈ SK := hT (Finset.mem_insert_self v T)
    have hTSK : T ⊆ SK := fun w hw => hT (Finset.mem_insert_of_mem hw)
    obtain ⟨k, E', hndvd, hEeq⟩ := WfDvdMonoid.max_power_factor (show E ≠ 0 from hE0) v.irreducible
    have hE'0 : E' ≠ ⊥ := by
      rintro rfl
      exact hE0 (by rw [hEeq, Ideal.mul_bot])
    have hE'T : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ E' → w ∈ T := by
      intro w hw
      have hwE : w.asIdeal ∣ E := by
        rw [hEeq]
        exact dvd_mul_of_dvd_right hw _
      rcases Finset.mem_insert.mp (hET w hwE) with rfl | hwT
      · exact absurd hw hndvd
      · exact hwT
    have hlev : D * E = D * E' * v.asIdeal ^ k := by
      rw [hEeq]
      ring
    rw [hlev] at hiso
    have hinv' : ∀ g : AdelicGL2 (𝓞 K) K,
        ∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E' * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
          φ (g * x) = φ g := by
      have hE2 : E' * v.asIdeal ^ k = E := by
        rw [hEeq, mul_comm]
      rw [hE2]
      exact hinv
    obtain ⟨c, φ', hφ'iso, hφ'inv, hφ't, hφ'0⟩ :=
      AutomorphicForm.exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
        K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK ξ SK π tys v hvSK D E' k φ hiso hinv' htys hφ0
    refine ih hTSK (D * v.asIdeal ^ c) E' φ' ?_ ?_ hE'0 hE'T hφ'iso hφ'inv hφ't hφ'0
    · exact mul_ne_zero (show D ≠ 0 from hD0) (pow_ne_zero _ (show v.asIdeal ≠ 0 from v.ne_bot))
    · intro w hw
      rcases NPrimeReduction.eq_or_dvd_of_dvd_mul_pow K v hw with h | rfl
      · exact hDS w h
      · exact hvSK

theorem solution
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (π : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N' SK π u)
    (hu0 : u ≠ 0) :
    ∃ (N'' : Ideal (𝓞 K)) (φ : AdelicGL2 (𝓞 K) K → ℂ),
      N'' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N'' → v ∈ SK) ∧
      IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N'' SK π φ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ x ∈ levelOne (𝓞 K) K N'' ⊓ finiteAdelicGL2Subgroup K, φ (g * x) = φ g) ∧
      φ ≠ 0 := by
  obtain ⟨tys, u₁, hu₁, hu₁t, hu₁0⟩ :=
    AutomorphicForm.exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero
      K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK SK ξ N' hN' π u hu hu0
  have hN'0 : N' ≠ ⊥ := by
    rintro rfl
    obtain ⟨w, hw⟩ := NPrimeReduction.exists_notMem K SK
    exact hw (hN' w (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _))
  have hu₁' : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ (⊤ * N') SK π u₁ := by
    rwa [Ideal.top_mul]
  refine reduce K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK SK ξ π tys SK (Finset.Subset.refl SK) ⊤ N' u₁
    top_ne_bot ?_ hN'0 hN' hu₁' ?_ hu₁t hu₁0
  · intro w hw
    exact absurd (Ideal.dvd_iff_le.mp hw) fun h => w.isPrime.ne_top (top_le_iff.mp h)
  · intro g x hx
    exact hu₁.level_invariant g x (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1.2, (Subgroup.mem_inf.mp hx).2⟩)

#print axioms solution

end S_AutomorphicForm_exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_levelOne_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero (solution)
