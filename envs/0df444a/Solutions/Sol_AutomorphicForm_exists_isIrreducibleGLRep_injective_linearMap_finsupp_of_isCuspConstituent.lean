-- Prove2me | solution 1 for AutomorphicForm.exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d06a1ad6-e7f1-5ac4-856a-d5aa1f922ef5

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain
import Theorems.Thm_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_LocalNewvector_exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top
import Theorems.Thm_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

private noncomputable abbrev windowPins (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) :=
  productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

section

open NumberField

private theorem padicToAdelic_mul_comm_of_finComponent_eq_one (q : ℕ) [Fact q.Prime]
    (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hq : AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) = 1)
    (x : GL (Fin 2) ℚ_[q]) :
    (AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) * h =
      h * AdelicDock.padicToAdelic q x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ
  ·
    rw [map_mul, map_mul]
    have harch : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
      calc (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
            ((AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
            = ((AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q x) : GL (Fin 2) (InfiniteAdeleRing ℚ)) :
                Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) := rfl
        _ = 1 := by rw [AdelicDock.glArch_padicToAdelic]; exact Units.val_one
    rw [harch, one_mul, mul_one]
  ·
    rw [map_mul, map_mul]
    apply AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ
    intro w
    rw [map_mul, map_mul]
    by_cases hw : w = AdelicDock.padicPlace q
    ·
      subst hw
      have hh : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := by
        calc (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mapMatrix
              ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))
              = ((AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) :
                    GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) :
                  Matrix (Fin 2) (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) := rfl
          _ = 1 := by rw [hq]; exact Units.val_one
      rw [hh, one_mul, mul_one]
    ·
      have hx : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
            ((AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := by
        calc (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
              ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
                ((AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
                  Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))
              = ((AdelicLevel.finComponent (𝓞 ℚ) ℚ w
                    (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q x)) :
                    GL (Fin 2) (w.adicCompletion ℚ)) :
                  Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) := rfl
          _ = 1 := by
            rw [AdelicDock.glFin_padicToAdelic, AdelicDock.finComponent_padicToFinAdelic_of_ne q x hw]
            exact Units.val_one
      rw [hx, one_mul, mul_one]

private theorem smul_padic_smul_comm_of_finComponent_eq_one (q : ℕ) [Fact q.Prime]
    (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hq : AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) = 1)
    (x : GL (Fin 2) ℚ_[q]) (m : LocalNewvector.AdelicFnCarrier ℚ) :
    h • (x • m) = x • (h • m) := by
  rw [LocalNewvector.AdelicFnCarrier.padic_smul_def, LocalNewvector.AdelicFnCarrier.padic_smul_def,
    ← mul_smul, ← mul_smul, padicToAdelic_mul_comm_of_finComponent_eq_one q h hq x]

end

section

open NumberField

section Generic

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (N : Ideal (𝓞 ℚ))

private theorem isLocalLevelOne_of_isLevelOneMatrix
    {m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hm : AdelicLevel.IsLevelOneMatrix (𝓞 ℚ) ℚ N m) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v N (Matrix.of fun i j => m i j v) := by
  obtain ⟨⟨hint, hll⟩, hlr⟩ := hm
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · simpa only [Matrix.of_apply] using hint i j v
  · simpa only [Matrix.of_apply] using hll v
  · have h := hlr v
    rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at h
    simpa only [Matrix.of_apply] using h

private theorem coe_finComponent_eq
    (g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((AdelicLevel.finComponent (𝓞 ℚ) ℚ v g :
        Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _)
      = Matrix.of fun i j =>
          (g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j v := by
  ext i j
  rw [AdelicLevel.finComponent_apply, Matrix.of_apply]

private theorem localEmbed_finComponent_mem_finiteLevelOne
    {g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hg : g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ N) :
    AdelicDock.localEmbed (𝓞 ℚ) ℚ v (AdelicLevel.finComponent (𝓞 ℚ) ℚ v g)
      ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ N := by
  rw [AdelicLevel.mem_finiteLevelOne_iff] at hg ⊢
  obtain ⟨h₁, h₂⟩ := hg
  rw [← map_inv, ← map_inv, AdelicDock.coe_localEmbed, AdelicDock.coe_localEmbed,
    AdelicDock.isLevelOneMatrix_localMat_iff, AdelicDock.isLevelOneMatrix_localMat_iff,
    coe_finComponent_eq, coe_finComponent_eq]
  exact ⟨isLocalLevelOne_of_isLevelOneMatrix v N h₁, isLocalLevelOne_of_isLevelOneMatrix v N h₂⟩

end Generic

section Padic

variable (q : ℕ) [Fact q.Prime]

private noncomputable def padicGLInv :
    Matrix.GeneralLinearGroup (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ) →*
      Matrix.GeneralLinearGroup (Fin 2) ℚ_[q] :=
  Matrix.GeneralLinearGroup.map (AdelicDock.padicRingEquiv q).symm.toRingHom

private theorem padicGL_padicGLInv
    (y : Matrix.GeneralLinearGroup (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) :
    AdelicDock.padicGL q (padicGLInv q y) = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicDock.padicGL_apply, padicGLInv, Matrix.GeneralLinearGroup.map_apply]
  exact (AdelicDock.padicRingEquiv q).apply_symm_apply _

private def IsAwayFromQ (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : Prop :=
  AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) = 1

private theorem exists_padicToAdelic_mul_of_mem_levelOne_inf (N : Ideal (𝓞 ℚ))
    (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hg : g ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) :
    ∃ x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q],
      x ∈ (AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ).comap
          (AdelicDock.padicToAdelic q) ∧
      ∃ h ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ,
        IsAwayFromQ q h ∧ g = AdelicDock.padicToAdelic q x * h := by
  obtain ⟨hg₁, -⟩ := Subgroup.mem_inf.mp hg

  set c := AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g)
    with hc
  set x := padicGLInv q c with hx
  have hxc : AdelicDock.padicGL q x = c := padicGL_padicGLInv q c

  have hxU : AdelicDock.padicToAdelic q x ∈
      AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [AdelicLevel.mem_levelOne_iff, AdelicDock.glFin_padicToAdelic, AdelicDock.padicToFinAdelic_apply,
        hxc, hc]
      exact localEmbed_finComponent_mem_finiteLevelOne _ N (AdelicLevel.mem_levelOne_iff.mp hg₁)
    · rw [AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff]
      exact AdelicDock.glArch_padicToAdelic q x
  refine ⟨x, Subgroup.mem_comap.mpr hxU, (AdelicDock.padicToAdelic q x)⁻¹ * g,
    mul_mem (inv_mem hxU) hg, ?_, (mul_inv_cancel_left _ _).symm⟩

  unfold IsAwayFromQ
  rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_padicToAdelic,
    AdelicDock.finComponent_padicToFinAdelic_self, hxc, ← hc]
  exact inv_mul_cancel c

private noncomputable def awayGroup (N : Ideal (𝓞 ℚ)) : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :=
  (AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) ⊓
    ((AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).comp (AdelicLevel.glFin (𝓞 ℚ) ℚ)).ker

private theorem mem_awayGroup_iff (N : Ideal (𝓞 ℚ)) (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    h ∈ awayGroup q N ↔
      h ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ ∧ IsAwayFromQ q h := by
  simp only [awayGroup, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.comp_apply, IsAwayFromQ]

private theorem awayGroup_le (N : Ideal (𝓞 ℚ)) :
    awayGroup q N ≤ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ :=
  inf_le_left

private theorem exists_mem_comap_mul_mem_awayGroup (N : Ideal (𝓞 ℚ)) (u : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hu : u ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) :
    ∃ k ∈ (AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ).comap
        (AdelicDock.padicToAdelic q),
      ∃ h ∈ awayGroup q N, u = AdelicDock.padicToAdelic q k * h := by
  obtain ⟨x, hx, h, hh, hq, rfl⟩ := exists_padicToAdelic_mul_of_mem_levelOne_inf q N u hu
  exact ⟨x, hx, h, (mem_awayGroup_iff q N h).mpr ⟨hh, hq⟩, rfl⟩

private theorem exists_eq_mul_padicToAdelic_isAwayFromQ (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]),
      g = h * AdelicDock.padicToAdelic q x ∧ IsAwayFromQ q h ∧
        (g ∈ AutomorphicForm.finiteAdelicGL2Subgroup ℚ → h ∈ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) := by
  refine ⟨g * (AdelicDock.padicToAdelic q (padicGLInv q (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
    (AdelicLevel.glFin (𝓞 ℚ) ℚ g))))⁻¹, padicGLInv q (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
    (AdelicLevel.glFin (𝓞 ℚ) ℚ g)), (inv_mul_cancel_right _ _).symm, ?_, ?_⟩
  · unfold IsAwayFromQ
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_padicToAdelic,
      AdelicDock.finComponent_padicToFinAdelic_self, padicGL_padicGLInv, mul_inv_cancel]
  · intro hg
    rw [AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff] at hg ⊢
    rw [map_mul, map_inv, AdelicDock.glArch_padicToAdelic, inv_one, mul_one, hg]

end Padic

private theorem exists_padic_mul_eq_of_mem_finiteAdelicGL2Subgroup (q : ℕ) [Fact q.Prime]
    (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) :
    ∃ (k : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]) (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ),
      h ∈ AutomorphicForm.finiteAdelicGL2Subgroup ℚ ∧
        (∀ x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q],
          Commute (AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) h) ∧
        g = h * AdelicDock.padicToAdelic q k := by
  obtain ⟨h, k, hgk, hq, hfin⟩ := exists_eq_mul_padicToAdelic_isAwayFromQ q g
  exact ⟨k, h, hfin hg, fun x => padicToAdelic_mul_comm_of_finComponent_eq_one q h hq x, hgk⟩

end

section

open NumberField AutomorphicForm

private theorem comp_mul_mem_archCutSubmodule_of_commute {tys : ArchTypeFamily ℚ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ archCutSubmodule ℚ tys) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hg : ∀ (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion), Commute g (rowIsometryInclAt₀ ℚ w k)) :
    (fun x => f (x * g)) ∈ archCutSubmodule ℚ tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (x * g)) ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt ℚ w (tys.rep w i))
    (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archTypeSubmoduleAt ℚ w (tys.rep w j)) i
      (comp_mul_mem_typeSubmodule_of_commute hfi g (hg w))
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

private theorem commute_padicToAdelic_rowIsometryInclAt₀ (q : ℕ) [Fact q.Prime] (x : GL (Fin 2) ℚ_[q])
    (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion) :
    Commute (AdelicDock.padicToAdelic q x : AdelicGL2 (𝓞 ℚ) ℚ) (rowIsometryInclAt₀ ℚ w k) :=
  padicToAdelic_mul_comm_of_finComponent_eq_one q (rowIsometryInclAt₀ ℚ w k)
    (by rw [glFin_rowIsometryInclAt₀, map_one]) x

private theorem comp_mul_padicToAdelic_mem_archCutSubmodule {tys : ArchTypeFamily ℚ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ archCutSubmodule ℚ tys) (q : ℕ) [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) :
    (fun y => f (y * AdelicDock.padicToAdelic q x)) ∈ archCutSubmodule ℚ tys :=
  comp_mul_mem_archCutSubmodule_of_commute hf _ (commute_padicToAdelic_rowIsometryInclAt₀ q x)

end

section

open NumberField

private theorem continuous_finMat : Continuous (AdelicDock.finMat (𝓞 ℚ) ℚ) := by
  refine continuous_matrix fun i j => ?_
  exact continuous_const.prodMk (continuous_id.matrix_elem i j)

private theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 ℚ) ℚ) := by
  obtain ⟨hval, hinv⟩ := Units.continuous_iff.mp
    (continuous_id : Continuous fun g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) => g)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_finMat.comp hval
  · exact continuous_finMat.comp hinv

private noncomputable def finEmbedSub (g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ) :=
  ⟨AdelicDock.finEmbed (𝓞 ℚ) ℚ g,
    (AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ g)⟩

private theorem continuous_finEmbedSub : Continuous finEmbedSub :=
  continuous_finEmbed.subtype_mk _

private noncomputable def levelCompact (N : Ideal (𝓞 ℚ)) : Set ↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ) :=
  finEmbedSub '' (AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ N : Set _)

private theorem isCompact_levelCompact (N : Ideal (𝓞 ℚ)) : IsCompact (levelCompact N) :=
  (AdelicLevel.isCompact_finiteLevelOne (𝓞 ℚ) ℚ N).image continuous_finEmbedSub

private theorem finEmbedSub_glFin (u : ↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ)) :
    finEmbedSub (AdelicLevel.glFin (𝓞 ℚ) ℚ (u : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)) = u := by
  have harch : AdelicLevel.glArch (𝓞 ℚ) ℚ (u : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
    (AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff ℚ _).mp u.2
  apply Subtype.ext
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show AdelicDock.finMat (𝓞 ℚ) ℚ _ i j = _
  refine Prod.ext ?_ ?_
  · have h1 := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) harch
    simpa [AdelicDock.finMat, AdelicLevel.glArch_apply] using h1.symm
  · simp [AdelicDock.finMat, AdelicLevel.glFin_apply]

private theorem mem_levelCompact_of_mem_levelOne (N : Ideal (𝓞 ℚ))
    (u : ↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ))
    (hu : (u : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N) :
    u ∈ levelCompact N :=
  ⟨AdelicLevel.glFin (𝓞 ℚ) ℚ (u : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ), AdelicLevel.mem_levelOne_iff.mp hu,
    finEmbedSub_glFin u⟩

private theorem padic_mem_levelCompact (q : ℕ) [Fact q.Prime] (N : Ideal (𝓞 ℚ))
    (x : GL (Fin 2) ℚ_[q]) (hx : AdelicDock.padicToAdelic q x ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N) :
    (⟨AdelicDock.padicToAdelic q x,
        (AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_padicToAdelic q x)⟩ :
      ↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ)) ∈ levelCompact N := by
  refine ⟨AdelicDock.padicToFinAdelic q x, ?_, ?_⟩
  · have h := AdelicLevel.mem_levelOne_iff.mp hx
    rwa [AdelicDock.glFin_padicToAdelic] at h
  · exact Subtype.ext (AdelicDock.padicToAdelic_apply q x).symm

end

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace AwayCarrier
p2m_open "LocalNewvector"

variable {q : ℕ} [Fact q.Prime]

private theorem finite_smul_image_of_isCompact_of_forall_mem
    {V : Submodule ℂ (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)}
    (hVsm : ∀ f ∈ V, AutomorphicForm.IsKfSmooth ℚ f)
    {K : Set ↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ)} (hK : IsCompact K)
    (U₀ : Subgroup (GL (Fin 2) ℚ_[q]))
    (hU₀ : ∀ k ∈ U₀, ∃ u ∈ K,
      (u : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) = AdelicDock.padicToAdelic q k)
    {ψ : AdelicFnCarrier ℚ} (hψ : ψ.toFn ∈ V) :
    Set.Finite ((fun k : GL (Fin 2) ℚ_[q] => k • ψ) '' (U₀ : Set (GL (Fin 2) ℚ_[q]))) := by
  have hfin := (hVsm ψ.toFn hψ).finite_smul_image_of_isCompact hK
  refine Set.Finite.of_finite_image (f := fun χ : AdelicFnCarrier ℚ =>
    (FLT.SmoothVectors.RightTranslationFn.mk χ.toFn :
      FLT.SmoothVectors.RightTranslationFn (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) ℂ))
    (hfin.subset ?_) ?_
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    obtain ⟨u, huK, hu⟩ := hU₀ k hk
    refine ⟨u, huK, ?_⟩
    apply FLT.SmoothVectors.RightTranslationFn.ext
    intro x
    show ψ.toFn (x * (u : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)) =
      ψ.toFn (x * AdelicDock.padicToAdelic q k)
    rw [hu]
  · intro a _ b _ hab
    exact AdelicFnCarrier.ext fun x => congrFun (congrArg FLT.SmoothVectors.RightTranslationFn.toFun hab) x

end LocalNewvector.AwayCarrier

end

section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.CuspidalConstituent
p2m_open "LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector"

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace AwayCarrier
p2m_open "LocalNewvector"

variable (q : ℕ) [Fact q.Prime]

private def awayCarrier (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (tys : ArchTypeFamily ℚ) : Submodule ℂ (AdelicFnCarrier ℚ) where
  carrier := {ψ | ψ.toFn ∈ V ∧ (∀ h ∈ Uaw, rightTranslate ℚ h ψ.toFn = ψ.toFn) ∧
    ψ.toFn ∈ archCutSubmodule ℚ tys}
  zero_mem' := ⟨V.zero_mem, fun _ _ => funext fun _ => rfl, (archCutSubmodule ℚ tys).zero_mem⟩
  add_mem' := fun ha hb =>
    ⟨V.add_mem ha.1 hb.1,
      fun h hh => funext fun x => congrArg₂ (· + ·) (congrFun (ha.2.1 h hh) x) (congrFun (hb.2.1 h hh) x),
      (archCutSubmodule ℚ tys).add_mem ha.2.2 hb.2.2⟩
  smul_mem' := fun c {_a} ha =>
    ⟨V.smul_mem c ha.1, fun h hh => funext fun x => congrArg (c • ·) (congrFun (ha.2.1 h hh) x),
      (archCutSubmodule ℚ tys).smul_mem c ha.2.2⟩

private def fixedCarrier (U₀ : Subgroup (GL (Fin 2) ℚ_[q])) : Submodule ℂ (AdelicFnCarrier ℚ) where
  carrier := {ψ | ∀ k ∈ U₀, k • ψ = ψ}
  zero_mem' := fun k _ => smul_zero k
  add_mem' := fun {a b} ha hb k hk => by rw [smul_add, ha k hk, hb k hk]
  smul_mem' := fun c {a} ha k hk => by rw [smul_comm k c a, ha k hk]

private noncomputable def localLevel (N₀ : Ideal (𝓞 ℚ)) : Subgroup (GL (Fin 2) ℚ_[q]) :=
  (levelOne (𝓞 ℚ) ℚ N₀ ⊓ finiteAdelicGL2Subgroup ℚ).comap (AdelicDock.padicToAdelic q)

variable {q}

private theorem smul_mem_awayCarrier {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)} {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)}
    {tys : ArchTypeFamily ℚ}
    (hV : ∀ (ψ : AdelicFnCarrier ℚ) (x : GL (Fin 2) ℚ_[q]), ψ.toFn ∈ V → (x • ψ).toFn ∈ V)
    (hcomm : ∀ h ∈ Uaw, ∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h)
    (harch : ∀ f ∈ archCutSubmodule ℚ tys, ∀ x : GL (Fin 2) ℚ_[q],
      (fun y => f (y * AdelicDock.padicToAdelic q x)) ∈ archCutSubmodule ℚ tys)
    (x : GL (Fin 2) ℚ_[q]) {ψ : AdelicFnCarrier ℚ} (hψ : ψ ∈ awayCarrier V Uaw tys) :
    x • ψ ∈ awayCarrier V Uaw tys := by
  obtain ⟨hψV, hfix, hcut⟩ := hψ
  refine ⟨hV ψ x hψV, fun h hh => funext fun y => ?_, harch _ hcut x⟩
  show ψ.toFn (y * h * AdelicDock.padicToAdelic q x) = ψ.toFn (y * AdelicDock.padicToAdelic q x)
  rw [mul_assoc, ← (hcomm h hh x).eq, ← mul_assoc]
  exact congrFun (hfix h hh) (y * AdelicDock.padicToAdelic q x)

private theorem toFn_image_awayCarrier_inf_fixedCarrier {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} {tys : ArchTypeFamily ℚ} (pins : CarrierPins ℚ) (N₀ : Ideal (𝓞 ℚ))
    (hU : pins.U N₀ = levelOne (𝓞 ℚ) ℚ N₀ ⊓ finiteAdelicGL2Subgroup ℚ) (hUaw : Uaw ≤ pins.U N₀)
    (hsplit : ∀ u ∈ pins.U N₀, ∃ k ∈ localLevel q N₀, ∃ h ∈ Uaw, u = AdelicDock.padicToAdelic q k * h) :
    {f | ∃ ψ ∈ awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀), ψ.toFn = f} =
      ↑(V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys) := by
  ext f
  constructor
  · rintro ⟨ψ, ⟨⟨hψV, hfix, hcut⟩, hfx⟩, rfl⟩
    refine ⟨⟨hψV, fun g u hu => ?_⟩, hcut⟩
    obtain ⟨k, hk, h, hh, rfl⟩ := hsplit u hu
    calc ψ.toFn (g * (AdelicDock.padicToAdelic q k * h))
        = ψ.toFn (g * AdelicDock.padicToAdelic q k * h) := congrArg ψ.toFn (mul_assoc _ _ _).symm
      _ = ψ.toFn (g * AdelicDock.padicToAdelic q k) := congrFun (hfix h hh) (g * AdelicDock.padicToAdelic q k)
      _ = (k • ψ).toFn g := rfl
      _ = ψ.toFn g := by rw [hfx k hk]
  · rintro ⟨⟨hfV, hflev⟩, hfcut⟩
    have hpad : ∀ k ∈ localLevel q N₀, AdelicDock.padicToAdelic q k ∈ pins.U N₀ := fun k hk => by
      rw [hU]; exact hk
    exact ⟨AdelicFnCarrier.mk f, ⟨⟨hfV, fun h hh => funext fun y => hflev y h (hUaw hh), hfcut⟩,
      fun k hk => AdelicFnCarrier.ext fun y => hflev y _ (hpad k hk)⟩, rfl⟩

private theorem finiteDimensional_awayCarrier_inf_fixedCarrier {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} {tys : ArchTypeFamily ℚ} (pins : CarrierPins ℚ) (N₀ : Ideal (𝓞 ℚ))
    (hU : pins.U N₀ = levelOne (𝓞 ℚ) ℚ N₀ ⊓ finiteAdelicGL2Subgroup ℚ) (hUaw : Uaw ≤ pins.U N₀)
    (hsplit : ∀ u ∈ pins.U N₀, ∃ k ∈ localLevel q N₀, ∃ h ∈ Uaw, u = AdelicDock.padicToAdelic q k * h)
    (hfd : FiniteDimensional ℂ ↥(V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys)) :
    FiniteDimensional ℂ ↥(awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀)) := by
  have hsub : ∀ ψ ∈ awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀),
      ψ.toFn ∈ V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys := fun ψ hψ =>
    (toFn_image_awayCarrier_inf_fixedCarrier (V := V) (Uaw := Uaw) (tys := tys) pins N₀ hU hUaw hsplit).le
      ⟨ψ, hψ, rfl⟩
  let L : ↥(awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀)) →ₗ[ℂ]
      ↥(V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys) :=
    { toFun := fun ψ => ⟨ψ.1.toFn, hsub ψ.1 ψ.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI := hfd
  exact FiniteDimensional.of_injective L fun a b hab =>
    Subtype.ext (AdelicFnCarrier.ext fun g => congrFun (congrArg Subtype.val hab) g)

private theorem awayCarrier_inf_fixedCarrier_ne_bot {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} {tys : ArchTypeFamily ℚ} (pins : CarrierPins ℚ) (N₀ : Ideal (𝓞 ℚ))
    (hUaw : Uaw ≤ pins.U N₀) (hpad : ∀ k ∈ localLevel q N₀, AdelicDock.padicToAdelic q k ∈ pins.U N₀)
    (hne : V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys ≠ ⊥) :
    awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀) ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨⟨hfV, hflev⟩, hfcut⟩ := hf
  refine (Submodule.ne_bot_iff _).mpr ⟨AdelicFnCarrier.mk f, ⟨⟨hfV, fun h hh => funext fun y => ?_, hfcut⟩,
    fun k hk => AdelicFnCarrier.ext fun y => ?_⟩, AdelicFnCarrier.mk_ne_zero_of_ne_zero hf0⟩
  · exact hflev y h (hUaw hh)
  · exact hflev y _ (hpad k hk)

private theorem finite_smul_image_localLevel {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} {tys : ArchTypeFamily ℚ} (hVsm : ∀ f ∈ V, IsKfSmooth ℚ f)
    (N₀ : Ideal (𝓞 ℚ)) {ψ : AdelicFnCarrier ℚ} (hψ : ψ ∈ awayCarrier V Uaw tys) :
    Set.Finite ((fun k : GL (Fin 2) ℚ_[q] => k • ψ) '' (localLevel q N₀ : Set (GL (Fin 2) ℚ_[q]))) := by
  exact finite_smul_image_of_isCompact_of_forall_mem hVsm (isCompact_levelCompact N₀) (localLevel q N₀)
    (fun k hk => ⟨_, padic_mem_levelCompact q N₀ k (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hk)).1, rfl⟩) hψ.1

end LocalNewvector.AwayCarrier

end

section

open NumberField AutomorphicForm

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace AwayCarrier
p2m_open "LocalNewvector"

private def carrierToFn : AdelicFnCarrier ℚ →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) where
  toFun := AdelicFnCarrier.toFn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable abbrev stableAction (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) : DistribMulAction (GL (Fin 2) ℚ_[q]) ↥Z where
  smul x z := ⟨x • z.1, hZst x z.1 z.2⟩
  one_smul z := Subtype.ext (one_smul _ z.1)
  mul_smul x y z := Subtype.ext (mul_smul x y z.1)
  smul_zero x := Subtype.ext (smul_zero x)
  smul_add x a b := Subtype.ext (smul_add x a.1 b.1)

private theorem stableAction_coe_smul (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) (x : GL (Fin 2) ℚ_[q]) (z : ↥Z) :
    letI := stableAction q Z hZst
    ((x • z : ↥Z) : AdelicFnCarrier ℚ) = x • (z : AdelicFnCarrier ℚ) := by
  letI := stableAction q Z hZst
  rfl

private theorem stableAction_smulCommClass (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) :
    letI := stableAction q Z hZst
    SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ ↥Z :=
  letI := stableAction q Z hZst
  ⟨fun x c z => Subtype.ext (smul_comm x c z.1)⟩

private theorem stableAction_finite_image (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) (U : Set (GL (Fin 2) ℚ_[q])) (z : ↥Z)
    (hfin : Set.Finite ((fun k : GL (Fin 2) ℚ_[q] => k • (z : AdelicFnCarrier ℚ)) '' U)) :
    letI := stableAction q Z hZst
    Set.Finite ((fun k : GL (Fin 2) ℚ_[q] => k • z) '' U) := by
  letI := stableAction q Z hZst
  refine Set.Finite.of_finite_image (f := fun w : ↥Z => (w : AdelicFnCarrier ℚ)) (hfin.subset ?_) ?_
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · intro a _ b _ hab
    exact Subtype.ext hab

private theorem finiteDimensional_of_fixed (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) (U : Set (GL (Fin 2) ℚ_[q]))
    (C : Submodule ℂ (AdelicFnCarrier ℚ)) (hC : ∀ ψ : AdelicFnCarrier ℚ, ψ ∈ C ↔ ψ ∈ Z ∧ ∀ k ∈ U, k • ψ = ψ)
    [FiniteDimensional ℂ ↥C] (F₀ : Submodule ℂ ↥Z)
    (hF₀ : letI := stableAction q Z hZst; ∀ z : ↥Z, z ∈ F₀ ↔ ∀ k ∈ U, k • z = z) :
    FiniteDimensional ℂ ↥F₀ := by
  letI := stableAction q Z hZst
  let f : ↥F₀ →ₗ[ℂ] ↥C :=
    { toFun := fun w => ⟨((w : ↥Z) : AdelicFnCarrier ℚ), (hC _).mpr ⟨(w : ↥Z).2, fun k hk =>
        congrArg Subtype.val ((hF₀ (w : ↥Z)).mp w.2 k hk)⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective f fun a b hab => ?_
  have h : ((f a : ↥C) : AdelicFnCarrier ℚ) = ((f b : ↥C) : AdelicFnCarrier ℚ) := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h)

private theorem fixed_ne_bot (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) (U : Set (GL (Fin 2) ℚ_[q]))
    (C : Submodule ℂ (AdelicFnCarrier ℚ)) (hC : ∀ ψ : AdelicFnCarrier ℚ, ψ ∈ C ↔ ψ ∈ Z ∧ ∀ k ∈ U, k • ψ = ψ)
    (hCne : C ≠ ⊥) (F₀ : Submodule ℂ ↥Z)
    (hF₀ : letI := stableAction q Z hZst; ∀ z : ↥Z, z ∈ F₀ ↔ ∀ k ∈ U, k • z = z) :
    F₀ ≠ ⊥ := by
  letI := stableAction q Z hZst
  obtain ⟨ψ, hψC, hψ0⟩ := (Submodule.ne_bot_iff C).mp hCne
  obtain ⟨hψZ, hfix⟩ := (hC ψ).mp hψC
  refine (Submodule.ne_bot_iff F₀).mpr ⟨⟨ψ, hψZ⟩, (hF₀ _).mpr fun k hk => Subtype.ext (hfix k hk), fun h => ?_⟩
  exact hψ0 (congrArg Subtype.val h)

private theorem exists_irreducible_stable_le_of_subtype (q : ℕ) [Fact q.Prime]
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZV : ∀ ψ ∈ Z, ψ.toFn ∈ V) [DistribMulAction (GL (Fin 2) ℚ_[q]) ↥Z]
    (hact : ∀ (x : GL (Fin 2) ℚ_[q]) (z : ↥Z), ((x • z : ↥Z) : AdelicFnCarrier ℚ) = x • (z : AdelicFnCarrier ℚ))
    (W : Submodule ℂ ↥Z) (hWne : W ≠ ⊥) (hWst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ w ∈ W, x • w ∈ W)
    (hWmin : ∀ Z' : Submodule ℂ ↥Z, Z' ≤ W → (∀ (x : GL (Fin 2) ℚ_[q]), ∀ z ∈ Z', x • z ∈ Z') →
      Z' = ⊥ ∨ Z' = W) :
    ∃ W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ), W₀ ≤ V ∧ W₀ ≠ ⊥ ∧
      (∀ (x : GL (Fin 2) ℚ_[q]) (ψ : AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀) ∧
      ∀ W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ), W' ≤ W₀ →
        (∀ (x : GL (Fin 2) ℚ_[q]) (ψ : AdelicFnCarrier ℚ), ψ.toFn ∈ W' → (x • ψ).toFn ∈ W') →
        W' = ⊥ ∨ W' = W₀ := by
  have toFn_injective : Function.Injective (AdelicFnCarrier.toFn (F := ℚ)) :=
    fun φ ψ h => AdelicFnCarrier.ext (fun g => congrFun h g)
  let W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) := (W.map Z.subtype).map carrierToFn
  have memW₀ : ∀ f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, f ∈ W₀ ↔ ∃ w ∈ W, (w : AdelicFnCarrier ℚ).toFn = f := by
    intro f
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(w : AdelicFnCarrier ℚ), ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨W₀, ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨w, _, rfl⟩ := (memW₀ f).mp hf
    exact hZV _ w.2
  · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hWne
    intro hbot
    apply hw0
    have hf : (w : AdelicFnCarrier ℚ).toFn ∈ W₀ := (memW₀ _).mpr ⟨w, hw, rfl⟩
    rw [hbot, Submodule.mem_bot] at hf
    exact Subtype.ext (toFn_injective (by simpa using hf))
  · intro x ψ hψ
    obtain ⟨w, hw, hwψ⟩ := (memW₀ _).mp hψ
    have hψw : ψ = (w : AdelicFnCarrier ℚ) := toFn_injective hwψ.symm
    subst hψw
    refine (memW₀ _).mpr ⟨x • w, hWst x w hw, ?_⟩
    rw [hact]
  · intro W' hW'le hW'st
    let Z' : Submodule ℂ ↥Z := W ⊓ W'.comap (carrierToFn ∘ₗ Z.subtype)
    have hZ'st : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ z ∈ Z', x • z ∈ Z' := by
      intro x z hz
      obtain ⟨hzW, hzW'⟩ := Submodule.mem_inf.mp hz
      refine Submodule.mem_inf.mpr ⟨hWst x z hzW, Submodule.mem_comap.mpr ?_⟩
      show ((x • z : ↥Z) : AdelicFnCarrier ℚ).toFn ∈ W'
      rw [hact]
      exact hW'st x _ (Submodule.mem_comap.mp hzW')
    rcases hWmin Z' inf_le_left hZ'st with h | h
    · left
      refine (Submodule.eq_bot_iff W').mpr fun f hf => ?_
      obtain ⟨w, hw, rfl⟩ := (memW₀ f).mp (hW'le hf)
      have hwZ' : w ∈ Z' := Submodule.mem_inf.mpr ⟨hw, Submodule.mem_comap.mpr hf⟩
      rw [h, Submodule.mem_bot] at hwZ'
      simp [hwZ']
    · right
      refine le_antisymm hW'le fun f hf => ?_
      obtain ⟨w, hw, rfl⟩ := (memW₀ f).mp hf
      have hwZ' : w ∈ Z' := h ▸ hw
      exact Submodule.mem_comap.mp (Submodule.mem_inf.mp hwZ').2

end LocalNewvector.AwayCarrier

end

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace InvariantComplement
p2m_open "LocalNewvector"

variable {G : Type*} [Group G] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
  [DistribMulAction G Y] [SMulCommClass G ℂ Y]

private def fixedSubmodule (U : Subgroup G) : Submodule ℂ Y where
  carrier := {y | ∀ k ∈ U, k • y = y}
  zero_mem' := fun k _ => smul_zero k
  add_mem' := fun {a b} ha hb k hk => by rw [smul_add, ha k hk, hb k hk]
  smul_mem' := fun c {a} ha k hk => by rw [smul_comm k c a, ha k hk]

private def diffSubmodule (U : Subgroup G) : Submodule ℂ Y :=
  Submodule.span ℂ {d | ∃ k ∈ U, ∃ y : Y, d = k • y - y}

private def orbitSet (U : Subgroup G) (y : Y) : Set Y :=
  (fun k : G => k • y) '' (U : Set G)

variable {U : Subgroup G}

omit [SMulCommClass G ℂ Y] in
private theorem smul_sub_self_mem_diffSubmodule {k : G} (hk : k ∈ U) (y : Y) : k • y - y ∈ diffSubmodule U :=
  Submodule.subset_span ⟨k, hk, y, rfl⟩

omit [Module ℂ Y] [SMulCommClass G ℂ Y] in
private theorem self_mem_orbitSet (y : Y) : y ∈ orbitSet U y :=
  ⟨1, U.one_mem, one_smul G y⟩

omit [Module ℂ Y] [SMulCommClass G ℂ Y] in
private theorem image_smul_orbitSet {k : G} (hk : k ∈ U) (y : Y) :
    (fun z : Y => k • z) '' orbitSet U y = orbitSet U y := by
  ext z
  constructor
  · rintro ⟨_, ⟨k', hk', rfl⟩, rfl⟩
    exact ⟨k * k', U.mul_mem hk hk', mul_smul k k' y⟩
  · rintro ⟨k', hk', rfl⟩
    exact ⟨k⁻¹ • k' • y, ⟨k⁻¹ * k', U.mul_mem (U.inv_mem hk) hk', mul_smul _ _ _⟩, smul_inv_smul k _⟩

private noncomputable def orbitAvg (U : Subgroup G) (y : Y) (h : (orbitSet U y).Finite) : Y :=
  ((h.toFinset.card : ℂ)⁻¹) • ∑ z ∈ h.toFinset, z

private theorem smul_orbitAvg {k : G} (hk : k ∈ U) (y : Y) (h : (orbitSet U y).Finite) :
    k • orbitAvg U y h = orbitAvg U y h := by
  classical
  unfold orbitAvg
  rw [smul_comm k, Finset.smul_sum]
  congr 1
  have himg : h.toFinset.image (fun z : Y => k • z) = h.toFinset := by
    rw [← Finset.coe_inj, Finset.coe_image, Set.Finite.coe_toFinset, image_smul_orbitSet hk]
  calc ∑ z ∈ h.toFinset, k • z = ∑ z ∈ h.toFinset.image (fun z : Y => k • z), z :=
        (Finset.sum_image (f := fun z => z) fun a _ b _ hab => MulAction.injective k hab).symm
    _ = ∑ z ∈ h.toFinset, z := by rw [himg]

omit [SMulCommClass G ℂ Y] in
private theorem orbitAvg_sub_self_mem_diffSubmodule (y : Y) (h : (orbitSet U y).Finite) :
    orbitAvg U y h - y ∈ diffSubmodule U := by
  have hne : h.toFinset.card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨y, (Set.Finite.mem_toFinset h).mpr (self_mem_orbitSet y)⟩
  have key : ((h.toFinset.card : ℂ)⁻¹) • ∑ z ∈ h.toFinset, (z - y) = orbitAvg U y h - y := by
    unfold orbitAvg
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hne), one_smul]
  rw [← key]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => ?_)
  obtain ⟨k, hk, rfl⟩ := (Set.Finite.mem_toFinset h).mp hz
  exact smul_sub_self_mem_diffSubmodule hk y

omit [SMulCommClass G ℂ Y] in
private theorem orbitAvg_mem_of_stable {Z : Submodule ℂ Y} (hZ : ∀ k ∈ U, ∀ z ∈ Z, k • z ∈ Z) {y : Y} (hy : y ∈ Z)
    (h : (orbitSet U y).Finite) : orbitAvg U y h ∈ Z := by
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => ?_)
  obtain ⟨k, hk, rfl⟩ := (Set.Finite.mem_toFinset h).mp hz
  exact hZ k hk y hy

section Form

variable (B : Y → Y → ℂ)

private theorem apply_fixed_diff_eq_zero (hB_addr : ∀ w d₁ d₂ : Y, B w (d₁ + d₂) = B w d₁ + B w d₂)
    (hB_smulr : ∀ (c : ℂ) (w d : Y), B w d = 0 → B w (c • d) = 0)
    (hB_inv : ∀ k ∈ U, ∀ y z : Y, B (k • y) (k • z) = B y z)
    {w : Y} (hw : w ∈ fixedSubmodule U) {d : Y} (hd : d ∈ diffSubmodule U) : B w d = 0 := by
  have hzero : B w 0 = 0 := by
    have h2 := hB_addr w 0 0
    rw [add_zero] at h2
    have h3 : B w 0 + B w 0 = B w 0 + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel h3
  have hneg : ∀ y : Y, B w (-y) = -B w y := fun y => by
    have h3 := hB_addr w y (-y)
    rw [add_neg_cancel, hzero] at h3
    exact (neg_eq_of_add_eq_zero_right h3.symm).symm
  induction hd using Submodule.span_induction with
  | mem d hdg =>
    obtain ⟨k, hk, y, rfl⟩ := hdg
    have h1 : B w (k • y) = B w y := by
      conv_lhs => rw [← hw k hk]
      exact hB_inv k hk w y
    rw [sub_eq_add_neg, hB_addr, h1, hneg y, add_neg_cancel]
  | zero => exact hzero
  | add d₁ d₂ _ _ h₁ h₂ => rw [hB_addr, h₁, h₂, add_zero]
  | smul c d _ h₁ => exact hB_smulr c w d h₁

private theorem apply_diff_fixed_eq_zero (hB_addl : ∀ y₁ y₂ z : Y, B (y₁ + y₂) z = B y₁ z + B y₂ z)
    (hB_smull : ∀ (c : ℂ) (y z : Y), B y z = 0 → B (c • y) z = 0)
    (hB_inv : ∀ k ∈ U, ∀ y z : Y, B (k • y) (k • z) = B y z)
    {d : Y} (hd : d ∈ diffSubmodule U) {w : Y} (hw : w ∈ fixedSubmodule U) : B d w = 0 := by
  have hzero : B 0 w = 0 := by
    have h2 := hB_addl 0 0 w
    rw [add_zero] at h2
    have h3 : B 0 w + B 0 w = B 0 w + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel h3
  have hneg : ∀ y : Y, B (-y) w = -B y w := fun y => by
    have h3 := hB_addl y (-y) w
    rw [add_neg_cancel, hzero] at h3
    exact (neg_eq_of_add_eq_zero_right h3.symm).symm
  induction hd using Submodule.span_induction with
  | mem d hdg =>
    obtain ⟨k, hk, y, rfl⟩ := hdg
    have h1 : B (k • y) w = B y w := by
      conv_lhs => rw [← hw k hk]
      exact hB_inv k hk y w
    rw [sub_eq_add_neg, hB_addl, h1, hneg y, add_neg_cancel]
  | zero => exact hzero
  | add d₁ d₂ _ _ h₁ h₂ => rw [hB_addl, h₁, h₂, add_zero]
  | smul c d _ h₁ => exact hB_smull c d w h₁

private theorem fixedSubmodule_inf_diffSubmodule_eq_bot
    (hB_addr : ∀ w d₁ d₂ : Y, B w (d₁ + d₂) = B w d₁ + B w d₂)
    (hB_smulr : ∀ (c : ℂ) (w d : Y), B w d = 0 → B w (c • d) = 0)
    (hB_inv : ∀ k ∈ U, ∀ y z : Y, B (k • y) (k • z) = B y z) (hB_def : ∀ z : Y, B z z = 0 → z = 0) :
    fixedSubmodule U ⊓ diffSubmodule U = (⊥ : Submodule ℂ Y) :=
  (Submodule.eq_bot_iff _).mpr fun w hw =>
    hB_def w (apply_fixed_diff_eq_zero B hB_addr hB_smulr hB_inv hw.1 hw.2)

end Form

section Projection

variable (U)

private theorem eq_zero_of_mem_fixed_of_mem_diff (hbot : fixedSubmodule U ⊓ diffSubmodule U = (⊥ : Submodule ℂ Y))
    {a : Y} (ha : a ∈ fixedSubmodule U) (hd : a ∈ diffSubmodule U) : a = 0 :=
  (Submodule.eq_bot_iff _).mp hbot a ⟨ha, hd⟩

private noncomputable def avgMap (hfin : ∀ y : Y, (orbitSet U y).Finite)
    (hbot : fixedSubmodule U ⊓ diffSubmodule U = (⊥ : Submodule ℂ Y)) : Y →ₗ[ℂ] Y where
  toFun y := orbitAvg U y (hfin y)
  map_add' y₁ y₂ := by
    have hF : orbitAvg U (y₁ + y₂) (hfin _) - (orbitAvg U y₁ (hfin _) + orbitAvg U y₂ (hfin _))
        ∈ fixedSubmodule U :=
      Submodule.sub_mem _ (fun k hk => smul_orbitAvg hk _ _)
        (Submodule.add_mem _ (fun k hk => smul_orbitAvg hk _ _) (fun k hk => smul_orbitAvg hk _ _))
    have h1 : y₁ - orbitAvg U y₁ (hfin _) ∈ diffSubmodule U := by
      rw [← neg_sub]; exact Submodule.neg_mem _ (orbitAvg_sub_self_mem_diffSubmodule y₁ (hfin _))
    have h2 : y₂ - orbitAvg U y₂ (hfin _) ∈ diffSubmodule U := by
      rw [← neg_sub]; exact Submodule.neg_mem _ (orbitAvg_sub_self_mem_diffSubmodule y₂ (hfin _))
    have hD : orbitAvg U (y₁ + y₂) (hfin _) - (orbitAvg U y₁ (hfin _) + orbitAvg U y₂ (hfin _))
        ∈ diffSubmodule U := by
      rw [← sub_add_sub_cancel (orbitAvg U (y₁ + y₂) (hfin _)) (y₁ + y₂)
        (orbitAvg U y₁ (hfin _) + orbitAvg U y₂ (hfin _)), add_sub_add_comm]
      exact Submodule.add_mem _ (orbitAvg_sub_self_mem_diffSubmodule _ (hfin _)) (Submodule.add_mem _ h1 h2)
    exact sub_eq_zero.mp (eq_zero_of_mem_fixed_of_mem_diff U hbot hF hD)
  map_smul' c y := by
    have hF : orbitAvg U (c • y) (hfin _) - c • orbitAvg U y (hfin _) ∈ fixedSubmodule U :=
      Submodule.sub_mem _ (fun k hk => smul_orbitAvg hk _ _)
        (Submodule.smul_mem _ c (fun k hk => smul_orbitAvg hk _ _))
    have h1 : y - orbitAvg U y (hfin _) ∈ diffSubmodule U := by
      rw [← neg_sub]; exact Submodule.neg_mem _ (orbitAvg_sub_self_mem_diffSubmodule y (hfin _))
    have hD : orbitAvg U (c • y) (hfin _) - c • orbitAvg U y (hfin _) ∈ diffSubmodule U := by
      rw [← sub_add_sub_cancel (orbitAvg U (c • y) (hfin _)) (c • y) (c • orbitAvg U y (hfin _)), ← smul_sub]
      exact Submodule.add_mem _ (orbitAvg_sub_self_mem_diffSubmodule _ (hfin _)) (Submodule.smul_mem _ c h1)
    exact sub_eq_zero.mp (eq_zero_of_mem_fixed_of_mem_diff U hbot hF hD)

variable {U}
variable {hfin : ∀ y : Y, (orbitSet U y).Finite}
  {hbot : fixedSubmodule U ⊓ diffSubmodule U = (⊥ : Submodule ℂ Y)}

private theorem avgMap_apply (y : Y) : avgMap U hfin hbot y = orbitAvg U y (hfin y) := rfl

private theorem avgMap_mem_fixedSubmodule (y : Y) : avgMap U hfin hbot y ∈ fixedSubmodule U :=
  fun _ hk => smul_orbitAvg hk y (hfin y)

private theorem self_sub_avgMap_mem_diffSubmodule (y : Y) : y - avgMap U hfin hbot y ∈ diffSubmodule U := by
  rw [← neg_sub]; exact Submodule.neg_mem _ (orbitAvg_sub_self_mem_diffSubmodule y (hfin y))

private theorem avgMap_eq_self_of_mem {y : Y} (hy : y ∈ fixedSubmodule U) : avgMap U hfin hbot y = y :=
  sub_eq_zero.mp (eq_zero_of_mem_fixed_of_mem_diff U hbot
    (Submodule.sub_mem _ (avgMap_mem_fixedSubmodule y) hy) (orbitAvg_sub_self_mem_diffSubmodule y (hfin y)))

private theorem avgMap_mem_of_stable {Z : Submodule ℂ Y} (hZ : ∀ k ∈ U, ∀ z ∈ Z, k • z ∈ Z) {y : Y} (hy : y ∈ Z) :
    avgMap U hfin hbot y ∈ Z :=
  orbitAvg_mem_of_stable hZ hy (hfin y)

private theorem apply_avgMap_comm (B : Y → Y → ℂ)
    (hB_addl : ∀ y₁ y₂ z : Y, B (y₁ + y₂) z = B y₁ z + B y₂ z)
    (hB_addr : ∀ w d₁ d₂ : Y, B w (d₁ + d₂) = B w d₁ + B w d₂)
    (hB_smull : ∀ (c : ℂ) (y z : Y), B y z = 0 → B (c • y) z = 0)
    (hB_smulr : ∀ (c : ℂ) (w d : Y), B w d = 0 → B w (c • d) = 0)
    (hB_inv : ∀ k ∈ U, ∀ y z : Y, B (k • y) (k • z) = B y z) (y z : Y) :
    B (avgMap U hfin hbot y) z = B y (avgMap U hfin hbot z) := by
  have r1 : B (avgMap U hfin hbot y) z = B (avgMap U hfin hbot y) (avgMap U hfin hbot z) := by
    conv_lhs => rw [← add_sub_cancel (avgMap U hfin hbot z) z]
    rw [hB_addr, apply_fixed_diff_eq_zero B hB_addr hB_smulr hB_inv (avgMap_mem_fixedSubmodule y)
      (self_sub_avgMap_mem_diffSubmodule z), add_zero]
  have r2 : B y (avgMap U hfin hbot z) = B (avgMap U hfin hbot y) (avgMap U hfin hbot z) := by
    conv_lhs => rw [← add_sub_cancel (avgMap U hfin hbot y) y]
    rw [hB_addl, apply_diff_fixed_eq_zero B hB_addl hB_smull hB_inv (self_sub_avgMap_mem_diffSubmodule y)
      (avgMap_mem_fixedSubmodule z), add_zero]
  rw [r1, r2]

end Projection

private theorem exists_linearMap_fixedSubmodule (U : Subgroup G) (B : Y → Y → ℂ)
    (hB_addl : ∀ y₁ y₂ z : Y, B (y₁ + y₂) z = B y₁ z + B y₂ z)
    (hB_addr : ∀ w d₁ d₂ : Y, B w (d₁ + d₂) = B w d₁ + B w d₂)
    (hB_smull : ∀ (c : ℂ) (y z : Y), B y z = 0 → B (c • y) z = 0)
    (hB_smulr : ∀ (c : ℂ) (w d : Y), B w d = 0 → B w (c • d) = 0)
    (hB_inv : ∀ k ∈ U, ∀ y z : Y, B (k • y) (k • z) = B y z) (hB_def : ∀ z : Y, B z z = 0 → z = 0)
    (hfin : ∀ y : Y, ((fun k : G => k • y) '' (U : Set G)).Finite) :
    ∃ e : Y →ₗ[ℂ] Y, (∀ y : Y, e y ∈ fixedSubmodule U) ∧ (∀ y ∈ fixedSubmodule U, e y = y) ∧
      (∀ y z : Y, B (e y) z = B y (e z)) ∧
      (∀ Z : Submodule ℂ Y, (∀ (g : G), ∀ z ∈ Z, g • z ∈ Z) → ∀ z ∈ Z, e z ∈ Z) :=
  have hbot := fixedSubmodule_inf_diffSubmodule_eq_bot B hB_addr hB_smulr hB_inv hB_def
  ⟨avgMap U hfin hbot, avgMap_mem_fixedSubmodule, fun _ hy => avgMap_eq_self_of_mem hy,
    apply_avgMap_comm B hB_addl hB_addr hB_smull hB_smulr hB_inv,
    fun _ hZ _ hz => avgMap_mem_of_stable (fun k _ => hZ k) hz⟩

end LocalNewvector.InvariantComplement

end

section

open NumberField

section Integral

variable (N : Ideal (𝓞 ℚ))

private theorem det_mem_integralFiniteAdeles {m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hm : AdelicLevel.IsLevelOneMatrix (𝓞 ℚ) ℚ N m) : m.det ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  rw [Matrix.det_fin_two]
  exact AdelicLevel.sub_mem_integralFiniteAdeles
    (AdelicLevel.mul_mem_integralFiniteAdeles (hm.integral 0 0) (hm.integral 1 1))
    (AdelicLevel.mul_mem_integralFiniteAdeles (hm.integral 0 1) (hm.integral 1 0))

private theorem det_mem_unitIdeles {g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hg : g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ N) :
    Matrix.GeneralLinearGroup.det g ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ := by
  obtain ⟨h₁, h₂⟩ := AdelicLevel.mem_finiteLevelOne_iff.mp hg
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_integralFiniteAdeles N h₁ v
  · rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_integralFiniteAdeles N h₂ v

end Integral

section Padic

variable (q : ℕ) [Fact q.Prime] (N : Ideal (𝓞 ℚ))

private theorem det_padicToAdelic_fst (k : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]) :
    ((Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q k) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
  have harch : ((AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q k) :
        Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) = 1 := by
    rw [AdelicDock.glArch_padicToAdelic, Units.val_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_one (R := InfiniteAdeleRing ℚ) (n := Fin 2), ← harch,
    Matrix.det_fin_two, Matrix.det_fin_two]
  rfl

private theorem finitePartUnits_det_padicToAdelic_mem {k : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]}
    (hk : AdelicDock.padicToAdelic q k ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N) :
    NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q k)) ∈
      IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ := by
  have hfin := det_mem_unitIdeles N (AdelicLevel.mem_levelOne_iff.mp hk)

  have hdet : NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ
        (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q k)) =
      Matrix.GeneralLinearGroup.det (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q k)) := by
    apply Units.ext
    rw [NumberField.AdeleRing.val_finitePartUnits, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
    rfl
  rw [hdet]
  exact hfin

private theorem ideleNorm_det_padicToAdelic_eq_one (k : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q])
    (hk : k ∈ (AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ).comap
      (AdelicDock.padicToAdelic q)) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q k)) = 1 :=
  NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ _
    (det_padicToAdelic_fst q k)
    (finitePartUnits_det_padicToAdelic_mem q N (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hk)).1)

end Padic

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace CarrierForm
p2m_open "LocalNewvector"

variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hΦ₀ : IsSlabFundamentalDomain ℚ α β Φ₀) (σ : ℝ)
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ) →* ℂˣ)
  {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (ι : Y →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
  (hι : ∀ y : Y, ι y ∈ contMemberSubmodule ℚ Φ₀ ξ)

private noncomputable def cmap : Y →ₗ[ℂ] Carrier ℚ Φ₀ σ :=
  (toCarrier ℚ hΦ₀ σ ξ) ∘ₗ LinearMap.codRestrict (memberSubmodule ℚ Φ₀ ξ) ι (fun y => (hι y).1)

private theorem cmap_apply (y : Y) : cmap hΦ₀ σ ξ ι hι y = toCarrier ℚ hΦ₀ σ ξ ⟨ι y, (hι y).1⟩ := rfl

private noncomputable def form (y z : Y) : ℂ :=
  ⟪cmap hΦ₀ σ ξ ι hι y, cmap hΦ₀ σ ξ ι hι z⟫_ℂ

private theorem form_add_left (y₁ y₂ z : Y) :
    form hΦ₀ σ ξ ι hι (y₁ + y₂) z = form hΦ₀ σ ξ ι hι y₁ z + form hΦ₀ σ ξ ι hι y₂ z := by
  unfold form; rw [map_add, inner_add_left]

private theorem form_add_right (y z₁ z₂ : Y) :
    form hΦ₀ σ ξ ι hι y (z₁ + z₂) = form hΦ₀ σ ξ ι hι y z₁ + form hΦ₀ σ ξ ι hι y z₂ := by
  unfold form; rw [map_add, inner_add_right]

private theorem form_smul_left_eq_zero (c : ℂ) (y z : Y) (h : form hΦ₀ σ ξ ι hι y z = 0) :
    form hΦ₀ σ ξ ι hι (c • y) z = 0 := by
  unfold form at h ⊢; rw [map_smul, inner_smul_left, h, mul_zero]

private theorem form_smul_right_eq_zero (c : ℂ) (y z : Y) (h : form hΦ₀ σ ξ ι hι y z = 0) :
    form hΦ₀ σ ξ ι hι y (c • z) = 0 := by
  unfold form at h ⊢; rw [map_smul, inner_smul_right, h, mul_zero]

private theorem form_zero_right (y : Y) : form hΦ₀ σ ξ ι hι y 0 = 0 := by
  unfold form; rw [map_zero, inner_zero_right]

private theorem eq_zero_of_form_self_eq_zero (hιinj : Function.Injective ι) (z : Y) (h : form hΦ₀ σ ξ ι hι z z = 0) :
    z = 0 := by
  unfold form at h
  have h0 : toCarrier ℚ hΦ₀ σ ξ ⟨ι z, (hι z).1⟩ = 0 := inner_self_eq_zero.mp h
  have hz : ι z = 0 := eq_zero_of_toCarrier_eq_zero ℚ hΦ₀ σ ξ (ι z) (hι z) h0
  exact hιinj (hz.trans (map_zero ι).symm)

section Local

variable (q : ℕ) [Fact q.Prime] [DistribMulAction (GL (Fin 2) ℚ_[q]) Y]
  (hιsmul : ∀ (x : GL (Fin 2) ℚ_[q]) (y : Y), ι (x • y) = rightTranslate ℚ (AdelicDock.padicToAdelic q x) (ι y))

include hιsmul

private theorem form_smul_left (x : GL (Fin 2) ℚ_[q])
    (hlift : ∃ T T' : Carrier ℚ Φ₀ σ →L[ℂ] Carrier ℚ Φ₀ σ,
      IsLift ℚ hΦ₀ σ ξ (rightTranslate ℚ (AdelicDock.padicToAdelic q x)) T ∧
      IsLift ℚ hΦ₀ σ ξ (rightTranslate ℚ (AdelicDock.padicToAdelic q x)⁻¹) T' ∧
      ContinuousLinearMap.adjoint T =
        ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x)) ^ σ
          : ℝ) : ℂ) • T')
    (y z : Y) :
    form hΦ₀ σ ξ ι hι (x • y) z =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x)) ^ σ
          : ℝ) : ℂ) * form hΦ₀ σ ξ ι hι y (x⁻¹ • z) := by
  obtain ⟨T, T', hT, hT', hadj⟩ := hlift
  have hy : cmap hΦ₀ σ ξ ι hι (x • y) = T (cmap hΦ₀ σ ξ ι hι y) := by
    rw [cmap_apply, cmap_apply, hT.comm (ι y) (hι y)]
    congr 1
    exact Subtype.ext (hιsmul x y)
  have hz : cmap hΦ₀ σ ξ ι hι (x⁻¹ • z) = T' (cmap hΦ₀ σ ξ ι hι z) := by
    rw [cmap_apply, cmap_apply, hT'.comm (ι z) (hι z)]
    congr 1
    apply Subtype.ext
    show ι (x⁻¹ • z) = rightTranslate ℚ (AdelicDock.padicToAdelic q x)⁻¹ (ι z)
    rw [hιsmul, map_inv]
  unfold form
  rw [hy, hz, ← ContinuousLinearMap.adjoint_inner_right, hadj, ContinuousLinearMap.smul_apply, inner_smul_right]

private theorem form_smul_left_eq_zero_of (x : GL (Fin 2) ℚ_[q])
    (hlift : ∃ T T' : Carrier ℚ Φ₀ σ →L[ℂ] Carrier ℚ Φ₀ σ,
      IsLift ℚ hΦ₀ σ ξ (rightTranslate ℚ (AdelicDock.padicToAdelic q x)) T ∧
      IsLift ℚ hΦ₀ σ ξ (rightTranslate ℚ (AdelicDock.padicToAdelic q x)⁻¹) T' ∧
      ContinuousLinearMap.adjoint T =
        ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x)) ^ σ
          : ℝ) : ℂ) • T')
    (y z : Y) (h : form hΦ₀ σ ξ ι hι y (x⁻¹ • z) = 0) : form hΦ₀ σ ξ ι hι (x • y) z = 0 := by
  rw [form_smul_left hΦ₀ σ ξ ι hι q hιsmul x hlift y z, h, mul_zero]

private theorem form_smul_smul (x : GL (Fin 2) ℚ_[q])
    (hlift : ∃ T T' : Carrier ℚ Φ₀ σ →L[ℂ] Carrier ℚ Φ₀ σ,
      IsLift ℚ hΦ₀ σ ξ (rightTranslate ℚ (AdelicDock.padicToAdelic q x)) T ∧
      IsLift ℚ hΦ₀ σ ξ (rightTranslate ℚ (AdelicDock.padicToAdelic q x)⁻¹) T' ∧
      ContinuousLinearMap.adjoint T =
        ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x)) ^ σ
          : ℝ) : ℂ) • T')
    (hdet : NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x)) = 1)
    (y z : Y) : form hΦ₀ σ ξ ι hι (x • y) (x • z) = form hΦ₀ σ ξ ι hι y z := by
  rw [form_smul_left hΦ₀ σ ξ ι hι q hιsmul x hlift y (x • z), inv_smul_smul, hdet, Real.one_rpow,
    Complex.ofReal_one, one_mul]

end Local

end LocalNewvector.CarrierForm

end

section

private theorem exists_irreducible_stable_submodule_of_finiteDimensional_projection
    (G : Type) [Group G]
    (Y : Type) [AddCommGroup Y] [Module ℂ Y] [DistribMulAction G Y] [SMulCommClass G ℂ Y]
    (B : Y → Y → ℂ)
    (hB_add : ∀ y₁ y₂ z : Y, B (y₁ + y₂) z = B y₁ z + B y₂ z)
    (hB_smul : ∀ (c : ℂ) (y z : Y), B y z = 0 → B (c • y) z = 0)
    (hB_inv : ∀ (g : G) (y z : Y), B y (g⁻¹ • z) = 0 → B (g • y) z = 0)
    (hB_zero : ∀ y : Y, B y 0 = 0) (hB_def : ∀ z : Y, B z z = 0 → z = 0)
    (F₀ : Submodule ℂ Y) [FiniteDimensional ℂ F₀] (hF₀ne : F₀ ≠ ⊥)
    (e : Y →ₗ[ℂ] Y) (he_mem : ∀ y : Y, e y ∈ F₀) (he_id : ∀ y ∈ F₀, e y = y)
    (he_adj : ∀ y z : Y, B (e y) z = B y (e z))
    (he_stable : ∀ Z : Submodule ℂ Y, (∀ (g : G), ∀ z ∈ Z, g • z ∈ Z) → ∀ z ∈ Z, e z ∈ Z) :
    ∃ W : Submodule ℂ Y, W ≠ ⊥ ∧ (∀ (g : G), ∀ w ∈ W, g • w ∈ W) ∧
      W ≤ Submodule.span ℂ {w : Y | ∃ (g : G) (y : Y), y ∈ W ⊓ F₀ ∧ w = g • y} ∧
      ∀ Z : Submodule ℂ Y, Z ≤ W → (∀ (g : G), ∀ z ∈ Z, g • z ∈ Z) → Z = ⊥ ∨ Z = W := by
  classical

  have hex : ∃ n : ℕ, ∃ W' : Submodule ℂ Y, (∀ (g : G), ∀ w ∈ W', g • w ∈ W') ∧ W' ⊓ F₀ ≠ ⊥ ∧
      Module.finrank ℂ ↥(W' ⊓ F₀) = n :=
    ⟨_, ⊤, fun _ _ _ => Submodule.mem_top, by simpa using hF₀ne, rfl⟩
  obtain ⟨W', hW'st, hW'ne, hW'rank⟩ := Nat.find_spec hex
  have hmin : ∀ Z : Submodule ℂ Y, (∀ (g : G), ∀ z ∈ Z, g • z ∈ Z) → Z ⊓ F₀ ≠ ⊥ →
      Nat.find hex ≤ Module.finrank ℂ ↥(Z ⊓ F₀) :=
    fun Z hZst hZne => Nat.find_min' hex ⟨Z, hZst, hZne, rfl⟩
  haveI : FiniteDimensional ℂ ↥(W' ⊓ F₀) := Submodule.finiteDimensional_of_le inf_le_right

  set S : Set Y := {w : Y | ∃ (g : G) (y : Y), y ∈ W' ⊓ F₀ ∧ w = g • y}
  set W : Submodule ℂ Y := Submodule.span ℂ S
  have hmeet_sub : ∀ y ∈ W' ⊓ F₀, y ∈ W := fun y hy =>
    Submodule.subset_span ⟨1, y, hy, (one_smul G y).symm⟩
  have hWst : ∀ (g : G), ∀ w ∈ W, g • w ∈ W := by
    intro g w hw
    refine Submodule.span_induction (p := fun w _ => g • w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨h, y, hy, rfl⟩
      exact Submodule.subset_span ⟨g * h, y, hy, (mul_smul g h y).symm⟩
    · show g • (0 : Y) ∈ W
      rw [smul_zero]
      exact W.zero_mem
    · intro a b _ _ ha hb
      show g • (a + b) ∈ W
      rw [smul_add]
      exact W.add_mem ha hb
    · intro c a _ ha
      show g • (c • a) ∈ W
      rw [smul_comm]
      exact W.smul_mem c ha
  have hWle : W ≤ W' := Submodule.span_le.mpr (by
    rintro _ ⟨g, y, hy, rfl⟩
    exact hW'st g y hy.1)
  refine ⟨W, ?_, hWst, ?_, ?_⟩
  ·
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hW'ne
    exact (Submodule.ne_bot_iff W).mpr ⟨y, hmeet_sub y hy, hy0⟩
  ·
    refine Submodule.span_mono ?_
    rintro _ ⟨g, y, hy, rfl⟩
    exact ⟨g, y, ⟨hmeet_sub y hy, hy.2⟩, rfl⟩
  ·
    intro Z hZle hZst
    by_cases hZ : Z ⊓ F₀ = ⊥
    · left

      have hgen : ∀ y ∈ W' ⊓ F₀, ∀ z ∈ Z, B y z = 0 := by
        intro y hy z hz
        have hez : e z ∈ Z ⊓ F₀ := ⟨he_stable Z hZst z hz, he_mem z⟩
        rw [hZ, Submodule.mem_bot] at hez
        calc B y z = B (e y) z := by rw [he_id y hy.2]
          _ = B y (e z) := he_adj y z
          _ = 0 := by rw [hez]; exact hB_zero y
      have horth : ∀ w ∈ W, ∀ z ∈ Z, B w z = 0 := by
        intro w hw
        refine Submodule.span_induction (p := fun w _ => ∀ z ∈ Z, B w z = 0) ?_ ?_ ?_ ?_ hw
        · rintro _ ⟨g, y, hy, rfl⟩ z hz
          exact hB_inv g y z (hgen y hy (g⁻¹ • z) (hZst g⁻¹ z hz))
        · intro z hz
          exact hgen 0 (Submodule.zero_mem _) z hz
        · intro a b _ _ ha hb z hz
          rw [hB_add, ha z hz, hb z hz, add_zero]
        · intro c a _ ha z hz
          exact hB_smul c a z (ha z hz)
      refine (Submodule.eq_bot_iff Z).mpr fun z hz => ?_
      exact hB_def z (horth z (hZle hz) z hz)
    · right

      have hle_meet : Z ⊓ F₀ ≤ W' ⊓ F₀ := inf_le_inf_right F₀ (hZle.trans hWle)
      have heq : Z ⊓ F₀ = W' ⊓ F₀ :=
        Submodule.eq_of_le_of_finrank_le hle_meet (by rw [hW'rank]; exact hmin Z hZst hZ)
      have hSZ : S ⊆ Z := by
        rintro _ ⟨g, y, hy, rfl⟩
        rw [← heq] at hy
        exact hZst g y hy.1
      exact le_antisymm hZle (Submodule.span_le.mpr hSZ)

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open FLT.SmoothVectors
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace Members
p2m_open "LocalNewvector"

private theorem rightTranslate_one (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : rightTranslate ℚ 1 φ = φ :=
  funext fun x => congrArg φ (mul_one x)

private theorem continuous_of_mem_cuspKFiniteSubmodule (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ cuspKFiniteSubmodule ℚ pins ξ) : Continuous f := by
  rw [cuspKFiniteSubmodule] at hf
  induction hf using Submodule.span_induction with
  | mem φ hφ => exact hφ.2.1
  | zero => exact continuous_const
  | add f g _ _ hfc hgc => exact hfc.add hgc
  | smul c f _ hfc => exact hfc.const_smul c

private theorem isKfSmooth_of_mem_cuspKFiniteSubmodule (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ cuspKFiniteSubmodule ℚ pins ξ) : IsKfSmooth ℚ f := by
  rw [cuspKFiniteSubmodule] at hf
  induction hf using Submodule.span_induction with
  | mem φ hφ =>
    have h := (hφ.1 1).2
    rwa [rightTranslate_one] at h
  | zero => exact isKfSmooth_zero ℚ
  | add f g _ _ hfs hgs =>
    rw [isKfSmooth_iff] at hfs hgs ⊢
    exact hfs.add hgs
  | smul c f _ hfs =>
    rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hfs ⊢
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ (RightTranslationFn.mk f)) (fun g hg => ?_) hfs
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    refine RightTranslationFn.ext fun x => ?_
    have hx : f (x * g) = f x := congrArg (fun h => RightTranslationFn.toFun h x) hg
    show c • f (x * g) = c • f x
    rw [hx]

section Window

variable (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
  (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
  (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
      (adelicBox ℚ)).Z →* ℂˣ)
  {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hΦ₀ : IsSlabFundamentalDomain ℚ α β Φ₀)

include hd hcov hΦ₀

private theorem mem_memberSubmodule_of_mem_cuspKFiniteSubmodule {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hf : f ∈ cuspKFiniteSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) ξ) :
    f ∈ memberSubmodule ℚ Φ₀ ξ := by
  rw [cuspKFiniteSubmodule] at hf
  induction hf using Submodule.span_induction with
  | mem φ hφ =>
    have h := (hφ.1 1).1.1
    rw [rightTranslate_one] at h
    exact isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre ℚ c u d₁ d₂ T hd hcov
      α β hΦ₀.pos Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ φ h
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hfm hgm => exact Submodule.add_mem _ hfm hgm
  | smul c f _ hfm => exact Submodule.smul_mem _ c hfm

private theorem mem_contMemberSubmodule_of_mem_cuspKFiniteSubmodule {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hf : f ∈ cuspKFiniteSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) ξ) :
    f ∈ contMemberSubmodule ℚ Φ₀ ξ := by
  show f ∈ memberSubmodule ℚ Φ₀ ξ ∧ Continuous f
  exact ⟨mem_memberSubmodule_of_mem_cuspKFiniteSubmodule c u d₁ d₂ T hd hcov ξ hΦ₀ hf,
    continuous_of_mem_cuspKFiniteSubmodule _ ξ hf⟩

end Window

end LocalNewvector.Members

end

section

open NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace Members
p2m_open "LocalNewvector"

private theorem padicToAdelic_mem_finiteAdelicGL2Subgroup (q : ℕ) [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) :
    AdelicDock.padicToAdelic q x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_padicToAdelic q x)

private theorem toFn_padic_smul (q : ℕ) [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) :
    (x • ψ).toFn = rightTranslate ℚ (AdelicDock.padicToAdelic q x) ψ.toFn :=
  funext fun y => by rw [AdelicFnCarrier.padic_smul_def, AdelicFnCarrier.toFn_smul, rightTranslate_apply]

private theorem toFn_smul_mem_of_isCuspSubrep (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hV : IsCuspSubrep ℚ pins ξ V) (q : ℕ) [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) (hψ : ψ.toFn ∈ V) : (x • ψ).toFn ∈ V := by
  rw [toFn_padic_smul]
  exact hV.rightTranslate_fin_mem _ (padicToAdelic_mem_finiteAdelicGL2Subgroup q x) _ hψ

private theorem toFn_smul_mem_of_isCuspConstituent (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hV : IsCuspConstituent ℚ pins ξ V) (q : ℕ) [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) (hψ : ψ.toFn ∈ V) : (x • ψ).toFn ∈ V :=
  toFn_smul_mem_of_isCuspSubrep pins ξ V hV.1 q x ψ hψ

end LocalNewvector.Members

end

section

open NumberField IsDedekindDomain

section Commute

private theorem adelicGL2_ext {x y : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (harch : AdelicLevel.glArch (𝓞 ℚ) ℚ x = AdelicLevel.glArch (𝓞 ℚ) ℚ y)
    (hfin : AdelicLevel.glFin (𝓞 ℚ) ℚ x = AdelicLevel.glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · exact congrArg (fun m : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) harch
  · exact congrArg (fun m : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) hfin

private theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one {g h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (hg : AdelicLevel.glArch (𝓞 ℚ) ℚ g = 1) (hh : AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1) : g * h = h * g := by
  refine adelicGL2_ext ?_ ?_
  · rw [map_mul, map_mul, hg, one_mul, mul_one]
  · rw [map_mul, map_mul, hh, one_mul, mul_one]

private theorem eq_archIncl_glArch_of_glFin_eq_one {h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (hh : AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1) :
    h = AutomorphicForm.adelicArchGLIncl ℚ (AdelicLevel.glArch (𝓞 ℚ) ℚ h) := by
  refine adelicGL2_ext ?_ ?_
  · rw [AutomorphicForm.glArch_adelicArchGLIncl]
  · rw [AutomorphicForm.glFin_adelicArchGLIncl, hh]

end Commute

section Transport

variable (u₀ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
  (Ψ' : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ) (c : ℂ)

private noncomputable def replaceFin (u₀ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (Ψ' : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ) (c : ℂ) :
    (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) where
  toFun h := fun x =>
    h (AutomorphicForm.adelicArchGLIncl ℚ (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * AdelicDock.finEmbed (𝓞 ℚ) ℚ u₀) *
      (Ψ' (AdelicLevel.glFin (𝓞 ℚ) ℚ x) / c)
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' a h := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

private theorem archIncl_glArch_mul_finEmbed_mul {k : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (hk : AdelicLevel.glFin (𝓞 ℚ) ℚ k = 1) (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AutomorphicForm.adelicArchGLIncl ℚ (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * AdelicDock.finEmbed (𝓞 ℚ) ℚ u₀ * k =
      AutomorphicForm.adelicArchGLIncl ℚ (AdelicLevel.glArch (𝓞 ℚ) ℚ (x * k)) * AdelicDock.finEmbed (𝓞 ℚ) ℚ u₀ := by
  rw [map_mul, map_mul, mul_assoc,
    mul_comm_of_glArch_eq_one_of_glFin_eq_one (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ u₀) hk, ← mul_assoc]
  conv_lhs => rw [eq_archIncl_glArch_of_glFin_eq_one hk]

private theorem replaceFin_mem_typeSubmodule {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ι : H →* AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ} (hι : ∀ k, AdelicLevel.glFin (𝓞 ℚ) ℚ (ι k) = 1)
    {ρ : Representation ℂ H W} {f : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hf : f ∈ AutomorphicForm.typeSubmodule ι ρ) :
    replaceFin u₀ Ψ' c f ∈ AutomorphicForm.typeSubmodule ι ρ := by
  refine Submodule.span_induction
    (p := fun f _ => replaceFin u₀ Ψ' c f ∈ AutomorphicForm.typeSubmodule ι ρ) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : AutomorphicForm.IsRightEquivariant ι ρ (replaceFin u₀ Ψ' c ∘ₗ T) := by
      intro k v' x
      show T (ρ k v') _ * (Ψ' (AdelicLevel.glFin (𝓞 ℚ) ℚ x) / c) =
        T v' _ * (Ψ' (AdelicLevel.glFin (𝓞 ℚ) ℚ (x * ι k)) / c)
      rw [hT k v', archIncl_glArch_mul_finEmbed_mul u₀ (hι k) x, map_mul (AdelicLevel.glFin (𝓞 ℚ) ℚ) x (ι k),
        hι k, mul_one]
    rw [← LinearMap.comp_apply]
    exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hS v
  · simpa only [map_zero] using (AutomorphicForm.typeSubmodule ι ρ).zero_mem
  · intro _ _ _ _ hu hw
    rw [map_add]
    exact (AutomorphicForm.typeSubmodule ι ρ).add_mem hu hw
  · intro a _ _ hu
    rw [map_smul]
    exact (AutomorphicForm.typeSubmodule ι ρ).smul_mem a hu

private theorem replaceFin_mem_iSup {H : Type*} [Group H] {n : ℕ} {W : Fin n → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] {ι : H →* AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (hι : ∀ k, AdelicLevel.glFin (𝓞 ℚ) ℚ (ι k) = 1) {ρ : ∀ i, Representation ℂ H (W i)}
    {f : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ ⨆ i, AutomorphicForm.typeSubmodule ι (ρ i)) :
    replaceFin u₀ Ψ' c f ∈ ⨆ i, AutomorphicForm.typeSubmodule ι (ρ i) := by
  refine Submodule.iSup_induction _
    (motive := fun f => replaceFin u₀ Ψ' c f ∈ ⨆ i, AutomorphicForm.typeSubmodule ι (ρ i))
    hf ?_ ?_ ?_
  · intro i g hg
    exact Submodule.mem_iSup_of_mem i (replaceFin_mem_typeSubmodule u₀ Ψ' c hι hg)
  · simpa only [map_zero] using (⨆ i, AutomorphicForm.typeSubmodule ι (ρ i)).zero_mem
  · intro g g' hg hg'
    rw [map_add]
    exact Submodule.add_mem _ hg hg'

end Transport

section Kernels

variable (Φ : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
  (Ψ Ψ' : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ)

private noncomputable def tensorKernel : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  fun x => Φ (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * Ψ (AdelicLevel.glFin (𝓞 ℚ) ℚ x)

private theorem replaceFin_tensorKernel {u₀ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : Ψ u₀ ≠ 0) : replaceFin u₀ Ψ' (Ψ u₀) (tensorKernel Φ Ψ) = tensorKernel Φ Ψ' := by
  funext x
  show Φ _ * Ψ _ * (Ψ' (AdelicLevel.glFin (𝓞 ℚ) ℚ x) / Ψ u₀) = Φ (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * Ψ' _
  rw [map_mul, map_mul, AutomorphicForm.glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one,
    AutomorphicForm.glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]
  field_simp

private theorem tensorKernel_inv :
    (fun x => tensorKernel Φ Ψ x⁻¹) = tensorKernel (fun a => Φ a⁻¹) (fun u => Ψ u⁻¹) := by
  funext x
  show Φ (AdelicLevel.glArch (𝓞 ℚ) ℚ x⁻¹) * Ψ (AdelicLevel.glFin (𝓞 ℚ) ℚ x⁻¹) = Φ _⁻¹ * Ψ _⁻¹
  rw [map_inv, map_inv]

private theorem isArchBiFinite_tensorKernel_of_isArchBiFinite (tys : AutomorphicForm.ArchTypeFamily ℚ)
    {u₀ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu₀ : Ψ u₀ ≠ 0)
    (hbf : AutomorphicForm.IsArchBiFinite ℚ tys (tensorKernel Φ Ψ)) :
    AutomorphicForm.IsArchBiFinite ℚ tys (tensorKernel Φ Ψ') := by
  obtain ⟨hinv, hdual⟩ := hbf
  refine ⟨?_, ?_⟩
  · rw [tensorKernel_inv] at hinv ⊢
    rw [AutomorphicForm.mem_archCutSubmodule_iff] at hinv ⊢
    intro w
    have hu₀' : Ψ u₀⁻¹⁻¹ ≠ 0 := by rwa [inv_inv]
    rw [← replaceFin_tensorKernel (fun a => Φ a⁻¹) (fun u => Ψ u⁻¹) (fun u => Ψ' u⁻¹) hu₀']
    exact replaceFin_mem_iSup _ _ _ (fun k => AutomorphicForm.glFin_rowIsometryInclAt₀ ℚ w k) (hinv w)
  · rw [AutomorphicForm.mem_archDualCutSubmodule_iff] at hdual ⊢
    intro w
    rw [← replaceFin_tensorKernel Φ Ψ Ψ' hu₀]
    exact replaceFin_mem_iSup _ _ _ (fun k => AutomorphicForm.glFin_rowIsometryInclAt₀ ℚ w k) (hdual w)

private theorem isFinTestFactor_indicator_of_isOpen_of_isCompact
    (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) (hopen : IsOpen (SetLike.coe U))
    (hcpt : IsCompact (SetLike.coe U)) (a : ℂ) :
    AutomorphicForm.IsFinTestFactor ℚ ((SetLike.coe U).indicator fun _ => a) := by
  classical
  refine ⟨fun s => ?_, HasCompactSupport.intro hcpt fun u hu => Set.indicator_of_notMem hu _⟩

  have hpre : (fun u => (SetLike.coe U).indicator (fun _ => a) u) ⁻¹' s =
      (if a ∈ s then (SetLike.coe U) else ∅) ∪ (if (0 : ℂ) ∈ s then (SetLike.coe U)ᶜ else ∅) := by
    ext u
    by_cases hu : u ∈ (SetLike.coe U)
    · simp [hu]
    · simp [hu]
  rw [hpre]
  refine IsOpen.union ?_ ?_
  · split_ifs
    · exact hopen
    · exact isOpen_empty
  · split_ifs
    · exact hcpt.isClosed.isOpen_compl
    · exact isOpen_empty

private theorem isFactorizableTestFn_and_isArchBiFinite_tensorKernel_indicator
    (tys : AutomorphicForm.ArchTypeFamily ℚ) (hΦ : AutomorphicForm.IsArchTestFactor ℚ Φ)
    {u₀ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu₀ : Ψ u₀ ≠ 0)
    (hbf : AutomorphicForm.IsArchBiFinite ℚ tys (tensorKernel Φ Ψ))
    (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) (hopen : IsOpen (SetLike.coe U))
    (hcpt : IsCompact (SetLike.coe U)) (a : ℂ) :
    AutomorphicForm.IsFactorizableTestFn ℚ (tensorKernel Φ ((SetLike.coe U).indicator fun _ => a)) ∧
      AutomorphicForm.IsArchBiFinite ℚ tys (tensorKernel Φ ((SetLike.coe U).indicator fun _ => a)) :=
  ⟨⟨Φ, _, hΦ, isFinTestFactor_indicator_of_isOpen_of_isCompact U hopen hcpt a, fun _ => rfl⟩,
    isArchBiFinite_tensorKernel_of_isArchBiFinite Φ Ψ _ tys hu₀ hbf⟩

private theorem exists_tensorKernel_eq_of_isFactorizableTestFn {f : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hf : AutomorphicForm.IsFactorizableTestFn ℚ f) :
    ∃ (Φ₀ : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
      (Ψ₀ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ),
      AutomorphicForm.IsArchTestFactor ℚ Φ₀ ∧ AutomorphicForm.IsFinTestFactor ℚ Ψ₀ ∧ f = tensorKernel Φ₀ Ψ₀ := by
  obtain ⟨Φ₀, Ψ₀, hΦ₀, hΨ₀, hfeq⟩ := hf
  exact ⟨Φ₀, Ψ₀, hΦ₀, hΨ₀, funext hfeq⟩

end Kernels

end

section

open NumberField IsDedekindDomain

private noncomputable def finEmbedHom :
    Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) →* ↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ) :=
  (AdelicDock.finEmbed (𝓞 ℚ) ℚ).codRestrict (AutomorphicForm.finiteAdelicGL2Subgroup ℚ) fun u =>
    (AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ u)

private theorem coe_finEmbedHom (u : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finEmbedHom u : ↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ)) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) =
      AdelicDock.finEmbed (𝓞 ℚ) ℚ u :=
  rfl

private theorem continuous_finEmbedHom (hcont : Continuous (AdelicDock.finEmbed (𝓞 ℚ) ℚ)) :
    Continuous finEmbedHom :=
  Continuous.subtype_mk hcont _

private theorem exists_isOpen_isCompact_forall_eq_of_isKfSmooth (hcont : Continuous (AdelicDock.finEmbed (𝓞 ℚ) ℚ))
    {φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : AutomorphicForm.IsKfSmooth ℚ φ) :
    ∃ U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsOpen (SetLike.coe U) ∧
      IsCompact (SetLike.coe U) ∧ ∀ u ∈ U, ∀ g, φ (g * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = φ g := by

  have hstab : IsOpen (SetLike.coe (MulAction.stabilizer (↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ))
      (FLT.SmoothVectors.RightTranslationFn.mk φ :
        FLT.SmoothVectors.RightTranslationFn (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) ℂ) : Subgroup _)) :=
    (FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer _).mp ((AutomorphicForm.isKfSmooth_iff ℚ φ).mp hφ)
  set U₁ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    (MulAction.stabilizer (↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ))
      (FLT.SmoothVectors.RightTranslationFn.mk φ :
        FLT.SmoothVectors.RightTranslationFn (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) ℂ)).comap finEmbedHom with hU₁
  have hU₁open : IsOpen (SetLike.coe U₁) := by
    rw [hU₁, Subgroup.coe_comap]
    exact hstab.preimage (continuous_finEmbedHom hcont)

  have hKopen : IsOpen (SetLike.coe (AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ)))) :=
    AdelicLevel.isOpen_finiteLevelOne (𝓞 ℚ) ℚ top_ne_bot
  have hKcpt : IsCompact (SetLike.coe (AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (⊤ : Ideal (𝓞 ℚ)))) :=
    AdelicLevel.isCompact_finiteLevelOne (𝓞 ℚ) ℚ ⊤
  refine ⟨U₁ ⊓ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ ⊤, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    exact hU₁open.inter hKopen
  · rw [Subgroup.coe_inf]
    exact IsCompact.of_isClosed_subset hKcpt ((U₁.isClosed_of_isOpen hU₁open).inter hKcpt.isClosed)
      Set.inter_subset_right
  · intro u hu g
    have hu₁ : finEmbedHom u ∈ MulAction.stabilizer (↥(AutomorphicForm.finiteAdelicGL2Subgroup ℚ))
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) ℂ) :=
      Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hu).1
    have hfix := MulAction.mem_stabilizer_iff.mp hu₁

    have := congrArg (fun f : FLT.SmoothVectors.RightTranslationFn (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) ℂ =>
      FLT.SmoothVectors.RightTranslationFn.toFun f g) hfix
    simpa [Subgroup.smul_def, coe_finEmbedHom] using this

end

section

open NumberField IsDedekindDomain
open scoped Topology

section Stabiliser

variable {ff : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ}

private theorem exists_isOpen_one_mem_forall_mul_eq (hlc : IsLocallyConstant ff)
    (b : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∃ N : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsOpen N ∧
      (1 : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ N ∧
      ∀ x ∈ N, ∀ y ∈ N, ff (b * (x * y)) = ff b := by
  have hfib : IsOpen {z | ff z = ff b} := hlc.isOpen_fiber (ff b)
  have hpre : IsOpen ((b * ·) ⁻¹' {z | ff z = ff b}) := hfib.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ (b * ·) ⁻¹' {z | ff z = ff b} := by
    rw [Set.mem_preimage, Set.mem_setOf_eq, mul_one]
  have hs : (b * ·) ⁻¹' {z | ff z = ff b} ∈
      𝓝 (1 : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    hpre.mem_nhds h1
  have hsplit := exists_open_nhds_one_split hs
  obtain ⟨N, hNo, hN1, hN⟩ := hsplit
  refine ⟨N, hNo, hN1, fun x hx y hy => ?_⟩
  have h := hN x hx y hy
  rw [Set.mem_preimage, Set.mem_setOf_eq] at h
  exact h

private theorem exists_mem_nhds_one_forall_eq_of_isFinTestFactor (hff : AutomorphicForm.IsFinTestFactor ℚ ff) :
    ∃ W : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)), W ∈ 𝓝 (1 : Matrix.GeneralLinearGroup
      (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧ ∀ w ∈ W, ∀ b, ff (b * w) = ff b := by
  obtain ⟨hlc, hcs⟩ := hff
  choose N hNo hN1 hN using exists_isOpen_one_mem_forall_mul_eq hlc

  have hcover : tsupport ff ⊆ ⋃ b ∈ tsupport ff, (b * ·) '' N b := fun b hb =>
    Set.mem_iUnion₂.mpr ⟨b, hb, 1, hN1 b, mul_one b⟩
  obtain ⟨t, hts, htfin, htcover⟩ := hcs.elim_finite_subcover_image
    (fun b _ => (isOpenMap_mul_left b) _ (hNo b)) hcover

  refine ⟨(⋂ b ∈ t, N b) ∩ (⋂ b ∈ t, N b)⁻¹, ?_, ?_⟩
  · have hI : IsOpen (⋂ b ∈ t, N b) := htfin.isOpen_biInter fun b _ => hNo b
    have h1 : (1 : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ ⋂ b ∈ t, N b :=
      Set.mem_iInter₂.mpr fun b _ => hN1 b
    exact (hI.inter hI.inv).mem_nhds ⟨h1, Set.mem_inv.mpr (by rw [inv_one]; exact h1)⟩
  · rintro w ⟨hw, hw'⟩ b
    have hwN : ∀ i ∈ t, w ∈ N i := fun i hi => Set.mem_iInter₂.mp hw i hi
    have hwN' : ∀ i ∈ t, w⁻¹ ∈ N i := fun i hi => Set.mem_iInter₂.mp (Set.mem_inv.mp hw') i hi

    have hpiece : ∀ z ∈ tsupport ff, ∀ v, (∀ i ∈ t, v ∈ N i) → ff (z * v) = ff z := by
      intro z hz v hv
      obtain ⟨i, hi, x, hx, rfl⟩ := Set.mem_iUnion₂.mp (htcover hz)
      have hx1 : ff (i * (x * 1)) = ff i := hN i x hx 1 (hN1 i)
      rw [mul_one] at hx1
      show ff (i * x * v) = ff (i * x)
      rw [mul_assoc, hN i x hx v (hv i hi), hx1]
    by_cases hb : b ∈ tsupport ff
    · exact hpiece b hb w hwN
    · by_cases hbw : b * w ∈ tsupport ff
      · have := hpiece (b * w) hbw w⁻¹ hwN'
        rw [mul_inv_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hb, image_eq_zero_of_notMem_tsupport hbw]

private theorem isSmoothVector_of_isFinTestFactor (hff : AutomorphicForm.IsFinTestFactor ℚ ff) :
    FLT.SmoothVectors.IsSmoothVector (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      (FLT.SmoothVectors.RightTranslationFn.mk ff :
        FLT.SmoothVectors.RightTranslationFn (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ℂ) := by
  obtain ⟨W, hW, hWff⟩ := exists_mem_nhds_one_forall_eq_of_isFinTestFactor hff
  rw [FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer]
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hW fun w hw => ?_)
  exact MulAction.mem_stabilizer_iff.mpr (FLT.SmoothVectors.RightTranslationFn.ext fun b => hWff w hw b)

private theorem exists_isOpen_isCompact_forall_eq_of_isFinTestFactor (hff : AutomorphicForm.IsFinTestFactor ℚ ff) :
    ∃ U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsOpen (SetLike.coe U) ∧
      IsCompact (SetLike.coe U) ∧ ∀ u ∈ U, ∀ b, ff (b * u) = ff b := by
  have hex : ∃ K : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)),
      IsCompact (SetLike.coe K) ∧ IsOpen (SetLike.coe K) :=
    ⟨AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ ⊤, AdelicLevel.isCompact_finiteLevelOne (𝓞 ℚ) ℚ ⊤,
      AdelicLevel.isOpen_finiteLevelOne (𝓞 ℚ) ℚ top_ne_bot⟩
  obtain ⟨U, hcpt, hopen, hU⟩ :=
    (FLT.SmoothVectors.isSmoothVector_iff_exists_isCompact_isOpen_subgroup hex).mp
      (isSmoothVector_of_isFinTestFactor hff)
  refine ⟨U, hopen, hcpt, fun u hu b => ?_⟩
  exact congrArg (fun f : FLT.SmoothVectors.RightTranslationFn
    (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ℂ => FLT.SmoothVectors.RightTranslationFn.toFun f b)
    (hU u hu)

end Stabiliser

end

section

open NumberField

private theorem continuous_archEntries : Continuous (AutomorphicForm.archEntries ℚ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (AdelicBox.continuous_ringEquiv_mixedSpace ℚ).comp (Units.continuous_val.matrix_elem i j)

private theorem continuous_of_isArchTestFactor {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) : Continuous fa := by
  classical
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩ := hfa
  have h : fa = Φ ∘ AutomorphicForm.archEntries ℚ := funext hfaΦ
  rw [h]
  exact hΦ.continuous.comp continuous_archEntries

private theorem hasCompactSupport_of_isArchTestFactor
    {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) :
    HasCompactSupport fa :=
  hfa.2

private theorem adelicArchGLIncl_entry (a : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) (i j : Fin 2) :
    ((AutomorphicForm.adelicArchGLIncl ℚ a : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      (((a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
        ((1 : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ) := by
  have h₁ := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) =>
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) (AutomorphicForm.glArch_adelicArchGLIncl ℚ a)
  have h₂ := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) =>
    (g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)
    (AutomorphicForm.glFin_adelicArchGLIncl ℚ a)
  simp only [AdelicLevel.glArch, AdelicLevel.glFin, Matrix.GeneralLinearGroup.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at h₁ h₂
  exact Prod.ext h₁ h₂

private theorem continuous_adelicArchGLIncl : Continuous (AutomorphicForm.adelicArchGLIncl ℚ) := by
  obtain ⟨hval, hinv⟩ := Units.continuous_iff.mp
    (continuous_id : Continuous fun a : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) => a)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact ((hval.matrix_elem i j).prodMk continuous_const).congr fun a => (adelicArchGLIncl_entry a i j).symm
  · refine continuous_matrix fun i j => ?_
    have e : ∀ a : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ),
        (((a⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :
            Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
          ((1 : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) =
          (((AutomorphicForm.adelicArchGLIncl ℚ a)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j := by
      intro a
      rw [← map_inv]
      exact (adelicArchGLIncl_entry a⁻¹ i j).symm
    exact ((hinv.matrix_elem i j).prodMk continuous_const).congr e

end

section

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private theorem integrable_summand
    (χ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hχ : Continuous χ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (fA : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (hfAc : Continuous fA) (hfAs : HasCompactSupport fA)
    (C : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))) (hCc : IsCompact C) (hCo : IsOpen C)
    (a : ℂ)
    (archIncl : GL (Fin 2) (InfiniteAdeleRing ℚ) → AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (harch : Continuous archIncl)
    (finEmbed : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) → AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hfin : Continuous finEmbed)
    (hdec : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ,
      x = archIncl (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * finEmbed (AdelicLevel.glFin (𝓞 ℚ) ℚ x)) :
    Integrable
      (fun x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ =>
        χ (g * x) * (fA (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * C.indicator (fun _ => a) (AdelicLevel.glFin (𝓞 ℚ) ℚ x)))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  have hclopen : IsClopen C := ⟨hCc.isClosed, hCo⟩
  have hcont : Continuous (fun x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ =>
      χ (g * x) * (fA (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * C.indicator (fun _ => a) (AdelicLevel.glFin (𝓞 ℚ) ℚ x))) :=
    (hχ.comp (continuous_const.mul continuous_id)).mul
      ((hfAc.comp (AdelicLevel.continuous_glArch (𝓞 ℚ) ℚ)).mul
        ((hclopen.continuous_indicator continuous_const).comp (AdelicLevel.continuous_glFin (𝓞 ℚ) ℚ)))
  have hK : IsCompact
      ((fun p : GL (Fin 2) (InfiniteAdeleRing ℚ) × GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) =>
          archIncl p.1 * finEmbed p.2) '' (tsupport fA ×ˢ C)) :=
    (IsCompact.prod hfAs hCc).image ((harch.comp continuous_fst).mul (hfin.comp continuous_snd))
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun x hx => ?_)
  by_cases h₁ : AdelicLevel.glArch (𝓞 ℚ) ℚ x ∈ tsupport fA
  · by_cases h₂ : AdelicLevel.glFin (𝓞 ℚ) ℚ x ∈ C
    · exact absurd ⟨(AdelicLevel.glArch (𝓞 ℚ) ℚ x, AdelicLevel.glFin (𝓞 ℚ) ℚ x), ⟨h₁, h₂⟩, (hdec x).symm⟩ hx
    · simp [h₂]
  · have h₀ : fA (AdelicLevel.glArch (𝓞 ℚ) ℚ x) = 0 := by
      by_contra hne
      exact h₁ (subset_tsupport fA (Function.mem_support.mpr hne))
    simp [h₀]

private theorem integrable_arch_integrand {A : Type} [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    (ψ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hψ : Continuous ψ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (archIncl : A → AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (harch : Continuous archIncl)
    (Φ : A → ℂ) (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) :
    Integrable (fun a : A => ψ (g * archIncl a) * Φ a) μ := by
  have hcont : Continuous (fun a : A => ψ (g * archIncl a) * Φ a) :=
    (hψ.comp (continuous_const.mul harch)).mul hΦc
  have hsupp : HasCompactSupport (fun a : A => ψ (g * archIncl a) * Φ a) := by
    show HasCompactSupport ((fun a : A => ψ (g * archIncl a)) * Φ)
    exact hΦs.mul_left
  exact hcont.integrable_of_hasCompactSupport hsupp

end

section

open NumberField IsDedekindDomain MeasureTheory

section Measures

private noncomputable abbrev archGLBorel :
    MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :=
  borel _

private noncomputable abbrev finGLBorel :
    MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  borel _

attribute [local instance] archGLBorel finGLBorel

private scoped instance : BorelSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) := ⟨rfl⟩

private scoped instance : BorelSpace (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := ⟨rfl⟩

private scoped instance : LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) := by
  haveI : LocallyCompactSpace (InfiniteAdeleRing ℚ) :=
    inferInstanceAs (LocallyCompactSpace ((v : InfinitePlace ℚ) → v.Completion))
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private scoped instance : LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private noncomputable def archHaarQ : Measure (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :=
  Measure.haar

private noncomputable def finHaarQ : Measure (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Measure.haar

private scoped instance : archHaarQ.IsHaarMeasure := by unfold archHaarQ; infer_instance
private scoped instance : archHaarQ.Regular := by unfold archHaarQ; infer_instance
private scoped instance : finHaarQ.IsHaarMeasure := by unfold finHaarQ; infer_instance
private scoped instance : finHaarQ.Regular := by unfold finHaarQ; infer_instance

private theorem finHaarQ_pos_of_isOpen (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hopen : IsOpen (SetLike.coe U)) : 0 < finHaarQ (SetLike.coe U) :=
  hopen.measure_pos finHaarQ ⟨1, U.one_mem⟩

private theorem finHaarQ_ne_top_of_isCompact
    (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) (hcpt : IsCompact (SetLike.coe U)) :
    finHaarQ (SetLike.coe U) ≠ ⊤ :=
  hcpt.measure_lt_top.ne

end Measures

attribute [local instance] archGLBorel finGLBorel

section Components

private theorem eq_archIncl_mul_finEmbed (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    h = AutomorphicForm.adelicArchGLIncl ℚ (AdelicLevel.glArch (𝓞 ℚ) ℚ h) *
      AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicLevel.glFin (𝓞 ℚ) ℚ h) := by
  refine adelicGL2_ext ?_ ?_
  · rw [map_mul, AutomorphicForm.glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  · rw [map_mul, AutomorphicForm.glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]

private theorem finComponent_glFin_archIncl (q : ℕ) [Fact q.Prime]
    (a : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
      (AdelicLevel.glFin (𝓞 ℚ) ℚ (AutomorphicForm.adelicArchGLIncl ℚ a)) = 1 := by
  rw [AutomorphicForm.glFin_adelicArchGLIncl, map_one]

end Components

section Commute

variable (q : ℕ) [Fact q.Prime]

private theorem padicToAdelic_mul_archIncl (x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q])
    (a : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :
    AdelicDock.padicToAdelic q x * AutomorphicForm.adelicArchGLIncl ℚ a =
      AutomorphicForm.adelicArchGLIncl ℚ a * AdelicDock.padicToAdelic q x := by
  refine adelicGL2_ext ?_ ?_
  · rw [map_mul, map_mul, AdelicDock.glArch_padicToAdelic, AutomorphicForm.glArch_adelicArchGLIncl, one_mul, mul_one]
  · rw [map_mul, map_mul, AutomorphicForm.glFin_adelicArchGLIncl, one_mul, mul_one]

end Commute

section ArchOp

private noncomputable def archOp (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (ψ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  fun g => ∫ a, ψ (g * AutomorphicForm.adelicArchGLIncl ℚ a) * fa a ∂archHaarQ

private theorem archOp_rightTranslate_padicToAdelic (q : ℕ) [Fact q.Prime]
    (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (ψ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]) :
    archOp fa (AutomorphicForm.CuspidalConstituent.rightTranslate ℚ (AdelicDock.padicToAdelic q x) ψ) =
      AutomorphicForm.CuspidalConstituent.rightTranslate ℚ (AdelicDock.padicToAdelic q x) (archOp fa ψ) := by
  funext g
  simp only [archOp, AutomorphicForm.CuspidalConstituent.rightTranslate_apply]
  congr 1
  funext a
  rw [mul_assoc, mul_assoc, padicToAdelic_mul_archIncl]

section Level

variable (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))

private noncomputable def unitIndicator : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ :=
  (SetLike.coe U).indicator fun _ => (((finHaarQ (SetLike.coe U)).toReal⁻¹ : ℝ) : ℂ)

private theorem integral_unitIndicator (hopen : IsOpen (SetLike.coe U)) (hcpt : IsCompact (SetLike.coe U)) :
    ∫ u, unitIndicator U u ∂finHaarQ = 1 := by
  have ht : (finHaarQ (SetLike.coe U)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (finHaarQ_pos_of_isOpen U hopen).ne' (finHaarQ_ne_top_of_isCompact U hcpt)).ne'
  unfold unitIndicator
  rw [MeasureTheory.integral_indicator_const _ hopen.measurableSet, Complex.real_smul, ← Complex.ofReal_mul,
    MeasureTheory.measureReal_def, mul_inv_cancel₀ ht, Complex.ofReal_one]

private noncomputable def archKernel (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) :
    AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  fun x => fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * unitIndicator U (AdelicLevel.glFin (𝓞 ℚ) ℚ x)

end Level

private theorem exists_forall_rightConv_archKernel_eq :
    ∃ c : ℝ, 0 < c ∧ ∀ (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
      (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))),
      IsOpen (SetLike.coe U) → IsCompact (SetLike.coe U) → ∀ ψ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
        (∀ u ∈ U, ∀ g, ψ (g * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = ψ g) →
        AutomorphicForm.rightConv ℚ ψ (archKernel U fa) = fun g => (c : ℂ) * archOp fa ψ g := by
  obtain ⟨c, hc, hsplit⟩ :=
    AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral ℚ archHaarQ finHaarQ
  refine ⟨(c : ℝ), NNReal.coe_pos.mpr hc, fun fa U hopen hcpt ψ hψ => ?_⟩
  funext g
  have key : (fun x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ => ψ (g * x) * archKernel U fa x) = fun x =>
      ψ (g * AutomorphicForm.adelicArchGLIncl ℚ (AdelicLevel.glArch (𝓞 ℚ) ℚ x)) * fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) *
        unitIndicator U (AdelicLevel.glFin (𝓞 ℚ) ℚ x) := by
    funext x
    by_cases hu : AdelicLevel.glFin (𝓞 ℚ) ℚ x ∈ U
    · have hx : ψ (g * x) = ψ (g * AutomorphicForm.adelicArchGLIncl ℚ (AdelicLevel.glArch (𝓞 ℚ) ℚ x)) := by
        conv_lhs => rw [eq_archIncl_mul_finEmbed x]
        rw [← mul_assoc]
        exact hψ _ hu _
      simp only [archKernel]
      rw [hx]
      ring
    · simp [archKernel, unitIndicator, hu]
  have hsplit' := hsplit (fun a => ψ (g * AutomorphicForm.adelicArchGLIncl ℚ a) * fa a) (unitIndicator U)
  rw [integral_unitIndicator U hopen hcpt, mul_one] at hsplit'
  rw [AutomorphicForm.rightConv_apply]
  rw [key]
  exact hsplit'

private theorem archOp_mem_of_isCuspSubrep {pins : AutomorphicForm.CarrierPins ℚ} {ξ : pins.Z →* ℂˣ}
    {V : Submodule ℂ (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspSubrep ℚ pins ξ V)
    (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) (hopen : IsOpen (SetLike.coe U))
    (hcpt : IsCompact (SetLike.coe U)) (tys : AutomorphicForm.ArchTypeFamily ℚ)
    (hker : AutomorphicForm.IsFactorizableTestFn ℚ (archKernel U fa))
    (hbf : AutomorphicForm.IsArchBiFinite ℚ tys (archKernel U fa)) (ψ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hψV : ψ ∈ V) (hψ : ∀ u ∈ U, ∀ g, ψ (g * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = ψ g) : archOp fa ψ ∈ V := by
  obtain ⟨c, hc, hconv⟩ := exists_forall_rightConv_archKernel_eq
  have hmem := hV.rightConv_mem (archKernel U fa) tys hker hbf ψ hψV
  rw [hconv fa U hopen hcpt ψ hψ] at hmem
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have : archOp fa ψ = (c : ℂ)⁻¹ • (fun g => (c : ℂ) * archOp fa ψ g) := by
    funext g
    simp [inv_mul_cancel_left₀ hc']
  rw [this]
  exact V.smul_mem _ hmem

end ArchOp

section FinConv

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

variable (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))

private noncomputable def cosetSet (b : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  (b⁻¹ * ·) ⁻¹' (SetLike.coe U)

private theorem mem_cosetSet {b x : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} :
    x ∈ cosetSet U b ↔ b⁻¹ * x ∈ U :=
  Iff.rfl

private theorem mul_mem_cosetSet_iff (b y : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    b * y ∈ cosetSet U b ↔ y ∈ U := by
  rw [mem_cosetSet, inv_mul_cancel_left]

private theorem isOpen_cosetSet (hopen : IsOpen (SetLike.coe U))
    (b : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : IsOpen (cosetSet U b) :=
  hopen.preimage (continuous_const.mul continuous_id)

private theorem isCompact_cosetSet (hcpt : IsCompact (SetLike.coe U))
    (b : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : IsCompact (cosetSet U b) := by
  have h : cosetSet U b = (b * ·) '' (SetLike.coe U) := by
    rw [Set.image_mul_left]
    rfl
  rw [h]
  exact hcpt.image (continuous_const.mul continuous_id)

private theorem isOpen_isCompact_inf {U₁ U₂ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))}
    (h₁o : IsOpen (SetLike.coe U₁)) (h₁c : IsCompact (SetLike.coe U₁)) (h₂o : IsOpen (SetLike.coe U₂))
    (h₂c : IsCompact (SetLike.coe U₂)) : IsOpen (SetLike.coe (U₁ ⊓ U₂)) ∧
      IsCompact (SetLike.coe (U₁ ⊓ U₂)) := by
  rw [Subgroup.coe_inf]
  exact ⟨h₁o.inter h₂o, IsCompact.of_isClosed_subset h₁c (h₁c.isClosed.inter h₂c.isClosed) Set.inter_subset_left⟩

private theorem exists_finset_eq_sum_indicator_cosetSet (hopen : IsOpen (SetLike.coe U))
    {ff : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ} (hcs : HasCompactSupport ff)
    (hinv : ∀ u ∈ U, ∀ b, ff (b * u) = ff b) :
    ∃ s : Finset (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) ⧸ U),
      ff = fun b => ∑ k ∈ s, (cosetSet U k.out).indicator (fun _ => ff k.out) b := by

  have hfin : ((QuotientGroup.mk : _ → Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) ⧸ U) ''
      tsupport ff).Finite := by
    have hcover : tsupport ff ⊆ ⋃ b ∈ tsupport ff, cosetSet U b := fun b hb =>
      Set.mem_iUnion₂.mpr ⟨b, hb, by rw [mem_cosetSet, inv_mul_cancel]; exact U.one_mem⟩
    obtain ⟨t, -, htfin, htcover⟩ := hcs.elim_finite_subcover_image (fun b _ => isOpen_cosetSet U hopen b) hcover
    refine (htfin.image QuotientGroup.mk).subset ?_
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := Set.mem_iUnion₂.mp (htcover hb)
    exact ⟨i, hi, QuotientGroup.eq.mpr ((mem_cosetSet U).mp hbi)⟩

  have hconst : ∀ (k : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) ⧸ U) (x),
      x ∈ cosetSet U k.out → ff x = ff k.out := by
    intro k x hx
    have h := hinv _ ((mem_cosetSet U).mp hx) k.out
    rwa [mul_inv_cancel_left] at h

  have hclass : ∀ (k : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) ⧸ U) (x),
      x ∈ cosetSet U k.out ↔ k = QuotientGroup.mk x := by
    intro k x
    rw [mem_cosetSet]
    constructor
    · intro h
      exact (QuotientGroup.out_eq' k).symm.trans (QuotientGroup.eq.mpr h)
    · rintro rfl
      exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
  refine ⟨hfin.toFinset, funext fun b => ?_⟩
  by_cases hb : (QuotientGroup.mk b : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) ⧸ U) ∈ hfin.toFinset
  · have hmem : b ∈ cosetSet U (QuotientGroup.mk b : Matrix.GeneralLinearGroup (Fin 2)
        (FiniteAdeleRing (𝓞 ℚ) ℚ) ⧸ U).out := (hclass _ b).mpr rfl
    rw [Finset.sum_eq_single (QuotientGroup.mk b)]
    · rw [Set.indicator_of_mem hmem]
      exact hconst _ b hmem
    · intro k _ hk
      exact Set.indicator_of_notMem (fun h => hk ((hclass k b).mp h)) _
    · intro h
      exact absurd hb h
  · have hb0 : ff b = 0 :=
      image_eq_zero_of_notMem_tsupport fun hbs => hb (hfin.mem_toFinset.mpr ⟨b, hbs, rfl⟩)
    rw [hb0]
    symm
    refine Finset.sum_eq_zero fun k hk => Set.indicator_of_notMem (fun h => ?_) _
    exact hb (((hclass k b).mp h) ▸ hk)

private theorem rightConv_indicator_cosetSet (χ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (b : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (a : ℂ) :
    AutomorphicForm.rightConv ℚ χ (fun x => fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) *
        (cosetSet U b).indicator (fun _ => a) (AdelicLevel.glFin (𝓞 ℚ) ℚ x)) =
      AutomorphicForm.CuspidalConstituent.rightTranslate ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ b)
        (AutomorphicForm.rightConv ℚ χ (fun x => fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) *
          (SetLike.coe U).indicator (fun _ => a) (AdelicLevel.glFin (𝓞 ℚ) ℚ x))) := by
  funext g
  rw [AutomorphicForm.CuspidalConstituent.rightTranslate_apply, AutomorphicForm.rightConv_apply,
    AutomorphicForm.rightConv_apply]
  rw [← MeasureTheory.integral_mul_left_eq_self (fun x => χ (g * x) * (fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) *
    (cosetSet U b).indicator (fun _ => a) (AdelicLevel.glFin (𝓞 ℚ) ℚ x))) (AdelicDock.finEmbed (𝓞 ℚ) ℚ b)]
  congr 1
  funext x
  have harch : AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ b * x) = AdelicLevel.glArch (𝓞 ℚ) ℚ x := by
    rw [map_mul, AdelicDock.glArch_finEmbed, one_mul]
  have hfin : AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ b * x) = b * AdelicLevel.glFin (𝓞 ℚ) ℚ x := by
    rw [map_mul, AdelicDock.glFin_finEmbed]
  have hind : (cosetSet U b).indicator (fun _ => a) (b * AdelicLevel.glFin (𝓞 ℚ) ℚ x) =
      (SetLike.coe U).indicator (fun _ => a) (AdelicLevel.glFin (𝓞 ℚ) ℚ x) := by
    by_cases hx : AdelicLevel.glFin (𝓞 ℚ) ℚ x ∈ U
    · rw [Set.indicator_of_mem ((mul_mem_cosetSet_iff U b _).mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx ((mul_mem_cosetSet_iff U b _).mp h)), Set.indicator_of_notMem hx]
  simp only [harch, hfin, hind, mul_assoc]

private theorem rightConv_indicator_eq_smul_rightConv_archKernel (hopen : IsOpen (SetLike.coe U))
    (hcpt : IsCompact (SetLike.coe U)) (χ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (a : ℂ) :
    AutomorphicForm.rightConv ℚ χ (fun x => fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) *
        (SetLike.coe U).indicator (fun _ => a) (AdelicLevel.glFin (𝓞 ℚ) ℚ x)) =
      fun g => (a * ((finHaarQ (SetLike.coe U)).toReal : ℂ)) * AutomorphicForm.rightConv ℚ χ (archKernel U fa) g := by
  have hm : ((finHaarQ (SetLike.coe U)).toReal : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (ENNReal.toReal_pos (finHaarQ_pos_of_isOpen U hopen).ne' (finHaarQ_ne_top_of_isCompact U hcpt)).ne'
  funext g
  rw [AutomorphicForm.rightConv_apply, AutomorphicForm.rightConv_apply]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  unfold archKernel unitIndicator
  by_cases hx : AdelicLevel.glFin (𝓞 ℚ) ℚ x ∈ U
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have key : ((finHaarQ (SetLike.coe U)).toReal : ℂ) * (((finHaarQ (SetLike.coe U)).toReal : ℂ))⁻¹ = 1 :=
      mul_inv_cancel₀ hm
    push_cast
    linear_combination (-(χ (g * x) * fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * a)) * key
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    ring

private theorem exists_finset_rightConv_eq_sum_rightTranslate_archOp (hopen : IsOpen (SetLike.coe U))
    (hcpt : IsCompact (SetLike.coe U)) (χ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hχ : ∀ u ∈ U, ∀ g, χ (g * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = χ g)
    (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    {ff : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ} (hcs : HasCompactSupport ff)
    (hffU : ∀ u ∈ U, ∀ b, ff (b * u) = ff b)
    (hint : ∀ C : Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact C → IsOpen C →
      ∀ (a : ℂ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ), MeasureTheory.Integrable (fun x => χ (g * x) *
        (fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * C.indicator (fun _ => a) (AdelicLevel.glFin (𝓞 ℚ) ℚ x)))
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    ∃ (s : Finset (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) ⧸ U))
      (coef : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) ⧸ U → ℂ),
      AutomorphicForm.rightConv ℚ χ (fun x => fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * ff (AdelicLevel.glFin (𝓞 ℚ) ℚ x)) =
        fun g => ∑ k ∈ s, coef k *
          AutomorphicForm.CuspidalConstituent.rightTranslate ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ k.out)
            (archOp fa χ) g := by
  have hexp := exists_finset_eq_sum_indicator_cosetSet U hopen hcs hffU
  obtain ⟨s, hs⟩ := hexp
  have hconst := exists_forall_rightConv_archKernel_eq
  obtain ⟨c, -, hind⟩ := hconst
  refine ⟨s, fun k => ff k.out * ((finHaarQ (SetLike.coe U)).toReal : ℂ) * (c : ℂ), ?_⟩

  have hsum : AutomorphicForm.rightConv ℚ χ
      (fun x => fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * ff (AdelicLevel.glFin (𝓞 ℚ) ℚ x)) = fun g => ∑ k ∈ s,
        AutomorphicForm.rightConv ℚ χ (fun x => fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) *
          (cosetSet U k.out).indicator (fun _ => ff k.out) (AdelicLevel.glFin (𝓞 ℚ) ℚ x)) g := by
    funext g
    rw [AutomorphicForm.rightConv_apply]
    have hpt : (fun x => χ (g * x) * (fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * ff (AdelicLevel.glFin (𝓞 ℚ) ℚ x))) =
        fun x => ∑ k ∈ s, χ (g * x) * (fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) *
          (cosetSet U k.out).indicator (fun _ => ff k.out) (AdelicLevel.glFin (𝓞 ℚ) ℚ x)) := by
      funext x
      have hx : ff (AdelicLevel.glFin (𝓞 ℚ) ℚ x) = ∑ k ∈ s,
          (cosetSet U k.out).indicator (fun _ => ff k.out) (AdelicLevel.glFin (𝓞 ℚ) ℚ x) := congrFun hs _
      rw [hx, Finset.mul_sum, Finset.mul_sum]
    have hI : ∀ k ∈ s, MeasureTheory.Integrable (fun x => χ (g * x) * (fa (AdelicLevel.glArch (𝓞 ℚ) ℚ x) *
        (cosetSet U k.out).indicator (fun _ => ff k.out) (AdelicLevel.glFin (𝓞 ℚ) ℚ x)))
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
      fun k _ => hint _ (isCompact_cosetSet U hcpt k.out) (isOpen_cosetSet U hopen k.out) (ff k.out) g
    rw [hpt, MeasureTheory.integral_finsetSum s hI]
    simp only [AutomorphicForm.rightConv_apply]
  rw [hsum]
  funext g
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rightConv_indicator_cosetSet U χ fa k.out (ff k.out), AutomorphicForm.CuspidalConstituent.rightTranslate_apply,
    rightConv_indicator_eq_smul_rightConv_archKernel U hopen hcpt χ fa (ff k.out), hind fa U hopen hcpt χ hχ,
    AutomorphicForm.CuspidalConstituent.rightTranslate_apply]
  beta_reduce
  ring

end FinConv

section ArchOpLin

variable (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)

private theorem archOp_add {ψ₁ ψ₂ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (h₁ : ∀ g, MeasureTheory.Integrable (fun a => ψ₁ (g * AutomorphicForm.adelicArchGLIncl ℚ a) * fa a) archHaarQ)
    (h₂ : ∀ g, MeasureTheory.Integrable (fun a => ψ₂ (g * AutomorphicForm.adelicArchGLIncl ℚ a) * fa a) archHaarQ) :
    archOp fa (ψ₁ + ψ₂) = archOp fa ψ₁ + archOp fa ψ₂ := by
  funext g
  simp only [archOp, Pi.add_apply, add_mul]
  exact MeasureTheory.integral_add (h₁ g) (h₂ g)

private theorem archOp_smul (c : ℂ) (ψ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    archOp fa (c • ψ) = c • archOp fa ψ := by
  funext g
  simp only [archOp, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul c _

private noncomputable def archOpOn (V : Submodule ℂ (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hint : ∀ φ ∈ V, ∀ g,
      MeasureTheory.Integrable (fun a => φ (g * AutomorphicForm.adelicArchGLIncl ℚ a) * fa a) archHaarQ) :
    ↥V →ₗ[ℂ] (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) where
  toFun φ := archOp fa φ.1
  map_add' φ₁ φ₂ := archOp_add fa (hint _ φ₁.2) (hint _ φ₂.2)
  map_smul' c φ := archOp_smul fa c φ.1

private theorem archOpOn_apply (V : Submodule ℂ (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hint : ∀ φ ∈ V, ∀ g,
      MeasureTheory.Integrable (fun a => φ (g * AutomorphicForm.adelicArchGLIncl ℚ a) * fa a) archHaarQ)
    (φ : ↥V) : archOpOn fa V hint φ = archOp fa φ.1 :=
  rfl

end ArchOpLin

end

section

noncomputable section

open NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace EquivariantSpan
p2m_open "LocalNewvector"

variable (q : ℕ) [Fact q.Prime]

private def toFnₗ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) where
  toFun := LocalNewvector.AdelicFnCarrier.toFn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def mkₗ : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ where
  toFun := LocalNewvector.AdelicFnCarrier.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp]
private theorem toFnₗ_apply (ψ : LocalNewvector.AdelicFnCarrier ℚ) : toFnₗ ψ = ψ.toFn := rfl

@[scoped simp]
private theorem mkₗ_apply (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : mkₗ f = LocalNewvector.AdelicFnCarrier.mk f := rfl

private abbrev family (V W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) : Type :=
  {θ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ //
    (∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → θ (x • ψ) = x • θ ψ) ∧
      ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ W₀ → (θ ψ).toFn ∈ V}

private def imageSpan (V W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
  Submodule.span ℂ {χ | ∃ (θ : family q V W₀) (ψ' : LocalNewvector.AdelicFnCarrier ℚ),
    ψ'.toFn ∈ W₀ ∧ χ = (θ.1 ψ').toFn}

variable {q}
variable {V W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}

private theorem toFn_mem_imageSpan (θ : family q V W₀) {ψ' : LocalNewvector.AdelicFnCarrier ℚ} (hψ' : ψ'.toFn ∈ W₀) :
    (θ.1 ψ').toFn ∈ imageSpan q V W₀ :=
  Submodule.subset_span ⟨θ, ψ', hψ', rfl⟩

private theorem imageSpan_le : imageSpan q V W₀ ≤ V :=
  Submodule.span_le.mpr (by rintro _ ⟨θ, ψ', hψ', rfl⟩; exact θ.2.2 ψ' hψ')

private def idFamily (hle : W₀ ≤ V) : family q V W₀ :=
  ⟨LinearMap.id, fun _ _ _ => rfl, fun _ hψ => hle hψ⟩

private theorem le_imageSpan (hle : W₀ ≤ V) : W₀ ≤ imageSpan q V W₀ := fun f hf =>
  toFn_mem_imageSpan (idFamily hle) (ψ' := LocalNewvector.AdelicFnCarrier.mk f) hf

private def compFamily (A : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)
    (hAeq : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V → A (x • ψ) = x • A ψ)
    (hAV : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V → (A ψ).toFn ∈ V) (θ : family q V W₀) :
    family q V W₀ :=
  ⟨A ∘ₗ θ.1, fun x ψ hψ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, θ.2.1 x ψ hψ, hAeq x _ (θ.2.2 ψ hψ)],
    fun ψ hψ => hAV _ (θ.2.2 ψ hψ)⟩

private theorem map_mem_imageSpan
    (E : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hEcomm : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ φ ∈ V,
      E (rightTranslate ℚ (AdelicDock.padicToAdelic q x) φ) = rightTranslate ℚ (AdelicDock.padicToAdelic q x) (E φ))
    (hEV : ∀ φ ∈ V, E φ ∈ V) {χ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hχ : χ ∈ imageSpan q V W₀) :
    E χ ∈ imageSpan q V W₀ := by
  have hsm : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ),
      (x • ψ).toFn = rightTranslate ℚ (AdelicDock.padicToAdelic q x) ψ.toFn := fun x ψ =>
    funext fun y => by
      rw [AdelicFnCarrier.padic_smul_def, AdelicFnCarrier.toFn_smul, rightTranslate_apply]
  let A : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ := mkₗ ∘ₗ E ∘ₗ toFnₗ
  have hA : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, (A ψ).toFn = E ψ.toFn := fun _ => rfl
  have hAeq : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V →
      A (x • ψ) = x • A ψ :=
    fun x ψ hψ => LocalNewvector.AdelicFnCarrier.ext fun y => by
      change E (x • ψ).toFn y = (x • A ψ).toFn y
      rw [hsm x ψ, hEcomm x _ hψ, hsm x (A ψ), hA]
  have hAV : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V → (A ψ).toFn ∈ V := fun ψ hψ => by
    rw [hA]; exact hEV _ hψ
  unfold imageSpan at hχ
  induction hχ using Submodule.span_induction with
  | mem χ hχ =>
    obtain ⟨θ, ψ', hψ', rfl⟩ := hχ
    rw [← hA]
    exact toFn_mem_imageSpan (compFamily A hAeq hAV θ) hψ'
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

private theorem map_mem_imageSpan_of_restrict
    (hVst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ φ ∈ V, rightTranslate ℚ (AdelicDock.padicToAdelic q x) φ ∈ V)
    (E : ↥V →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hEcomm : ∀ (x : GL (Fin 2) ℚ_[q]) (φ : ↥V),
      E ⟨rightTranslate ℚ (AdelicDock.padicToAdelic q x) φ, hVst x φ φ.2⟩ =
        rightTranslate ℚ (AdelicDock.padicToAdelic q x) (E φ))
    (hEV : ∀ φ : ↥V, E φ ∈ V) {χ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hχ : χ ∈ imageSpan q V W₀) :
    E ⟨χ, imageSpan_le hχ⟩ ∈ imageSpan q V W₀ := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl V
  let P : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] ↥V := Submodule.projectionOnto (p := V) (q := C) hC
  have hP : ∀ (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : f ∈ V), P f = ⟨f, hf⟩ := fun f hf =>
    Submodule.projectionOnto_apply_left (p := V) (q := C) hC ⟨f, hf⟩
  have hEP : ∀ (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : f ∈ V), (E ∘ₗ P) f = E ⟨f, hf⟩ := fun f hf => by
    rw [LinearMap.comp_apply, hP f hf]
  rw [← hEP χ (imageSpan_le hχ)]
  refine map_mem_imageSpan (E ∘ₗ P) (fun x φ hφ => ?_) (fun φ hφ => ?_) hχ
  · rw [hEP _ (hVst x φ hφ), hEP φ hφ]
    exact hEcomm x ⟨φ, hφ⟩
  · rw [hEP φ hφ]; exact hEV ⟨φ, hφ⟩

private def rightTranslateₗ (g : AdelicGL2 (𝓞 ℚ) ℚ) : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) where
  toFun := rightTranslate ℚ g
  map_add' := rightTranslate_add ℚ g
  map_smul' := rightTranslate_smul ℚ g

@[scoped simp]
private theorem rightTranslateₗ_apply (g : AdelicGL2 (𝓞 ℚ) ℚ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    rightTranslateₗ g φ = rightTranslate ℚ g φ := rfl

private theorem rightTranslate_mem_imageSpan_of_commute
    (h : AdelicGL2 (𝓞 ℚ) ℚ) (hcomm : ∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h)
    (hV : ∀ φ ∈ V, rightTranslate ℚ h φ ∈ V) {χ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hχ : χ ∈ imageSpan q V W₀) :
    rightTranslate ℚ h χ ∈ imageSpan q V W₀ := by
  refine map_mem_imageSpan (rightTranslateₗ h) (fun x φ _ => ?_) hV hχ
  simp only [rightTranslateₗ_apply, rightTranslate_rightTranslate, (hcomm x).eq]

private theorem rightTranslate_padicToAdelic_mem_imageSpan
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀)
    (x : GL (Fin 2) ℚ_[q]) {χ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hχ : χ ∈ imageSpan q V W₀) :
    rightTranslate ℚ (AdelicDock.padicToAdelic q x) χ ∈ imageSpan q V W₀ := by
  have hsm : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ,
      (x • ψ).toFn = rightTranslate ℚ (AdelicDock.padicToAdelic q x) ψ.toFn := fun ψ =>
    funext fun y => by rw [AdelicFnCarrier.padic_smul_def, AdelicFnCarrier.toFn_smul, rightTranslate_apply]
  unfold imageSpan at hχ
  induction hχ using Submodule.span_induction with
  | mem χ hχ =>
    obtain ⟨θ, ψ', hψ', rfl⟩ := hχ
    rw [← hsm, ← θ.2.1 x ψ' hψ']
    exact toFn_mem_imageSpan θ (hst x ψ' hψ')
  | zero => rw [rightTranslate_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [rightTranslate_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [rightTranslate_smul]; exact Submodule.smul_mem _ c hf

private theorem rightTranslate_mem_imageSpan_of_eq_mul
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀)
    {g h : AdelicGL2 (𝓞 ℚ) ℚ} {k : GL (Fin 2) ℚ_[q]} (hg : g = h * AdelicDock.padicToAdelic q k)
    (hcomm : ∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h)
    (hV : ∀ φ ∈ V, rightTranslate ℚ h φ ∈ V) {χ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hχ : χ ∈ imageSpan q V W₀) :
    rightTranslate ℚ g χ ∈ imageSpan q V W₀ := by
  rw [hg, ← rightTranslate_rightTranslate]
  exact rightTranslate_mem_imageSpan_of_commute h hcomm hV (rightTranslate_padicToAdelic_mem_imageSpan hst k hχ)

private theorem mk_mem_span_of_mem_imageSpan {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ imageSpan q V W₀) :
    LocalNewvector.AdelicFnCarrier.mk f ∈ Submodule.span ℂ {χ : LocalNewvector.AdelicFnCarrier ℚ |
      ∃ (θ : family q V W₀) (ψ' : LocalNewvector.AdelicFnCarrier ℚ), ψ'.toFn ∈ W₀ ∧ χ = θ.1 ψ'} := by
  have h := Submodule.mem_map_of_mem (f := mkₗ) hf
  rw [imageSpan, Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨θ, ψ', hψ', rfl⟩, rfl⟩
  exact ⟨θ, ψ', hψ', rfl⟩

end LocalNewvector.EquivariantSpan
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"

noncomputable section

open NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace EquivariantSpan
p2m_open "LocalNewvector"

variable {q : ℕ} [Fact q.Prime]
variable {V W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}

private theorem rightTranslate_padicToAdelic_mem_of_isCuspSubrep {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ}
    (hV : IsCuspSubrep ℚ pins ξ V) (x : GL (Fin 2) ℚ_[q]) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ V) :
    rightTranslate ℚ (AdelicDock.padicToAdelic q x) φ ∈ V :=
  hV.rightTranslate_fin_mem _
    ((mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_padicToAdelic q x)) φ hφ

private theorem isCuspSubrep_imageSpan {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ} (hV : IsCuspSubrep ℚ pins ξ V)
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀)
    (hfac : ∀ g ∈ finiteAdelicGL2Subgroup ℚ, ∃ (k : GL (Fin 2) ℚ_[q]) (h : AdelicGL2 (𝓞 ℚ) ℚ),
      h ∈ finiteAdelicGL2Subgroup ℚ ∧ (∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h) ∧
        g = h * AdelicDock.padicToAdelic q k)
    (hcommArch : ∀ (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) ℚ_[q]),
      Commute (AdelicDock.padicToAdelic q x) (rowIsometryInclAt₀ ℚ w k))
    (hconv : ∀ (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
      IsFactorizableTestFn ℚ f → IsArchBiFinite ℚ tys f →
        ∀ χ ∈ imageSpan q V W₀, rightConv ℚ χ f ∈ imageSpan q V W₀) :
    IsCuspSubrep ℚ pins ξ (imageSpan q V W₀) where
  le := imageSpan_le.trans hV.le
  rightTranslate_fin_mem g hg χ hχ := by
    obtain ⟨k, h, hh, hcomm, rfl⟩ := hfac g hg
    exact rightTranslate_mem_imageSpan_of_eq_mul hst rfl hcomm (hV.rightTranslate_fin_mem h hh) hχ
  rightTranslate_arch_mem w k χ hχ :=
    rightTranslate_mem_imageSpan_of_commute _ (hcommArch w k) (hV.rightTranslate_arch_mem w k) hχ
  rightConv_mem := hconv

private theorem exists_family_span_of_isCuspConstituent (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    (hV : IsCuspConstituent ℚ pins ξ V) (q : ℕ) [Fact q.Prime] (hle : W₀ ≤ V) (hW₀ : W₀ ≠ ⊥)
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀)
    (hfac : ∀ g ∈ finiteAdelicGL2Subgroup ℚ, ∃ (k : GL (Fin 2) ℚ_[q]) (h : AdelicGL2 (𝓞 ℚ) ℚ),
      h ∈ finiteAdelicGL2Subgroup ℚ ∧ (∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h) ∧
        g = h * AdelicDock.padicToAdelic q k)
    (hcommArch : ∀ (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) ℚ_[q]),
      Commute (AdelicDock.padicToAdelic q x) (rowIsometryInclAt₀ ℚ w k))
    (hconv : ∀ (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
      IsFactorizableTestFn ℚ f → IsArchBiFinite ℚ tys f →
        ∀ χ ∈ imageSpan q V W₀, rightConv ℚ χ f ∈ imageSpan q V W₀) :
    ∃ (κ : Type) (θ : κ → (LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
      (∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ →
        θ i (x • ψ) = x • θ i ψ) ∧
      (∀ (i : κ) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (θ i ψ).toFn ∈ V) ∧
      ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V →
        ψ ∈ Submodule.span ℂ {χ : LocalNewvector.AdelicFnCarrier ℚ |
          ∃ (i : κ) (ψ' : LocalNewvector.AdelicFnCarrier ℚ), ψ'.toFn ∈ W₀ ∧ χ = θ i ψ'} := by
  have hS : IsCuspSubrep ℚ pins ξ (imageSpan q V W₀) := isCuspSubrep_imageSpan hV.1 hst hfac hcommArch hconv
  have hSV : imageSpan q V W₀ = V := by
    rcases hV.2.2 _ hS imageSpan_le with h | h
    · exact absurd (le_bot_iff.mp ((le_imageSpan hle).trans h.le)) hW₀
    · exact h
  refine ⟨family q V W₀, fun i => i.1, fun i => i.2.1, fun i => i.2.2, fun ψ hψ => ?_⟩
  have hmem : ψ.toFn ∈ imageSpan q V W₀ := by rw [hSV]; exact hψ
  exact mk_mem_span_of_mem_imageSpan hmem

end LocalNewvector.EquivariantSpan
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open AutomorphicForm AutomorphicForm.CuspidalConstituent

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def fixedSubmodule IsIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace EquivariantSpan
p2m_open "LocalNewvector"

variable {q : ℕ} [Fact q.Prime]
variable {V W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}

private theorem rightConv_mem_imageSpan {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ} (hV : IsCuspSubrep ℚ pins ξ V)
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀)
    (hfac : ∀ g ∈ finiteAdelicGL2Subgroup ℚ, ∃ (k : GL (Fin 2) ℚ_[q]) (h : AdelicGL2 (𝓞 ℚ) ℚ),
      h ∈ finiteAdelicGL2Subgroup ℚ ∧ (∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h) ∧
        g = h * AdelicDock.padicToAdelic q k)
    (hVc : ∀ φ ∈ V, Continuous φ) (hVs : ∀ φ ∈ V, IsKfSmooth ℚ φ)
    (hfinc : Continuous (AdelicDock.finEmbed (𝓞 ℚ) ℚ)) (harchc : Continuous (adelicArchGLIncl ℚ))
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ) (hf : IsFactorizableTestFn ℚ f)
    (hbf : IsArchBiFinite ℚ tys f) {χ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hχ : χ ∈ imageSpan q V W₀) :
    rightConv ℚ χ f ∈ imageSpan q V W₀ := by
  obtain ⟨Φ₀, Ψ₀, hΦ₀, hΨ₀, rfl⟩ := exists_tensorKernel_eq_of_isFactorizableTestFn hf
  have hχV : χ ∈ V := imageSpan_le hχ
  have hVst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ φ ∈ V, rightTranslate ℚ (AdelicDock.padicToAdelic q x) φ ∈ V :=
    fun x φ hφ => rightTranslate_padicToAdelic_mem_of_isCuspSubrep hV x hφ
  have hΦ₀c : Continuous Φ₀ := continuous_of_isArchTestFactor hΦ₀
  have hΦ₀s : HasCompactSupport Φ₀ := hasCompactSupport_of_isArchTestFactor hΦ₀

  by_cases hΨ : ∀ u, Ψ₀ u = 0
  · have h0 : tensorKernel Φ₀ Ψ₀ = fun _ => 0 := funext fun x => by
      show Φ₀ _ * Ψ₀ _ = 0
      rw [hΨ, mul_zero]
    rw [h0, rightConv_zero_right]
    exact Submodule.zero_mem _
  obtain ⟨u₀, hu₀⟩ := not_forall.mp hΨ

  obtain ⟨U₁, h₁o, h₁c, hχU⟩ := exists_isOpen_isCompact_forall_eq_of_isKfSmooth hfinc (hVs χ hχV)
  obtain ⟨U₂, h₂o, h₂c, hΨU⟩ := exists_isOpen_isCompact_forall_eq_of_isFinTestFactor hΨ₀
  obtain ⟨hUo, hUc⟩ := isOpen_isCompact_inf h₁o h₁c h₂o h₂c

  obtain ⟨s, coef, hexp⟩ := exists_finset_rightConv_eq_sum_rightTranslate_archOp (U₁ ⊓ U₂) hUo hUc χ
    (fun u hu g => hχU u hu.1 g) Φ₀ hΨ₀.2 (fun u hu b => hΨU u hu.2 b)
    (fun C hCc hCo a g => integrable_summand χ (hVc χ hχV) g Φ₀ hΦ₀c hΦ₀s C hCc hCo a
      (adelicArchGLIncl ℚ) harchc (AdelicDock.finEmbed (𝓞 ℚ) ℚ) hfinc eq_archIncl_mul_finEmbed)
  change rightConv ℚ χ (fun x => Φ₀ (AdelicLevel.glArch (𝓞 ℚ) ℚ x) * Ψ₀ (AdelicLevel.glFin (𝓞 ℚ) ℚ x)) ∈ _
  rw [hexp]

  have hint : ∀ φ ∈ V, ∀ g, Integrable (fun a => φ (g * adelicArchGLIncl ℚ a) * Φ₀ a) archHaarQ := by
    letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing ℚ)) := archGLBorel
    haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing ℚ)) := ⟨rfl⟩
    exact fun φ hφ g => integrable_arch_integrand archHaarQ φ (hVc φ hφ) g _ harchc Φ₀ hΦ₀c hΦ₀s
  have harch : archOp Φ₀ χ ∈ imageSpan q V W₀ := by
    refine map_mem_imageSpan_of_restrict hVst (archOpOn Φ₀ V hint) (fun x φ => ?_) (fun φ => ?_) hχ
    · exact archOp_rightTranslate_padicToAdelic q Φ₀ φ.1 x
    · obtain ⟨Uφ, hφo, hφc, hφU⟩ := exists_isOpen_isCompact_forall_eq_of_isKfSmooth hfinc (hVs φ.1 φ.2)
      obtain ⟨hker, hbf'⟩ := isFactorizableTestFn_and_isArchBiFinite_tensorKernel_indicator Φ₀ Ψ₀ tys hΦ₀ hu₀
        hbf Uφ hφo hφc
        (((finHaarQ (Uφ : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))).toReal⁻¹ : ℝ) : ℂ)
      exact archOp_mem_of_isCuspSubrep hV Φ₀ Uφ hφo hφc tys hker hbf' φ.1 φ.2 hφU

  have hsum : (fun g => ∑ k ∈ s, coef k *
        rightTranslate ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ k.out) (archOp Φ₀ χ) g) =
      ∑ k ∈ s, coef k • rightTranslate ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ k.out) (archOp Φ₀ χ) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  obtain ⟨kq, h, hh, hcomm, hk⟩ := hfac (AdelicDock.finEmbed (𝓞 ℚ) ℚ k.out)
    ((mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed _ _ _))
  exact rightTranslate_mem_imageSpan_of_eq_mul hst hk hcomm (hV.rightTranslate_fin_mem h hh) harch

private theorem exists_family_span_of_isCuspConstituent' (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    (hV : IsCuspConstituent ℚ pins ξ V) (q : ℕ) [Fact q.Prime] (hle : W₀ ≤ V) (hW₀ : W₀ ≠ ⊥)
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀)
    (harchc : Continuous (adelicArchGLIncl ℚ)) :
    ∃ (κ : Type) (θ : κ → (LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
      (∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ →
        θ i (x • ψ) = x • θ i ψ) ∧
      (∀ (i : κ) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (θ i ψ).toFn ∈ V) ∧
      ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V →
        ψ ∈ Submodule.span ℂ {χ : LocalNewvector.AdelicFnCarrier ℚ |
          ∃ (i : κ) (ψ' : LocalNewvector.AdelicFnCarrier ℚ), ψ'.toFn ∈ W₀ ∧ χ = θ i ψ'} :=
  have hVc : ∀ φ ∈ V, Continuous φ := fun _ hφ =>
    LocalNewvector.Members.continuous_of_mem_cuspKFiniteSubmodule pins ξ (hV.1.le hφ)
  have hVs : ∀ φ ∈ V, IsKfSmooth ℚ φ := fun _ hφ =>
    LocalNewvector.Members.isKfSmooth_of_mem_cuspKFiniteSubmodule pins ξ (hV.1.le hφ)
  exists_family_span_of_isCuspConstituent pins ξ hV q hle hW₀ hst
    (exists_padic_mul_eq_of_mem_finiteAdelicGL2Subgroup q)
    (fun w k x => show _ * _ = _ * _ from padicToAdelic_mul_archIncl q x (archGLIncl ℚ w ↑k))
    (fun f tys hf hbf _ hχ => rightConv_mem_imageSpan hV.1 hst (exists_padic_mul_eq_of_mem_finiteAdelicGL2Subgroup q)
      hVc hVs continuous_finEmbed harchc f tys hf hbf hχ)

end LocalNewvector.EquivariantSpan
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"

section

private def carrierToFn : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) where
  toFun := LocalNewvector.AdelicFnCarrier.toFn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector.EquivariantSpan"

private theorem toFn_smul_mem_of_isCuspConstituent (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (ξ : (windowPins c u d₁ d₂ T).Z →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) ξ V) (q : ℕ) [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) (hψ : ψ.toFn ∈ V) :
    (x • ψ).toFn ∈ V := by
  exact LocalNewvector.Members.toFn_smul_mem_of_isCuspConstituent _ ξ V hV q x ψ hψ

open _root_.LocalNewvector _root_.P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent.LocalNewvector LocalNewvector.AwayCarrier AutomorphicForm.CuspidalSpectrum in

private theorem exists_irreducible_stable_le_of_isCuspConstituent (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (windowPins c u d₁ d₂ T).Z →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) ξ V)
    (N₀ : Ideal (𝓞 ℚ)) (hN₀ : N₀ ≠ ⊥) (tys₀ : AutomorphicForm.ArchTypeFamily ℚ)
    (hne : V ⊓ levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) N₀ ⊓ archCutSubmodule ℚ tys₀ ≠ ⊥)
    (q : ℕ) [Fact q.Prime] :
    ∃ W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ), W₀ ≤ V ∧ W₀ ≠ ⊥ ∧
      (∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀) ∧
      ∀ W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ), W' ≤ W₀ →
        (∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W' → (x • ψ).toFn ∈ W') →
        W' = ⊥ ∨ W' = W₀ := by
  classical

  obtain ⟨α, β, Φ₀, hΦ₀⟩ := CuspidalSpectrum.exists_isSlabFundamentalDomain ℚ
  obtain ⟨σ, hσ⟩ := CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent ℚ c u d₁ d₂ T ξ V hV

  have hVst : ∀ (ψ : AdelicFnCarrier ℚ) (x : GL (Fin 2) ℚ_[q]), ψ.toFn ∈ V → (x • ψ).toFn ∈ V :=
    fun ψ x hψ => toFn_smul_mem_of_isCuspConstituent c u d₁ d₂ T ξ V hV q x ψ hψ
  have hVsm : ∀ f ∈ V, IsKfSmooth ℚ f :=
    fun f hf => LocalNewvector.Members.isKfSmooth_of_mem_cuspKFiniteSubmodule _ ξ (hV.1.le hf)

  have hcomm : ∀ h ∈ awayGroup q N₀, ∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h :=
    fun h hh x => padicToAdelic_mul_comm_of_finComponent_eq_one q h ((mem_awayGroup_iff q N₀ h).mp hh).2 x
  have hU : (windowPins c u d₁ d₂ T).U N₀ = levelOne (𝓞 ℚ) ℚ N₀ ⊓ finiteAdelicGL2Subgroup ℚ := rfl
  have hUaw : awayGroup q N₀ ≤ (windowPins c u d₁ d₂ T).U N₀ := by rw [hU]; exact awayGroup_le q N₀
  have hsplit : ∀ v ∈ (windowPins c u d₁ d₂ T).U N₀,
      ∃ k ∈ localLevel q N₀, ∃ h ∈ awayGroup q N₀, v = AdelicDock.padicToAdelic q k * h := by
    intro v hv
    rw [hU] at hv
    exact exists_mem_comap_mul_mem_awayGroup q N₀ v hv
  have hpad : ∀ k ∈ localLevel q N₀, AdelicDock.padicToAdelic q k ∈ (windowPins c u d₁ d₂ T).U N₀ := by
    intro k hk
    rw [hU]
    exact Subgroup.mem_comap.mp hk

  have harch : ∀ f ∈ archCutSubmodule ℚ tys₀, ∀ x : GL (Fin 2) ℚ_[q],
      (fun y => f (y * AdelicDock.padicToAdelic q x)) ∈ archCutSubmodule ℚ tys₀ :=
    fun f hf x => comp_mul_padicToAdelic_mem_archCutSubmodule hf q x
  set Z : Submodule ℂ (AdelicFnCarrier ℚ) := awayCarrier V (awayGroup q N₀) tys₀ with hZdef
  have hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z := fun x ψ hψ => smul_mem_awayCarrier hVst hcomm harch x hψ
  have hZV : ∀ ψ ∈ Z, ψ.toFn ∈ V := fun ψ hψ => hψ.1
  have hC : ∀ ψ : AdelicFnCarrier ℚ, ψ ∈ Z ⊓ fixedCarrier q (localLevel q N₀) ↔
      ψ ∈ Z ∧ ∀ k ∈ (localLevel q N₀ : Set (GL (Fin 2) ℚ_[q])), k • ψ = ψ := fun ψ => Iff.rfl
  haveI hCfd : FiniteDimensional ℂ ↥(Z ⊓ fixedCarrier q (localLevel q N₀)) :=
    finiteDimensional_awayCarrier_inf_fixedCarrier (windowPins c u d₁ d₂ T) N₀ hU hUaw hsplit
      (finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent ℚ c u d₁ d₂ T hd hcov ξ
        N₀ hN₀ tys₀ V hV)
  have hCne : Z ⊓ fixedCarrier q (localLevel q N₀) ≠ ⊥ :=
    awayCarrier_inf_fixedCarrier_ne_bot (windowPins c u d₁ d₂ T) N₀ hUaw hpad hne

  letI : DistribMulAction (GL (Fin 2) ℚ_[q]) ↥Z := stableAction q Z hZst
  haveI : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ ↥Z := stableAction_smulCommClass q Z hZst
  set F₀ : Submodule ℂ ↥Z := InvariantComplement.fixedSubmodule (localLevel q N₀) with hF₀def
  have hF₀ : ∀ z : ↥Z, z ∈ F₀ ↔ ∀ k ∈ (localLevel q N₀ : Set (GL (Fin 2) ℚ_[q])), k • z = z := fun z => Iff.rfl
  haveI : FiniteDimensional ℂ ↥F₀ :=
    finiteDimensional_of_fixed q Z hZst _ (Z ⊓ fixedCarrier q (localLevel q N₀)) hC F₀ hF₀
  have hF₀ne : F₀ ≠ ⊥ := fixed_ne_bot q Z hZst _ (Z ⊓ fixedCarrier q (localLevel q N₀)) hC hCne F₀ hF₀
  have hfin : ∀ z : ↥Z,
      ((fun k : GL (Fin 2) ℚ_[q] => k • z) '' (localLevel q N₀ : Set (GL (Fin 2) ℚ_[q]))).Finite :=
    fun z => stableAction_finite_image q Z hZst _ z (finite_smul_image_localLevel hVsm N₀ z.2)

  set ι : ↥Z →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) := LocalNewvector.AwayCarrier.carrierToFn ∘ₗ Z.subtype with hιdef
  have hι : ∀ z : ↥Z, ι z ∈ contMemberSubmodule ℚ Φ₀ ξ :=
    fun z => LocalNewvector.Members.mem_contMemberSubmodule_of_mem_cuspKFiniteSubmodule c u d₁ d₂ T hd hcov ξ hΦ₀
      (hV.1.le (hZV z z.2))
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (AdelicFnCarrier.ext fun g => congrFun hab g)
  have hιsmul : ∀ (x : GL (Fin 2) ℚ_[q]) (z : ↥Z),
      ι (x • z) = rightTranslate ℚ (AdelicDock.padicToAdelic q x) (ι z) :=
    fun x z => LocalNewvector.Members.toFn_padic_smul q x z
  have hlift : ∀ x : GL (Fin 2) ℚ_[q],
      ∃ T₁ T₂ : CuspidalSpectrum.Carrier ℚ Φ₀ σ →L[ℂ] CuspidalSpectrum.Carrier ℚ Φ₀ σ,
      CuspidalSpectrum.IsLift ℚ hΦ₀ σ ξ (rightTranslate ℚ (AdelicDock.padicToAdelic q x)) T₁ ∧
      CuspidalSpectrum.IsLift ℚ hΦ₀ σ ξ (rightTranslate ℚ (AdelicDock.padicToAdelic q x)⁻¹) T₂ ∧
      ContinuousLinearMap.adjoint T₁ =
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x)) ^ σ : ℝ) : ℂ) •
          T₂ := by
    intro x
    obtain ⟨T₁, T₂, h₁, h₂, h₃, -⟩ :=
      CuspidalSpectrum.exists_isLift_rightTranslate ℚ α β Φ₀ hΦ₀ σ ξ hσ (AdelicDock.padicToAdelic q x)
    exact ⟨T₁, T₂, h₁, h₂, h₃⟩

  obtain ⟨e, he_mem, he_id, he_adj, he_stable⟩ :=
    InvariantComplement.exists_linearMap_fixedSubmodule (localLevel q N₀) (CarrierForm.form hΦ₀ σ ξ ι hι)
      (CarrierForm.form_add_left hΦ₀ σ ξ ι hι) (CarrierForm.form_add_right hΦ₀ σ ξ ι hι)
      (CarrierForm.form_smul_left_eq_zero hΦ₀ σ ξ ι hι) (CarrierForm.form_smul_right_eq_zero hΦ₀ σ ξ ι hι)
      (fun k hk y z =>
        CarrierForm.form_smul_smul hΦ₀ σ ξ ι hι q hιsmul k (hlift k)
          (ideleNorm_det_padicToAdelic_eq_one q N₀ k hk) y z)
      (CarrierForm.eq_zero_of_form_self_eq_zero hΦ₀ σ ξ ι hι hιinj) hfin

  obtain ⟨W, hWne, hWst, -, hWmin⟩ :=
    exists_irreducible_stable_submodule_of_finiteDimensional_projection (GL (Fin 2) ℚ_[q]) ↥Z
      (CarrierForm.form hΦ₀ σ ξ ι hι) (CarrierForm.form_add_left hΦ₀ σ ξ ι hι)
      (CarrierForm.form_smul_left_eq_zero hΦ₀ σ ξ ι hι)
      (fun g y z h => CarrierForm.form_smul_left_eq_zero_of hΦ₀ σ ξ ι hι q hιsmul g (hlift g) y z h)
      (CarrierForm.form_zero_right hΦ₀ σ ξ ι hι) (CarrierForm.eq_zero_of_form_self_eq_zero hΦ₀ σ ξ ι hι hιinj)
      F₀ hF₀ne e he_mem he_id he_adj he_stable

  exact exists_irreducible_stable_le_of_subtype q V Z hZV (stableAction_coe_smul q Z hZst) W hWne hWst hWmin

open LocalNewvector.EquivariantSpan in

private theorem exists_equivariant_family_span_eq_of_isCuspConstituent (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (ξ : (windowPins c u d₁ d₂ T).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hV : IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) ξ V)
    (q : ℕ) [Fact q.Prime] (W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hle : W₀ ≤ V) (hW₀ : W₀ ≠ ⊥)
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀) :
    ∃ (κ : Type) (θ : κ → (LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
      (∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ →
        θ i (x • ψ) = x • θ i ψ) ∧
      (∀ (i : κ) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (θ i ψ).toFn ∈ V) ∧
      ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V →
        ψ ∈ Submodule.span ℂ {χ : LocalNewvector.AdelicFnCarrier ℚ |
          ∃ (i : κ) (ψ' : LocalNewvector.AdelicFnCarrier ℚ), ψ'.toFn ∈ W₀ ∧ χ = θ i ψ'} := by
  exact exists_family_span_of_isCuspConstituent' (windowPins c u d₁ d₂ T) ξ hV q hle hW₀ hst
    continuous_adelicArchGLIncl

private theorem exists_injective_equivariant_of_span_images (q : ℕ) [Fact q.Prime]
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hVst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V → (x • ψ).toFn ∈ V)
    (W₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hW₀ : W₀ ≠ ⊥)
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (x • ψ).toFn ∈ W₀)
    (hirr : ∀ W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ), W' ≤ W₀ →
      (∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W' → (x • ψ).toFn ∈ W') →
      W' = ⊥ ∨ W' = W₀)
    (κ : Type) (θ : κ → (LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ))
    (hθ : ∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ →
      θ i (x • ψ) = x • θ i ψ)
    (hθV : ∀ (i : κ) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ W₀ → (θ i ψ).toFn ∈ V)
    (hspan : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V →
      ψ ∈ Submodule.span ℂ {χ : LocalNewvector.AdelicFnCarrier ℚ |
        ∃ (i : κ) (ψ' : LocalNewvector.AdelicFnCarrier ℚ), ψ'.toFn ∈ W₀ ∧ χ = θ i ψ'}) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) W)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W),
      LocalNewvector.IsIrreducibleGLRep q W ∧
      ∃ (ι : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι →₀ W)),
        (∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V → Φ ψ = 0 → ψ = 0) ∧
        ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V →
          ∀ x : GL (Fin 2) ℚ_[q], Φ (x • ψ) = x • Φ ψ := by
  classical

  let Z₀ : Submodule ℂ (LocalNewvector.AdelicFnCarrier ℚ) := W₀.comap carrierToFn
  let ZV : Submodule ℂ (LocalNewvector.AdelicFnCarrier ℚ) := V.comap carrierToFn
  have memZ₀ : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ ∈ Z₀ ↔ ψ.toFn ∈ W₀ := fun ψ => Iff.rfl
  have memZV : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ ∈ ZV ↔ ψ.toFn ∈ V := fun ψ => Iff.rfl
  letI actZ₀ : DistribMulAction (GL (Fin 2) ℚ_[q]) Z₀ :=
    { smul := fun x z => ⟨x • z.1, hst x z.1 z.2⟩
      one_smul := fun z => Subtype.ext (one_smul _ z.1)
      mul_smul := fun x y z => Subtype.ext (mul_smul x y z.1)
      smul_zero := fun x => Subtype.ext (smul_zero x)
      smul_add := fun x a b => Subtype.ext (smul_add x a.1 b.1) }
  letI actZV : DistribMulAction (GL (Fin 2) ℚ_[q]) ZV :=
    { smul := fun x z => ⟨x • z.1, hVst x z.1 z.2⟩
      one_smul := fun z => Subtype.ext (one_smul _ z.1)
      mul_smul := fun x y z => Subtype.ext (mul_smul x y z.1)
      smul_zero := fun x => Subtype.ext (smul_zero x)
      smul_add := fun x a b => Subtype.ext (smul_add x a.1 b.1) }
  haveI commZ₀ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ Z₀ := ⟨fun x c z => Subtype.ext (smul_comm x c z.1)⟩
  haveI commZV : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ ZV := ⟨fun x c z => Subtype.ext (smul_comm x c z.1)⟩
  have toFn_injective : Function.Injective (LocalNewvector.AdelicFnCarrier.toFn (F := ℚ)) :=
    fun φ ψ h => LocalNewvector.AdelicFnCarrier.ext (fun g => congrFun h g)

  have hirrZ₀ : LocalNewvector.IsIrreducibleGLRep q Z₀ := by
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W₀).mp hW₀
      refine ⟨⟨LocalNewvector.AdelicFnCarrier.mk w, hw⟩, ?_⟩
      intro h
      apply hw0
      have h1 := congrArg (fun z : Z₀ => (z.1).toFn) h
      simpa using h1
    · intro p hp
      let W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) := (p.map Z₀.subtype).map carrierToFn
      have hW'le : W' ≤ W₀ := by
        rintro _ ⟨ψ, ⟨z, hz, rfl⟩, rfl⟩
        exact z.2
      have hW'st : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ),
          ψ.toFn ∈ W' → (x • ψ).toFn ∈ W' := by
        rintro x ψ ⟨_, ⟨z, hz, rfl⟩, hψ⟩
        have hψz : ψ = z.1 := toFn_injective hψ.symm
        subst hψz
        exact ⟨(x • z).1, ⟨x • z, hp x z hz, rfl⟩, rfl⟩
      rcases hirr W' hW'le hW'st with h | h
      · left
        refine (Submodule.eq_bot_iff p).mpr fun z hz => ?_
        have hz' : z.1.toFn ∈ W' := ⟨z.1, ⟨z, hz, rfl⟩, rfl⟩
        rw [h, Submodule.mem_bot] at hz'
        exact Subtype.ext (toFn_injective (by simpa using hz'))
      · right
        refine eq_top_iff.mpr fun z _ => ?_
        have hz : z.1.toFn ∈ W' := h ▸ z.2
        obtain ⟨_, ⟨z', hz', rfl⟩, hzz⟩ := hz
        have : z' = z := Subtype.ext (toFn_injective hzz)
        exact this ▸ hz'

  let f : κ → (Z₀ →ₗ[ℂ] ZV) := fun i => (θ i).restrict (fun ψ hψ => hθV i ψ hψ)
  have hf : ∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (z : Z₀), f i (x • z) = x • f i z :=
    fun i x z =>
    Subtype.ext (hθ i x z.1 z.2)
  have hfW : ⨆ i : κ, LinearMap.range (f i) = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    have hv : v.1 ∈ Submodule.span ℂ {χ : LocalNewvector.AdelicFnCarrier ℚ |
        ∃ (i : κ) (ψ' : LocalNewvector.AdelicFnCarrier ℚ), ψ'.toFn ∈ W₀ ∧ χ = θ i ψ'} := hspan v.1 v.2
    have hspanle : Submodule.span ℂ {χ : LocalNewvector.AdelicFnCarrier ℚ |
        ∃ (i : κ) (ψ' : LocalNewvector.AdelicFnCarrier ℚ), ψ'.toFn ∈ W₀ ∧ χ = θ i ψ'} ≤
        (⨆ i : κ, LinearMap.range (f i)).map ZV.subtype := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, ψ', hψ', rfl⟩
      refine ⟨f i ⟨ψ', hψ'⟩, Submodule.mem_iSup_of_mem i ⟨⟨ψ', hψ'⟩, rfl⟩, rfl⟩
    obtain ⟨u, hu, huv⟩ := hspanle hv
    have : u = v := Subtype.ext huv
    exact this ▸ hu
  obtain ⟨ι, L, hL, hLx⟩ :=
    LocalNewvector.exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top
      q Z₀ ZV hirrZ₀ κ f hf hfW
  obtain ⟨Φ, hΦ⟩ := L.exists_extend
  have hΦ' : ∀ (ψ : LocalNewvector.AdelicFnCarrier ℚ) (hψ : ψ ∈ ZV), Φ ψ = L ⟨ψ, hψ⟩ := fun ψ hψ =>
    LinearMap.congr_fun hΦ ⟨ψ, hψ⟩
  refine ⟨Z₀, inferInstance, inferInstance, actZ₀, commZ₀, hirrZ₀, ι, Φ, ?_, ?_⟩
  · intro ψ hψ h0
    have h1 : L ⟨ψ, hψ⟩ = 0 := (hΦ' ψ hψ).symm.trans h0
    have h2 : (⟨ψ, hψ⟩ : ZV) = 0 := hL (h1.trans (map_zero L).symm)
    exact congrArg Subtype.val h2
  · intro ψ hψ x
    rw [hΦ' (x • ψ) (hVst x ψ hψ), hΦ' ψ hψ]
    exact hLx x ⟨ψ, hψ⟩

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : IsCuspConstituent ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) ξ V)
    (N₀ : Ideal (𝓞 ℚ)) (hN₀ : N₀ ≠ ⊥) (tys₀ : AutomorphicForm.ArchTypeFamily ℚ)
    (hne : V ⊓ levelInvariantSubmodule ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
          (adelicBox ℚ)) N₀ ⊓ archCutSubmodule ℚ tys₀ ≠ ⊥)
    (q : ℕ) [Fact q.Prime] :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) W)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W),
      LocalNewvector.IsIrreducibleGLRep q W ∧
      ∃ (ι : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι →₀ W)),
        (∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V → Φ ψ = 0 → ψ = 0) ∧
        ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V →
          ∀ x : GL (Fin 2) ℚ_[q], Φ (x • ψ) = x • Φ ψ := by
  obtain ⟨W₀, hle, hW₀, hst, hirr⟩ := exists_irreducible_stable_le_of_isCuspConstituent c u d₁ d₂ T hd hcov ξ V
    hV N₀ hN₀ tys₀ hne q
  obtain ⟨κ, θ, hθ, hθV, hspan⟩ :=
    exists_equivariant_family_span_eq_of_isCuspConstituent c u d₁ d₂ T ξ V hV q W₀ hle hW₀ hst
  exact exists_injective_equivariant_of_span_images q V
    (fun x ψ hψ => toFn_smul_mem_of_isCuspConstituent c u d₁ d₂ T ξ V hV q x ψ hψ) W₀ hW₀ hst hirr κ θ hθ hθV
    hspan

#print axioms solution

end S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent (solution)
