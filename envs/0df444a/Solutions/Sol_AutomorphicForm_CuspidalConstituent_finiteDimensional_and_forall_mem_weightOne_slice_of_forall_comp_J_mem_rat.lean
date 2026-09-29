-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9a9f8a7f-68e9-58a7-a9eb-c71108113e9b

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse
open AutomorphicForm.CuspidalConstituent NumberField.AdelicVolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "finiteAdelicGL2Subgroup lsXiMemberAt_iff IsAutomorphicFnAt productionPinsOf AdelicGL2 centralScalar HeckeEigensystem glEquivOfRingEquiv rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightCharAt rowIsometrySubgroup₀ archWeightCharℝ HasArchCharacterAt₀ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archGLIncl adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl SiegelCovering.mul_centralScalar_comm archRealGLAt IsArchSmoothAt ArchDir archDerivAt archDerivAt_smul eq_of_glArch_eq_of_glFin_eq ArchDir.H ArchDir.Fm ArchDir.E isotypicCuspSubmodule ArchRepAt ArchRepAt.ofChar archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff mem_archTypeSubmoduleAt_ofChar_iff CuspidalConstituent.exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one CuspidalConstituent.lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule"
namespace RJClose
namespace K2pRat
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

theorem archRealGLAt_scalar_eq_centralScalar {w : InfinitePlace F} (hw : w.IsReal) (t : ℝˣ) :
    archRealGLAt hw (Matrix.GeneralLinearGroup.scalar (Fin 2) t)
      = centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) := by
  apply eq_of_glArch_eq_of_glFin_eq
  · show glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w _)) = _
    rw [glArch_adelicArchGLIncl]
    apply Units.ext
    apply Matrix.ext
    intro i j
    funext v
    show archMatrixUpdate F w _ i j v = _
    rw [show ((glArch (𝓞 F) F (centralScalar (𝓞 F) F
        (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t))) :
          GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j v
        = (((centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) :
            AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 v from rfl,
      centralScalar_val]
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, glEquivOfRingEquiv, Matrix.GeneralLinearGroup.scalar, archCentralUnit_fst_self]
      all_goals rfl
    · rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, archCentralUnit_fst_of_ne _ _ hv]
      all_goals rfl
  · show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w _)) = _
    rw [glFin_adelicArchGLIncl]
    apply Units.ext
    apply Matrix.ext
    intro i j
    show (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      = (((centralScalar (𝓞 F) F
          (archCentralUnit F w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom t)) :
            AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
    rw [centralScalar_val]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, archCentralUnit_snd]
    all_goals rfl

theorem J_eq_eps_mul_neg_one :
    UpperHalfPlane.J = Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, -1] (by simp)
      * Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : ℝˣ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.GeneralLinearGroup.scalar]

theorem hasArchCharacterAt₀_smul {w : InfinitePlace F} (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (a : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : HasArchCharacterAt₀ F w χ φ) :
    HasArchCharacterAt₀ F w χ (a • φ) := fun k g => by
  simp only [Pi.smul_apply, smul_eq_mul, h k g]
  ring

theorem apply_centralScalar_mul_of_mem (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (y : AdelicGL2 (𝓞 F) F → ℂ) (hy : y ∈ V) (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    y (centralScalar (𝓞 F) F z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g := by
  obtain ⟨-, hs⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
      F _ _ _ ξ y (hV.1.le hy)
  have h := (hs 1).1.1
  have hrt : rightTranslate F 1 y = y := funext fun g => by simp [rightTranslate]
  rw [hrt] at h
  unfold IsAutomorphicFnAt at h
  rw [lsXiMemberAt_iff] at h
  exact h.1.central_transform ⟨z, Subgroup.mem_top z⟩ g

end AutomorphicForm.RJClose.K2pRat

open AutomorphicForm.RJClose.K2pRat in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Ψ : HeckeEigensystem ℚ ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : IsCuspConstituent ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ V)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hsm : ∀ x ∈ V, IsArchSmoothAt hw x)
    (hJV : ∀ x ∈ V, (fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ V)
    (tys : ArchTypeFamily ℚ)
    (h₁ : ∃ i, tys.rep w i = ArchRepAt.ofChar ℚ ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))))
    (hm₁ : ∃ i, tys.rep w i = ArchRepAt.ofChar ℚ ((archWeightCharℝ (-1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))) :
    let Sp : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
      V ⊓ isotypicCuspSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Ψ ⊓ archCutSubmodule ℚ tys ⊓
        archTypeSubmoduleAt ℚ w (ArchRepAt.ofChar ℚ ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))))
    FiniteDimensional ℂ Sp ∧
    ∀ x ∈ Sp, (fun g => (archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x)) (g * archRealGLAt hw UpperHalfPlane.J)) ∈ Sp := by
  intro Sp

  have hisolev : isotypicCuspSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Ψ ≤
      levelInvariantSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) N :=
    Submodule.span_le.mpr fun φ hφ => hφ.level_invariant
  have hle : Sp ≤ V ⊓ levelInvariantSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) N ⊓ archCutSubmodule ℚ tys :=
    fun x hx => ⟨⟨hx.1.1.1, hisolev hx.1.1.2⟩, hx.1.2⟩
  haveI := AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
    ℚ c u d₁ d₂ T hd hcov ξ N hN tys V hV
  refine ⟨Submodule.finiteDimensional_of_le hle, fun x hx => ?_⟩

  have hxV : x ∈ V := hx.1.1.1
  have hxiso : x ∈ isotypicCuspSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Ψ := hx.1.1.2
  have hxcut : x ∈ archCutSubmodule ℚ tys := hx.1.2
  have hx1 : HasArchCharacterAt₀ ℚ w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) x :=
    (mem_archTypeSubmoduleAt_ofChar_iff ℚ w _ x).mp hx.2

  by_cases hx0 : x = 0
  · subst hx0
    have h0 : (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
        (archDerivAt hw ArchDir.H (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) - Complex.I •
          (archDerivAt hw ArchDir.E (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) + archDerivAt hw ArchDir.Fm (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
          (g * archRealGLAt hw UpperHalfPlane.J)) = 0 := by
      funext g
      have hz : ∀ d : ArchDir, archDerivAt hw d (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) = 0 := fun d => by
        have := archDerivAt_smul hw d 0 (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
        simpa using this
      simp [hz]
    rw [h0]
    exact Submodule.zero_mem _
  have hxlev : x ∈ levelInvariantSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) N := hisolev hxiso

  have hpure : ∀ (v : InfinitePlace ℚ) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ ℚ v (archWeightCharAt hv m) x :=
    fun v hv => by
      obtain rfl : v = w := Subsingleton.elim _ _
      exact ⟨1, hx1⟩
  obtain ⟨hlow, -⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
      ℚ c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys w hw x ⟨⟨hxV, hxlev⟩, hxcut⟩ hpure 1 hx1
  obtain ⟨⟨tys', hmem'⟩, -, hwt⟩ := hlow 1
  simp only [Function.iterate_one] at hmem' hwt
  set y : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
    archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x) with hy_def
  have hyV : y ∈ V := hmem'.1.1
  have hym1 : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (-1)) y := by
    have h12 : (1 : ℤ) - 2 * (1 : ℕ) = -1 := by norm_num
    rw [h12] at hwt
    exact hwt
  have hyiso : y ∈ isotypicCuspSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Ψ :=
    (AutomorphicForm.CuspidalConstituent.lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
      ℚ c u d₁ d₂ T ξ N S Ψ V hV w hw hsm x hxV hx0 hxiso).1 hyV

  set z : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun g => y (g * archRealGLAt hw UpperHalfPlane.J) with hz_def
  have hzV : z ∈ V := hJV y hyV
  have hziso : z ∈ isotypicCuspSubmodule ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Ψ := by
    by_cases hy0 : y = 0
    · have : z = 0 := by funext g; simp [hz_def, hy0]
      rw [this]; exact Submodule.zero_mem _
    exact (AutomorphicForm.CuspidalConstituent.lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
      ℚ c u d₁ d₂ T ξ N S Ψ V hV w hw hsm y hyV hy0 hyiso).2 hzV

  have hz1 : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) z := by
    obtain ⟨hflip, -, -⟩ :=
      AutomorphicForm.hasArchCharacterAt_neg_and_archCasimirAt_comp_mul_diag_one_neg_one ℚ hw y (-1) hym1
    simp only [neg_neg] at hflip
    set zc : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
      archCentralUnit ℚ w (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom (-1 : ℝˣ)) with hzc
    have hzfun : z = (((ξ ⟨zc, Subgroup.mem_top zc⟩ : ℂˣ) : ℂ)) •
        fun g => y (g * archRealGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, -1] (by simp))) := by
      funext g
      simp only [hz_def, Pi.smul_apply, smul_eq_mul]
      rw [J_eq_eps_mul_neg_one, map_mul, archRealGLAt_scalar_eq_centralScalar, ← mul_assoc,
        SiegelCovering.mul_centralScalar_comm, apply_centralScalar_mul_of_mem _ ξ V hV y hyV]
    rw [hzfun]
    exact hasArchCharacterAt₀_smul _ _ hflip
  have hzcut : z ∈ archCutSubmodule ℚ tys := by
    rw [mem_archCutSubmodule_iff]
    intro w'
    obtain rfl : w' = w := Subsingleton.elim _ _
    obtain ⟨i, hi⟩ := h₁
    apply Submodule.mem_iSup_of_mem i
    rw [hi]
    exact (mem_archTypeSubmoduleAt_ofChar_iff ℚ w' _ z).mpr hz1
  exact ⟨⟨⟨hzV, hziso⟩, hzcut⟩, (mem_archTypeSubmoduleAt_ofChar_iff ℚ w _ z).mpr hz1⟩

end S_AutomorphicForm_CuspidalConstituent_finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_finiteDimensional_and_forall_mem_weightOne_slice_of_forall_comp_J_mem_rat (solution)
