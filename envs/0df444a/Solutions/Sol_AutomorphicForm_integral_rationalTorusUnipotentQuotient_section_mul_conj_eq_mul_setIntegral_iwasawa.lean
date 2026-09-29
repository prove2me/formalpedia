-- Prove2me | solution 1 for AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/13aa34cc-c1bd-50b0-8593-05d197aadd2e

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa.AutomorphicForm"
open IsDedekindDomain NumberField.TateGlobal
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K]

private theorem measurable_ofReal_ideleNorm_inv :
    Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹) :=
  ((continuous_ideleNorm K).measurable.inv).ennreal_ofReal

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F] in

private theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 F) F)).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

variable (F : Type) [Field F] [NumberField F] in

private theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_idele F
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
  infer_instance

end AutomorphicForm

section HeightUnipotent

open NumberField NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicHeight

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

section Generic

variable {A B : Type*} [CommRing A] [CommRing B]

private theorem glMap_unipotentGL2 (f : A →+* B) (x : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2]

end Generic

section LocalInvariance

variable {K : Type*} [NormedField K]

private theorem det_coe_unipotentGL2_mul (y : K) (h : GL (Fin 2) K) :
    ((unipotentGL2 y * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      (h : Matrix (Fin 2) (Fin 2) K).det := by
  rw [Units.val_mul, Matrix.det_mul]
  simp [unipotentGL2, Matrix.det_fin_two_of]

private theorem localHeight_unipotentGL2_mul (y : K) (h : GL (Fin 2) K) :
    localHeight (unipotentGL2 y * h) = localHeight h := by
  have hrow : rowNormSq ((unipotentGL2 y * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      rowNormSq (h : Matrix (Fin 2) (Fin 2) K) := by
    simp [rowNormSq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2]
  unfold localHeight
  rw [det_coe_unipotentGL2_mul, hrow]

private theorem finLocalHeight_unipotentGL2_mul (y : K) (h : GL (Fin 2) K) :
    finLocalHeight (unipotentGL2 y * h) = finLocalHeight h := by
  have hrow : rowMaxNorm ((unipotentGL2 y * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      rowMaxNorm (h : Matrix (Fin 2) (Fin 2) K) := by
    simp [rowMaxNorm, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2]
  unfold finLocalHeight
  rw [det_coe_unipotentGL2_mul, hrow]

end LocalInvariance

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem archHeight_glArch_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (unipotentGL2 x * g)) = archHeight F (glArch (𝓞 F) F g) := by
  unfold archHeight
  refine Finset.prod_congr rfl fun w _ => ?_
  have h1 : glArch (𝓞 F) F (unipotentGL2 x) = unipotentGL2 _ := glMap_unipotentGL2 _ x
  have h2 : ∀ y, archComponent F w (unipotentGL2 y) = unipotentGL2 _ :=
    fun y => glMap_unipotentGL2 _ y
  rw [map_mul, h1, map_mul, h2, localHeight_unipotentGL2_mul]

private theorem finHeight_glFin_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    finHeight F (glFin (𝓞 F) F (unipotentGL2 x * g)) = finHeight F (glFin (𝓞 F) F g) := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  have h1 : glFin (𝓞 F) F (unipotentGL2 x) = unipotentGL2 _ := glMap_unipotentGL2 _ x
  have h2 : ∀ y, finComponent (𝓞 F) F v (unipotentGL2 y) = unipotentGL2 _ :=
    fun y => glMap_unipotentGL2 _ y
  rw [map_mul, h1, map_mul, h2, finLocalHeight_unipotentGL2_mul]

private theorem adelicHeight_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (unipotentGL2 x * g) = adelicHeight F g := by
  unfold adelicHeight
  rw [archHeight_glArch_unipotentGL2_mul, finHeight_glFin_unipotentGL2_mul]

end Adelic

end AutomorphicForm

end HeightUnipotent

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

section Determinants

variable {R : Type*} [CommRing R]

private theorem generalLinearGroup_det_unipotentGL2 (x : R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  show Matrix.det !![(1 : R), x; 0, 1] = 1
  rw [Matrix.det_fin_two_of]
  simp

private theorem generalLinearGroup_det_unipotentGL2_mul (x : R) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, generalLinearGroup_det_unipotentGL2, one_mul]

end Determinants

private def leftInvariantSubgroup {G X : Type*} [Group G] (f : G → X) : Subgroup G where
  carrier := {x | ∀ g, f (x * g) = f g}
  one_mem' := fun g => by simp
  mul_mem' := by
    intro x y hx hy g
    rw [mul_assoc, hx, hy]
  inv_mem' := by
    intro x hx g
    have h := hx (x⁻¹ * g)
    rwa [mul_inv_cancel_left, eq_comm] at h

variable (F : Type) [Field F] [NumberField F]

private theorem rationalTorusUnipotent_le_of_globalPoints_borel_of_unipotentGL2 {S : Subgroup (AdelicGL2 (𝓞 F) F)}
    (hB : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) F, γ ∈ borelSubgroup F → globalPoints (𝓞 F) F γ ∈ S)
    (hN : ∀ x : AdeleRing (𝓞 F) F, unipotentGL2 x ∈ S) :
    rationalTorusUnipotent F ≤ S := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨ζ, rfl⟩
    refine hB _ ?_
    show ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom ζ :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    simp [Units.coe_map]
  · rintro _ ⟨a, rfl⟩
    refine hB _ ?_
    show Matrix.diagonal ![(a : F), 1] 1 0 = 0
    simp
  · rintro _ ⟨y, rfl⟩
    exact hN y.toAdd

private theorem ideleNorm_det_globalPoints_mul (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ * g))
      = ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

private theorem ideleNorm_det_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (unipotentGL2 x * g))
      = ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [generalLinearGroup_det_unipotentGL2_mul]

variable {F}

private theorem isInducedSection_globalPoints_mul {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} {s : ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hμF : IsIdeleClassChar (𝓞 F) F μ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
    (hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    φ (globalPoints (𝓞 F) F γ * g) = φ g := by
  have h₁ : ∀ u : Fˣ, etaFst μ α hα s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u) = 1 :=
    etaFst_isIdeleClassChar hμF hprin s
  have h₂ : ∀ u : Fˣ, etaSnd ν α hα s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u) = 1 :=
    etaSnd_isIdeleClassChar hνF hprin s
  rw [hφ _ (globalPoints_mem_adelicBorel (𝓞 F) F hγ) g, borelDiagFst_globalPoints (𝓞 F) F hγ,
    borelDiagSnd_globalPoints (𝓞 F) F hγ, h₁, h₂]
  simp

variable (F)

private theorem sectionPairing_integrand_rationalTorusUnipotent_mul
    {μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ}
    {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} {s s' : ℂ} {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ')
    (hμF : IsIdeleClassChar (𝓞 F) F μ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
    (hμ'F : IsIdeleClassChar (𝓞 F) F μ') (hν'F : IsIdeleClassChar (𝓞 F) F ν')
    (hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
    (hH : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      NumberField.AdelicHeight.adelicHeight F (unipotentGL2 x * g) = NumberField.AdelicHeight.adelicHeight F g)
    (a b R R' : ℝ) :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      ({g : AdelicGL2 (𝓞 F) F |
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}).indicator
            (fun _ => (1 : ℂ)) (x * g) *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F (x * g)) *
          (φ (x * g) * (starRingEnd ℂ) (φ' (x * g)))
        = ({g : AdelicGL2 (𝓞 F) F |
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}).indicator
            (fun _ => (1 : ℂ)) g *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F g) *
          (φ g * (starRingEnd ℂ) (φ' g)) := by
  intro x hx
  refine rationalTorusUnipotent_le_of_globalPoints_borel_of_unipotentGL2 F
    (S := leftInvariantSubgroup fun g : AdelicGL2 (𝓞 F) F =>
      ({g : AdelicGL2 (𝓞 F) F |
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}).indicator
            (fun _ => (1 : ℂ)) g *
        (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
          (NumberField.AdelicHeight.adelicHeight F g) *
        (φ g * (starRingEnd ℂ) (φ' g)))
    ?_ ?_ hx
  · intro γ hγ g
    simp only [Set.indicator_apply, Set.mem_setOf_eq, ideleNorm_det_globalPoints_mul,
      NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ hγ,
      isInducedSection_globalPoints_mul hφ hμF hνF hprin γ hγ,
      isInducedSection_globalPoints_mul hφ' hμ'F hν'F hprin γ hγ]
  · intro y g
    simp only [Set.indicator_apply, Set.mem_setOf_eq, ideleNorm_det_unipotentGL2_mul, hH,
      isInducedSection_unipotent_mul hφ, isInducedSection_unipotent_mul hφ']

private theorem isPrincipalTrivial_distribHaarChar_toHomUnits :
    IsPrincipalTrivial (R := 𝓞 F) (K := F)
      (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits) := by
  intro u
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
  apply Units.ext
  rw [MonoidHom.coe_toHomUnits, MonoidHom.comp_apply]
  have e : Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u := rfl
  rw [e, h]
  simp

private theorem measurable_out_of_forall_rationalTorusUnipotent_mul {X : Type*} [MeasurableSpace X]
    {G : AdelicGL2 (𝓞 F) F → X} (hG : Measurable G)
    (hinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g, G (x * g) = G g) :
    Measurable fun q : RationalTorusUnipotentQuotient F => G q.out := by
  refine measurable_from_quotient.2 ?_
  have hcomp : ((fun q : RationalTorusUnipotentQuotient F => G q.out) ∘ Quotient.mk'') = G := by
    funext g
    show G (Quotient.mk'' g : RationalTorusUnipotentQuotient F).out = G g
    have hobt1 := MulAction.orbitRel_apply.1
      (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' g : RationalTorusUnipotentQuotient F)))
    obtain ⟨x, hx⟩ := hobt1
    rw [← hx]
    exact hinv x x.2 g
  rw [hcomp]
  exact hG

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private noncomputable def torusIwasawaMap
    (p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) : AdelicGL2 (𝓞 F) F :=
  centralScalar (𝓞 F) F p.1 * diagOne p.2.1 * (p.2.2 : AdelicGL2 (𝓞 F) F)

private noncomputable def torusCoordinateMeasure (c : ℝ≥0∞) (D D' : Set (AdeleRing (𝓞 F) F)ˣ) :
    Measure ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) :=
  c • ((NumberField.Idele.idelicHaar F).restrict D).prod
    ((((NumberField.Idele.idelicHaar F).restrict D').withDensity
        fun t => ENNReal.ofReal ((ideleNorm F t)⁻¹)).prod (maximalCompactHaar F))

variable {F}

private theorem apply_out_mk_of_forall_rationalTorusUnipotent_mul {X : Type*} {G : AdelicGL2 (𝓞 F) F → X}
    (hinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, G (x * g) = G g)
    (g : AdelicGL2 (𝓞 F) F) :
    G (Quotient.mk'' g : RationalTorusUnipotentQuotient F).out = G g := by
  have hobt2 := MulAction.orbitRel_apply.1
    (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' g : RationalTorusUnipotentQuotient F)))
  obtain ⟨x, hx⟩ := hobt2
  rw [← hx]
  exact hinv x x.2 g

private theorem mk_rationalTorusUnipotent_mul {x : AdelicGL2 (𝓞 F) F} (hx : x ∈ rationalTorusUnipotent F)
    (g : AdelicGL2 (𝓞 F) F) :
    (Quotient.mk'' (x * g) : RationalTorusUnipotentQuotient F) = Quotient.mk'' g :=
  Quotient.sound' (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨⟨x, hx⟩, rfl⟩))

variable (F)

private theorem rationalTorusUnipotentQuotientMeasure_eq_map_torusIwasawaMap
    [SigmaFinite (NumberField.Idele.idelicHaar F)]
    (hΘ : Measurable (torusIwasawaMap F))
    (hw : Measurable fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((ideleNorm F t)⁻¹))
    (c : ℝ≥0∞)
      (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
        ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
          (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
          ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
            c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                  f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                    ENNReal.ofReal ((ideleNorm F t)⁻¹)
                ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (D D' : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F)) :
    rationalTorusUnipotentQuotientMeasure F =
      (torusCoordinateMeasure F c D D').map
        (fun p => (Quotient.mk'' (torusIwasawaMap F p) : RationalTorusUnipotentQuotient F)) := by
  have hΦ : Measurable
      fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        (Quotient.mk'' (torusIwasawaMap F p) : RationalTorusUnipotentQuotient F) :=
    measurable_quotient_mk''.comp hΘ
  refine Measure.ext fun S hS => ?_
  set f : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g =>
    ((fun g : AdelicGL2 (𝓞 F) F => (Quotient.mk'' g : RationalTorusUnipotentQuotient F)) ⁻¹' S).indicator
      (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) g
  have hf : Measurable f := measurable_one.indicator (measurable_quotient_mk'' hS)
  have hfinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g := by
    intro x hx g
    show S.indicator (1 : RationalTorusUnipotentQuotient F → ℝ≥0∞)
        (Quotient.mk'' (x * g) : RationalTorusUnipotentQuotient F)
      = S.indicator (1 : RationalTorusUnipotentQuotient F → ℝ≥0∞) (Quotient.mk'' g : RationalTorusUnipotentQuotient F)
    rw [mk_rationalTorusUnipotent_mul hx]
  have hL : rationalTorusUnipotentQuotientMeasure F S =
      ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) := by
    rw [← lintegral_indicator_one hS]
    refine lintegral_congr fun q => ?_
    show S.indicator (1 : RationalTorusUnipotentQuotient F → ℝ≥0∞) q
      = S.indicator (1 : RationalTorusUnipotentQuotient F → ℝ≥0∞)
          (Quotient.mk'' q.out : RationalTorusUnipotentQuotient F)
    rw [Quotient.out_eq']
  have hR : (torusCoordinateMeasure F c D D').map
        (fun p => (Quotient.mk'' (torusIwasawaMap F p) : RationalTorusUnipotentQuotient F)) S =
      c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
            f (torusIwasawaMap F (z, (t, k))) * ENNReal.ofReal ((ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
    rw [Measure.map_apply hΦ hS, ← lintegral_indicator_one (hΦ hS)]
    have hpt : ∀ p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F,
        ((fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
            (Quotient.mk'' (torusIwasawaMap F p) : RationalTorusUnipotentQuotient F)) ⁻¹' S).indicator
          1 p = f (torusIwasawaMap F p) := by
      intro p
      rfl
    simp only [hpt]
    unfold torusCoordinateMeasure
    simp only [lintegral_smul_measure, smul_eq_mul]
    congr 1
    have hfΘ : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        f (torusIwasawaMap F p) := hf.comp hΘ
    rw [lintegral_prod _ hfΘ.aemeasurable]
    refine lintegral_congr fun z => ?_
    have hfz : Measurable fun q : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        f (torusIwasawaMap F (z, q)) := hfΘ.comp measurable_prodMk_left
    rw [lintegral_prod _ hfz.aemeasurable]
    have hg : Measurable fun t : (AdeleRing (𝓞 F) F)ˣ =>
        ∫⁻ k, f (torusIwasawaMap F (z, (t, k))) ∂(maximalCompactHaar F) :=
      hfz.lintegral_prod_right'
    rw [lintegral_withDensity_eq_lintegral_mul _ hw hg]
    refine lintegral_congr fun t => ?_
    have hk : Measurable fun k : adelicMaximalCompact F => f (torusIwasawaMap F (z, (t, k))) :=
      hfz.comp measurable_prodMk_left
    rw [Pi.mul_apply, lintegral_mul_const _ hk, mul_comm]
  rw [hL, hc D D' hD hD' hDF hD'F f hf hfinv, hR]
  rfl

private theorem integrable_out_iff_and_integral_out_eq_of_eq_map {c : ℝ≥0∞} {D D' : Set (AdeleRing (𝓞 F) F)ˣ}
    (hmap : rationalTorusUnipotentQuotientMeasure F =
      (torusCoordinateMeasure F c D D').map
        (fun p => (Quotient.mk'' (torusIwasawaMap F p) : RationalTorusUnipotentQuotient F)))
    (hΘ : Measurable (torusIwasawaMap F)) {G : AdelicGL2 (𝓞 F) F → ℂ} (hG : Measurable G)
    (hinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, G (x * g) = G g) :
    (Integrable (fun q : RationalTorusUnipotentQuotient F => G q.out)
        (rationalTorusUnipotentQuotientMeasure F) ↔
      Integrable (fun p => G (torusIwasawaMap F p)) (torusCoordinateMeasure F c D D')) ∧
    ∫ q, G q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
      ∫ p, G (torusIwasawaMap F p) ∂(torusCoordinateMeasure F c D D') := by
  have hGq : Measurable fun q : RationalTorusUnipotentQuotient F => G q.out :=
    measurable_out_of_forall_rationalTorusUnipotent_mul F hG hinv
  have hΦ : Measurable
      fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        (Quotient.mk'' (torusIwasawaMap F p) : RationalTorusUnipotentQuotient F) :=
    measurable_quotient_mk''.comp hΘ
  have hcomp : ((fun q : RationalTorusUnipotentQuotient F => G q.out) ∘
      fun p => (Quotient.mk'' (torusIwasawaMap F p) : RationalTorusUnipotentQuotient F)) =
        fun p => G (torusIwasawaMap F p) :=
    funext fun p => apply_out_mk_of_forall_rationalTorusUnipotent_mul hinv _
  rw [hmap]
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure hGq.aestronglyMeasurable hΦ.aemeasurable, hcomp]
  · rw [integral_map hΦ.aemeasurable hGq.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p =>
      apply_out_mk_of_forall_rationalTorusUnipotent_mul hinv _)

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem diagOne_mem_adelicBorel (t : (AdeleRing (𝓞 F) F)ˣ) : diagOne t ∈ adelicBorel (𝓞 F) F := by
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  have hval : ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1] := rfl
  rw [hval]
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem borelDiagFst_diagOne (t : (AdeleRing (𝓞 F) F)ˣ) (hmem : diagOne t ∈ adelicBorel (𝓞 F) F) :
    borelDiagFst (⟨diagOne t, hmem⟩ : ↥(adelicBorel (𝓞 F) F)) = t := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0
      = (t : AdeleRing (𝓞 F) F)
  have hval : ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1] := rfl
  rw [hval, Matrix.diagonal_apply_eq]
  simp

private theorem borelDiagSnd_diagOne (t : (AdeleRing (𝓞 F) F)ˣ) (hmem : diagOne t ∈ adelicBorel (𝓞 F) F) :
    borelDiagSnd (⟨diagOne t, hmem⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1
      = (1 : AdeleRing (𝓞 F) F)
  have hval : ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1] := rfl
  rw [hval, Matrix.diagonal_apply_eq]
  simp

variable {F}

private theorem apply_centralScalar_mul_diagOne_mul_of_isInducedSection
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (z t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ (centralScalar (𝓞 F) F z * diagOne t * g)
      = ((χ₁ (z * t) : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * φ g := by
  have hz : centralScalar (𝓞 F) F z ∈ adelicBorel (𝓞 F) F :=
    centralScalar_mem_adelicBorel (R := 𝓞 F) (K := F) z
  have ht : diagOne t ∈ adelicBorel (𝓞 F) F := diagOne_mem_adelicBorel F t
  have hzt : centralScalar (𝓞 F) F z * diagOne t ∈ adelicBorel (𝓞 F) F :=
    (adelicBorel (𝓞 F) F).mul_mem hz ht
  have hprod : (⟨centralScalar (𝓞 F) F z * diagOne t, hzt⟩ : ↥(adelicBorel (𝓞 F) F))
      = (⟨centralScalar (𝓞 F) F z, hz⟩ : ↥(adelicBorel (𝓞 F) F)) * ⟨diagOne t, ht⟩ := rfl
  have h₁ : borelDiagFst (⟨centralScalar (𝓞 F) F z * diagOne t, hzt⟩ : ↥(adelicBorel (𝓞 F) F)) = z * t := by
    rw [hprod, map_mul, borelDiagFst_centralScalar (R := 𝓞 F) (K := F) z hz, borelDiagFst_diagOne F t ht]
  have h₂ : borelDiagSnd (⟨centralScalar (𝓞 F) F z * diagOne t, hzt⟩ : ↥(adelicBorel (𝓞 F) F)) = z := by
    rw [hprod, map_mul, borelDiagSnd_centralScalar (R := 𝓞 F) (K := F) z hz, borelDiagSnd_diagOne F t ht,
      mul_one]
  rw [hφ _ hzt g, h₁, h₂]

private theorem generalLinearGroup_det_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem generalLinearGroup_det_diagOne (t : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne t : AdelicGL2 (𝓞 F) F) = t := by
  apply Units.ext
  have hval : ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1] := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, hval, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem ideleNorm_det_centralScalar_mul_diagOne_mul (z t : (AdeleRing (𝓞 F) F)ˣ) {k : AdelicGL2 (𝓞 F) F}
    (hk : ideleNorm F (Matrix.GeneralLinearGroup.det k) = 1) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * diagOne t * k))
      = ideleNorm F z ^ 2 * ideleNorm F t := by
  rw [map_mul, map_mul, generalLinearGroup_det_centralScalar, generalLinearGroup_det_diagOne]
  unfold NumberField.TateGlobal.ideleNorm at hk ⊢
  simp only [map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow] at hk ⊢
  rw [hk, mul_one]

private theorem adelicHeight_centralScalar_mul_diagOne_mul (z t : (AdeleRing (𝓞 F) F)ˣ) {k : AdelicGL2 (𝓞 F) F}
    (hk : NumberField.AdelicHeight.adelicHeight F k = 1)
    (hz : ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.AdelicHeight.adelicHeight F (centralScalar (𝓞 F) F z * g)
        = NumberField.AdelicHeight.adelicHeight F g) :
    NumberField.AdelicHeight.adelicHeight F (centralScalar (𝓞 F) F z * diagOne t * k) = ideleNorm F t := by
  rw [mul_assoc, hz, NumberField.AdelicHeight.adelicHeight_diagOne_mul F t k, hk, mul_one]

private theorem sectionPairing_integrand_centralScalar_mul_diagOne_mul
    {χ₁ χ₂ χ₁' χ₂' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (hφ' : IsInducedSection (𝓞 F) F χ₁' χ₂' φ')
    (a b R R' : ℝ) (z t : (AdeleRing (𝓞 F) F)ˣ) {k : AdelicGL2 (𝓞 F) F}
    (hdet : ideleNorm F (Matrix.GeneralLinearGroup.det k) = 1) (hk : NumberField.AdelicHeight.adelicHeight F k = 1)
    (hz : ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.AdelicHeight.adelicHeight F (centralScalar (𝓞 F) F z * g)
        = NumberField.AdelicHeight.adelicHeight F g) :
    {g : AdelicGL2 (𝓞 F) F |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
      (fun _ => (1 : ℂ)) (centralScalar (𝓞 F) F z * diagOne t * k) *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
        (NumberField.AdelicHeight.adelicHeight F (centralScalar (𝓞 F) F z * diagOne t * k)) *
      (φ (centralScalar (𝓞 F) F z * diagOne t * k) *
        (starRingEnd ℂ) (φ' (centralScalar (𝓞 F) F z * diagOne t * k)))
    = ((χ₁ (z * t) : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) *
        (starRingEnd ℂ) (((χ₁' (z * t) : ℂˣ) : ℂ) * ((χ₂' z : ℂˣ) : ℂ)) *
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
        (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
        (φ k * (starRingEnd ℂ) (φ' k)) := by
  have hslab : {g : AdelicGL2 (𝓞 F) F |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
      (fun _ => (1 : ℂ)) (centralScalar (𝓞 F) F z * diagOne t * k)
      = (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) := by
    simp only [Set.indicator_apply, Set.mem_setOf_eq, ideleNorm_det_centralScalar_mul_diagOne_mul z t hdet]
  rw [hslab, adelicHeight_centralScalar_mul_diagOne_mul z t hk hz,
    apply_centralScalar_mul_diagOne_mul_of_isInducedSection hφ,
    apply_centralScalar_mul_diagOne_mul_of_isInducedSection hφ', map_mul (starRingEnd ℂ) (_ * _) (φ' k)]
  ring

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F) := by
  show Continuous (Units.map (Matrix.scalar (Fin 2) : AdeleRing (𝓞 F) F →+* Matrix (Fin 2) (Fin 2)
    (AdeleRing (𝓞 F) F)).toMonoidHom)
  refine Continuous.units_map _ ?_
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

private theorem continuous_diagOne :
    Continuous (fun t : (AdeleRing (𝓞 F) F)ˣ => (diagOne t : AdelicGL2 (𝓞 F) F)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => (t : AdeleRing (𝓞 F) F)
      exact Units.continuous_val
    · exact continuous_const
  · simp_rw [← map_inv]
    show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      exact Units.continuous_coe_inv
    · exact continuous_const

private theorem measurable_torusIwasawaMap : Measurable (torusIwasawaMap F) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  exact (((continuous_centralScalar F).measurable.comp measurable_fst).mul
      ((continuous_diagOne F).measurable.comp (measurable_fst.comp measurable_snd))).mul
    (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

section LocalHeights

variable {K : Type*} [NormedField K]

private theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    NumberField.AdelicHeight.finLocalHeight (s * g) = NumberField.AdelicHeight.finLocalHeight g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z * z := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hz : ‖z‖ ≠ 0 := by
    have hunit := (Matrix.isUnits_det_units s).ne_zero
    rw [hdets] at hunit
    exact norm_ne_zero_iff.2 (left_ne_zero_of_mul hunit)
  have e10 : ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 0
      = z * (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  have e11 : ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 1
      = z * (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold NumberField.AdelicHeight.finLocalHeight NumberField.AdelicHeight.rowMaxNorm
  rw [Units.val_mul, Matrix.det_mul, hdets, e10, e11]
  simp only [norm_mul]
  rw [← mul_max_of_nonneg _ _ (norm_nonneg z), mul_pow, pow_two ‖z‖]
  exact mul_div_mul_left _ _ (mul_ne_zero hz hz)

end LocalHeights

variable (F : Type) [Field F] [NumberField F]

private theorem finHeight_glFin_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ)
    (X : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    NumberField.AdelicHeight.finHeight F (glFin (𝓞 F) F (centralScalar (𝓞 F) F z) * X)
      = NumberField.AdelicHeight.finHeight F X := by
  have hval : ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) := rfl
  unfold NumberField.AdelicHeight.finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul (finComponent (𝓞 F) F v)]
  refine finLocalHeight_scalar_entries_mul (z := (z : AdeleRing (𝓞 F) F).2 v) ?_ ?_ ?_ ?_ _ <;>
    simp [finComponent_apply, glFin_apply, hval] <;> rfl

private theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    NumberField.AdelicHeight.adelicHeight F (centralScalar (𝓞 F) F z * g)
      = NumberField.AdelicHeight.adelicHeight F g := by
  have hval : ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) := rfl
  have hz : ∀ w : InfinitePlace F, (z : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
    intro w
    have h1 : (z : AdeleRing (𝓞 F) F).1 w * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 := by
      have h := congrArg (fun a : AdeleRing (𝓞 F) F => a.1 w) (Units.mul_inv z)
      exact h
    exact left_ne_zero_of_mul_eq_one h1
  unfold NumberField.AdelicHeight.adelicHeight
  rw [map_mul (glArch (𝓞 F) F), map_mul (glFin (𝓞 F) F), finHeight_glFin_centralScalar_mul]
  congr 1
  refine WindowedSiegel.archHeight_scalar_entries_mul F hz ?_ ?_ ?_ ?_ _ <;> simp [glArch_apply, hval] <;> rfl

variable {F}

private theorem adelicHeight_eq_one_of_mem_adelicMaximalCompact {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ adelicMaximalCompact F) : NumberField.AdelicHeight.adelicHeight F k = 1 := by
  have hobt3 := (mem_adelicMaximalCompact_iff (K := F)).1 hk
  obtain ⟨hfin, harch⟩ := hobt3
  rw [NumberField.AdelicHeight.adelicHeight_eq_archHeight_of_mem hfin, ← one_mul (glArch (𝓞 F) F k),
    WindowedSiegel.archHeight_mul_rowIsometry F 1 harch, WindowedSiegel.archHeight_one F]

private theorem ideleNorm_det_eq_one_of_mem_adelicMaximalCompact {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ adelicMaximalCompact F) : ideleNorm F (Matrix.GeneralLinearGroup.det k) = 1 := by
  have hobt4 := (mem_adelicMaximalCompact_iff (K := F)).1 hk
  obtain ⟨hfin, harch⟩ := hobt4
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F k hfin]
  refine Finset.prod_eq_one fun w _ => ?_
  unfold NumberField.AdelicVolume.archDetNorm
  rw [(harch w).1, one_pow]

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

section RealWindows

private theorem rpow_le_rpow_add_rpow_of_mem_Icc {x lo hi : ℝ} (hlo : 0 < lo) (hx : x ∈ Set.Icc lo hi) (e : ℝ) :
    x ^ e ≤ lo ^ e + hi ^ e := by
  rcases le_or_gt 0 e with he | he
  · calc x ^ e ≤ hi ^ e := Real.rpow_le_rpow (hlo.le.trans hx.1) hx.2 he
      _ ≤ lo ^ e + hi ^ e := le_add_of_nonneg_left (Real.rpow_nonneg hlo.le e)
  · calc x ^ e ≤ lo ^ e := Real.rpow_le_rpow_of_nonpos hlo hx.1 he.le
      _ ≤ lo ^ e + hi ^ e := le_add_of_nonneg_right (Real.rpow_nonneg (hlo.le.trans (hx.1.trans hx.2)) e)

private theorem slab_indicator_mul_shell_indicator_eq_zero {a b R R' tmin tmax zlo zhi x y : ℝ} (ha : 0 < a)
    (htmin : 0 < tmin) (htmax : 0 < tmax)
    (hshell : ∀ u, u ∈ Set.Ioc (Real.exp R) (Real.exp R') → u ∈ Set.Icc tmin tmax)
    (hzlo : zlo ≤ a / tmax) (hzhi : b / tmin ≤ zhi)
    (h : ¬ (x * 1 ∈ Set.Icc zlo zhi ∧ y ∈ Set.Icc tmin tmax)) :
    (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (x * y) *
      (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) y = 0 := by
  by_cases hxy : x * y ∈ Set.Icc a b
  · by_cases hy : y ∈ Set.Ioc (Real.exp R) (Real.exp R')
    · exfalso
      apply h
      have hyw := hshell y hy
      have hy0 : 0 < y := htmin.trans_le hyw.1
      have hx0 : 0 ≤ x := ((mul_pos_iff_of_pos_right hy0).1 (ha.trans_le hxy.1)).le
      refine ⟨⟨?_, ?_⟩, hyw⟩
      · rw [mul_one]
        refine hzlo.trans ?_
        rw [div_le_iff₀ htmax]
        exact hxy.1.trans (mul_le_mul_of_nonneg_left hyw.2 hx0)
      · rw [mul_one]
        refine le_trans ?_ hzhi
        rw [le_div_iff₀ htmin]
        exact (mul_le_mul_of_nonneg_left hyw.1 hx0).trans hxy.2
    · rw [Set.indicator_of_notMem hy, mul_zero]
  · rw [Set.indicator_of_notMem hxy, zero_mul]

end RealWindows

variable {F : Type} [Field F] [NumberField F]

section EtaNormFactorization

open NumberField

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem norm_etaSnd_apply_of_unitary {ν : (AdeleRing R K)ˣ →* ℂˣ}
    (hν : IsUnitaryChar R K ν) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    ‖((etaSnd ν α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (-(s.re + 1 / 2)) := by
  rw [etaSnd_apply, Units.val_mul, norm_mul, hν x, one_mul, norm_cpowChar_apply,
    Complex.neg_re, re_add_half]

end EtaNormFactorization

variable (F)

private theorem measurable_sectionPairing_integrand {φ φ' : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hφ'c : Continuous φ') (a b R R' : ℝ) :
    Measurable fun g : AdelicGL2 (𝓞 F) F =>
      {g : AdelicGL2 (𝓞 F) F |
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
        (fun _ => (1 : ℂ)) g *
        (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
          (NumberField.AdelicHeight.adelicHeight F g) *
        (φ g * (starRingEnd ℂ) (φ' g)) :=
  ((measurable_const.indicator (NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F a b)).mul
      ((measurable_const.indicator measurableSet_Ioc).comp
        (NumberField.AdelicHeight.continuous_adelicHeight F).measurable)).mul
    (hφc.measurable.mul (Complex.continuous_conj.measurable.comp hφ'c.measurable))

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

private theorem norm_indicator_one_le {β : Type*} (S : Set β) (r : β) : ‖S.indicator (fun _ => (1 : ℂ)) r‖ ≤ 1 := by
  unfold Set.indicator
  split_ifs <;> simp

variable {F : Type} [Field F] [NumberField F]

private theorem norm_etaFst_mul_mul_etaSnd_of_unitary {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (z t : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ)‖
      = ((α t : ℝˣ) : ℝ) ^ (s.re + 1 / 2) := by
  rw [norm_mul, norm_etaFst_apply_of_unitary hμ α hα s, norm_etaSnd_apply_of_unitary hν α hα s, map_mul α z t,
    Units.val_mul, Real.mul_rpow (hα z).le (hα t).le, Real.rpow_neg (hα z).le,
    mul_comm (((α z : ℝˣ) : ℝ) ^ (s.re + 1 / 2)) (((α t : ℝˣ) : ℝ) ^ (s.re + 1 / 2)),
    mul_inv_cancel_right₀ (Real.rpow_pos_of_pos (hα z) _).ne']

private theorem norm_sectionPairing_character_factor_le {μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (hμ' : IsUnitaryChar (𝓞 F) F μ')
    (hν' : IsUnitaryChar (𝓞 F) F ν') (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (s s' : ℂ) {tmin tmax : ℝ} (htmin : 0 < tmin) (z t : (AdeleRing (𝓞 F) F)ˣ)
    (ht : ((α t : ℝˣ) : ℝ) ∈ Set.Icc tmin tmax) :
    ‖((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
        (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ))‖
      ≤ (tmin ^ (s.re + 1 / 2) + tmax ^ (s.re + 1 / 2)) *
          (tmin ^ (s'.re + 1 / 2) + tmax ^ (s'.re + 1 / 2)) := by
  rw [norm_mul, Complex.norm_conj, norm_etaFst_mul_mul_etaSnd_of_unitary hμ hν α hα s,
    norm_etaFst_mul_mul_etaSnd_of_unitary hμ' hν' α hα s']
  have htmax : 0 ≤ tmax := htmin.le.trans (ht.1.trans ht.2)
  exact mul_le_mul (rpow_le_rpow_add_rpow_of_mem_Icc htmin ht _) (rpow_le_rpow_add_rpow_of_mem_Icc htmin ht _)
    (Real.rpow_nonneg (hα t).le _)
    (add_nonneg (Real.rpow_nonneg htmin.le _) (Real.rpow_nonneg htmax _))

private theorem exists_forall_norm_le_of_continuous_on_adelicMaximalCompact {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : adelicMaximalCompact F, ‖φ (k : AdelicGL2 (𝓞 F) F)‖ ≤ C := by
  have hcont : Continuous fun k : adelicMaximalCompact F => φ (k : AdelicGL2 (𝓞 F) F) :=
    hφc.comp continuous_subtype_val
  have hobt5 := (isCompact_range hcont).isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := hobt5
  exact ⟨max C 0, le_max_right _ _, fun k => (hC _ (Set.mem_range_self k)).trans (le_max_left _ _)⟩

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentQuotientMeasure unipotentGL2 AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar IsInducedSection isInducedSection_unipotent_mul borelSubgroup borelDiagFst borelDiagSnd adelicBorel globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar re_add_half norm_cpowChar_apply IsPrincipalTrivial etaFst etaSnd etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar norm_etaFst_apply_of_unitary adelicMaximalCompact mem_adelicMaximalCompact_iff maximalCompactHaar WindowedSiegel.archHeight_mul_rowIsometry WindowedSiegel.archHeight_one WindowedSiegel.archHeight_scalar_entries_mul ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private noncomputable def sectionPairingIntegrand (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) (a b R R' : ℝ)
    (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
    (fun _ => (1 : ℂ)) g *
  (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
    (NumberField.AdelicHeight.adelicHeight F g) *
  (φ g * (starRingEnd ℂ) (φ' g))

private noncomputable def torusCoordinateBase (D D' : Set (AdeleRing (𝓞 F) F)ˣ) :
    Measure ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) :=
  ((NumberField.Idele.idelicHaar F).restrict D).prod
    ((((NumberField.Idele.idelicHaar F).restrict D').withDensity
        fun t => ENNReal.ofReal ((ideleNorm F t)⁻¹)).prod (maximalCompactHaar F))

variable {F}

private theorem norm_mul_mul_mul_conj_le {x u v y y' : ℂ} {B C C' : ℝ} (hx : ‖x‖ ≤ B) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hy : ‖y‖ ≤ C) (hy' : ‖y'‖ ≤ C') : ‖x * u * v * (y * (starRingEnd ℂ) y')‖ ≤ B * (C * C') := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hx
  have hC : 0 ≤ C := (norm_nonneg _).trans hy
  have h1 : ‖x‖ * ‖u‖ ≤ B * 1 := mul_le_mul hx hu (norm_nonneg _) hB
  have h2 : ‖x‖ * ‖u‖ * ‖v‖ ≤ B * 1 * 1 := mul_le_mul h1 hv (norm_nonneg _) (by rw [mul_one]; exact hB)
  have h3 : ‖y‖ * ‖y'‖ ≤ C * C' := mul_le_mul hy hy' (norm_nonneg _) hC
  simp only [norm_mul, Complex.norm_conj]
  calc ‖x‖ * ‖u‖ * ‖v‖ * (‖y‖ * ‖y'‖) ≤ B * 1 * 1 * (C * C') :=
        mul_le_mul h2 h3 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by rw [mul_one, mul_one]; exact hB)
    _ = B * (C * C') := by ring

private theorem sectionPairingIntegrand_torusIwasawaMap {μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} {s s' : ℂ}
    {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ') (a b R R' : ℝ)
    (p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) :
    sectionPairingIntegrand F φ φ' a b R R' (torusIwasawaMap F p) =
      ((etaFst μ α hα s (p.1 * p.2.1) : ℂˣ) : ℂ) * ((etaSnd ν α hα s p.1 : ℂˣ) : ℂ) *
          (starRingEnd ℂ) (((etaFst μ' α hα s' (p.1 * p.2.1) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' p.1 : ℂˣ) : ℂ)) *
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F p.1 ^ 2 * ideleNorm F p.2.1) *
        (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F p.2.1) *
        (φ (p.2.2 : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (p.2.2 : AdelicGL2 (𝓞 F) F))) :=
  sectionPairing_integrand_centralScalar_mul_diagOne_mul hφ hφ' a b R R' p.1 p.2.1
    (ideleNorm_det_eq_one_of_mem_adelicMaximalCompact p.2.2.2)
    (adelicHeight_eq_one_of_mem_adelicMaximalCompact p.2.2.2) (adelicHeight_centralScalar_mul F p.1)

private theorem torusCoordinateBase_window_ne_top [SigmaFinite (NumberField.Idele.idelicHaar F)]
    {D D' : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    {zlo zhi tmin tmax : ℝ} (hzlo : 0 < zlo) (hz : zlo < zhi) (htmin : 0 < tmin) (ht : tmin < tmax) :
    torusCoordinateBase F D D'
        ({z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * 1 ∈ Set.Icc zlo zhi} ×ˢ
          ({t : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F t ∈ Set.Icc tmin tmax} ×ˢ
            (Set.univ : Set (adelicMaximalCompact F)))) ≠ ∞ := by
  have hobt6 :=
    NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const F D hD hDF zlo zhi hzlo hz
  obtain ⟨C, -, hC_top, hC⟩ := hobt6
  have hZ : (NumberField.Idele.idelicHaar F).restrict D
      {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * 1 ∈ Set.Icc zlo zhi} ≠ ∞ := by
    rw [Measure.restrict_apply' hD, Set.inter_comm, hC 1 one_pos]
    exact hC_top
  have hconst : ∫⁻ _ in {t : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F t ∈ Set.Icc tmin tmax},
      ENNReal.ofReal tmin⁻¹ ∂((NumberField.Idele.idelicHaar F).restrict D') ≠ ∞ := by
    rw [setLIntegral_const, Measure.restrict_apply' hD', Set.inter_comm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top F D' hD' hD'F tmin tmax htmin
        ht).2.ne
  have hT : ((NumberField.Idele.idelicHaar F).restrict D').withDensity
      (fun t => ENNReal.ofReal ((ideleNorm F t)⁻¹))
        {t : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F t ∈ Set.Icc tmin tmax} ≠ ∞ := by
    rw [withDensity_apply']
    exact ne_top_of_le_ne_top hconst
      (setLIntegral_mono measurable_const fun t htw => ENNReal.ofReal_le_ofReal (inv_anti₀ htmin htw.1))
  unfold torusCoordinateBase
  rw [Measure.prod_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top hZ (ENNReal.mul_ne_top hT (measure_ne_top _ _))

private theorem integrable_sectionPairingIntegrand_torusIwasawaMap [SigmaFinite (NumberField.Idele.idelicHaar F)]
    {D D' : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
    {μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμ' : IsUnitaryChar (𝓞 F) F μ') (hν' : IsUnitaryChar (𝓞 F) F ν') {α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ}
    {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} (hαn : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x) {s s' : ℂ}
    {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
    (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ')
    (hφc : Continuous φ) (hφ'c : Continuous φ') {a : ℝ} (b R R' : ℝ) (ha : 0 < a) :
    Integrable (fun p => sectionPairingIntegrand F φ φ' a b R R' (torusIwasawaMap F p))
      (torusCoordinateBase F D D') := by
  obtain ⟨tmax, hRtmax, hR'tmax⟩ : ∃ tmax : ℝ, Real.exp R < tmax ∧ Real.exp R' ≤ tmax :=
    ⟨max (Real.exp R') (Real.exp R + 1), lt_of_lt_of_le (lt_add_one _) (le_max_right _ _), le_max_left _ _⟩
  have htmin : 0 < Real.exp R := Real.exp_pos R
  have htmax : 0 < tmax := htmin.trans hRtmax
  obtain ⟨zhi, hbzhi, hzhi⟩ : ∃ zhi : ℝ, b / Real.exp R ≤ zhi ∧ a / tmax < zhi :=
    ⟨max (b / Real.exp R) (a / tmax + 1), le_max_left _ _, lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)⟩
  have hobt7 := exists_forall_norm_le_of_continuous_on_adelicMaximalCompact hφc
  obtain ⟨Cφ, hCφ0, hCφ⟩ := hobt7
  have hobt8 := exists_forall_norm_le_of_continuous_on_adelicMaximalCompact hφ'c
  obtain ⟨Cφ', hCφ'0, hCφ'⟩ := hobt8
  have hG : Measurable (sectionPairingIntegrand F φ φ' a b R R') :=
    measurable_sectionPairing_integrand F hφc hφ'c a b R R'
  have hvan : ∀ p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F,
      p ∉ {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * 1 ∈ Set.Icc (a / tmax) zhi} ×ˢ
          ({t : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F t ∈ Set.Icc (Real.exp R) tmax} ×ˢ
            (Set.univ : Set (adelicMaximalCompact F))) →
        sectionPairingIntegrand F φ φ' a b R R' (torusIwasawaMap F p) = 0 := by
    intro p hp
    have h0 := slab_indicator_mul_shell_indicator_eq_zero (x := ideleNorm F p.1 ^ 2) (y := ideleNorm F p.2.1)
      ha htmin htmax (fun u hu => ⟨hu.1.le, hu.2.trans hR'tmax⟩) le_rfl hbzhi
      (fun hmem => hp ⟨hmem.1, hmem.2, Set.mem_univ _⟩)
    rw [sectionPairingIntegrand_torusIwasawaMap hφ hφ' a b R R' p]
    rcases mul_eq_zero.1 h0 with h | h <;> rw [h] <;> simp
  have hbound : ∀ p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F,
      ‖sectionPairingIntegrand F φ φ' a b R R' (torusIwasawaMap F p)‖ ≤
        (Real.exp R ^ (s.re + 1 / 2) + tmax ^ (s.re + 1 / 2)) *
            (Real.exp R ^ (s'.re + 1 / 2) + tmax ^ (s'.re + 1 / 2)) * (Cφ * Cφ') := by
    intro p
    by_cases hp : p ∈ {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * 1 ∈ Set.Icc (a / tmax) zhi} ×ˢ
        ({t : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F t ∈ Set.Icc (Real.exp R) tmax} ×ˢ
          (Set.univ : Set (adelicMaximalCompact F)))
    · have ht : ((α p.2.1 : ℝˣ) : ℝ) ∈ Set.Icc (Real.exp R) tmax := by
        rw [hαn]
        exact hp.2.1
      rw [sectionPairingIntegrand_torusIwasawaMap hφ hφ' a b R R' p]
      exact norm_mul_mul_mul_conj_le
        (norm_sectionPairing_character_factor_le hμ hν hμ' hν' α hα s s' htmin p.1 p.2.1 ht)
        (norm_indicator_one_le _ _) (norm_indicator_one_le _ _) (hCφ p.2.2) (hCφ' p.2.2)
    · rw [hvan p hp, norm_zero]
      exact mul_nonneg
        (mul_nonneg (add_nonneg (Real.rpow_nonneg htmin.le _) (Real.rpow_nonneg htmax.le _))
          (add_nonneg (Real.rpow_nonneg htmin.le _) (Real.rpow_nonneg htmax.le _)))
        (mul_nonneg hCφ0 hCφ'0)
  exact (Measure.integrableOn_of_bounded
      (torusCoordinateBase_window_ne_top hD hD' hDF hD'F (div_pos ha htmax) hzhi htmin hRtmax)
      (hG.comp (measurable_torusIwasawaMap F)).aestronglyMeasurable
      (ae_of_all _ hbound)).integrable_of_forall_notMem_eq_zero hvan

end AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c : ℝ≥0∞) (hc_top : c ≠ ∞)
      (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
        ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
          (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
          ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
            c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                  f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                    ENNReal.ofReal ((ideleNorm F t)⁻¹)
                ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
      (D D' : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D) (hD' : MeasurableSet D')
      (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (hD'F : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F))
      (μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
      (hμ' : IsUnitaryChar (𝓞 F) F μ') (hν' : IsUnitaryChar (𝓞 F) F ν')
      (hμF : IsIdeleClassChar (𝓞 F) F μ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
      (hμ'F : IsIdeleClassChar (𝓞 F) F μ') (hν'F : IsIdeleClassChar (𝓞 F) F ν')
      (s s' : ℂ) (φ φ' : AdelicGL2 (𝓞 F) F → ℂ)
      (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (hφ' : IsInducedSection (𝓞 F) F (etaFst μ' α hα s') (etaSnd ν' α hα s') φ')
      (hφc : Continuous φ) (hφ'c : Continuous φ')
      (a b R R' : ℝ) (ha : 0 < a),
    Integrable (fun q : RationalTorusUnipotentQuotient F =>
        {g : AdelicGL2 (𝓞 F) F |
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
          (fun _ => (1 : ℂ)) q.out *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F q.out) *
          (φ q.out * (starRingEnd ℂ) (φ' q.out)))
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F,
        {g : AdelicGL2 (𝓞 F) F |
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
          (fun _ => (1 : ℂ)) q.out *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F q.out) *
          (φ q.out * (starRingEnd ℂ) (φ' q.out))
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      (c.toReal : ℂ) *
        (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F)) *
        ∫ z in D, ∫ t in D',
            ((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
              (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ)) *
              (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  intro α hα c hc_top hc D D' hD hD' hDF hD'F μ ν μ' ν' hμ hν hμ' hν' hμF hνF hμ'F hν'F s s' φ φ' hφ hφ' hφc
    hφ'c a b R R' ha
  haveI : SigmaFinite (NumberField.Idele.idelicHaar F) := sigmaFinite_idelicHaar F
  have hαn : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x := fun _ => rfl
  have hmap := rationalTorusUnipotentQuotientMeasure_eq_map_torusIwasawaMap F (measurable_torusIwasawaMap F)
    (measurable_ofReal_ideleNorm_inv F) c hc D D' hD hD' hDF hD'F
  have hG : Measurable (sectionPairingIntegrand F φ φ' a b R R') :=
    measurable_sectionPairing_integrand F hφc hφ'c a b R R'
  have hinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      sectionPairingIntegrand F φ φ' a b R R' (x * g) = sectionPairingIntegrand F φ φ' a b R R' g :=
    sectionPairing_integrand_rationalTorusUnipotent_mul F hφ hφ' hμF hνF hμ'F hν'F
      (isPrincipalTrivial_distribHaarChar_toHomUnits F) (adelicHeight_unipotentGL2_mul (F := F)) a b R R'
  have hobt9 :=
    integrable_out_iff_and_integral_out_eq_of_eq_map F hmap (measurable_torusIwasawaMap F) hG hinv
  obtain ⟨hiff, heq⟩ := hobt9
  have hint : Integrable (fun p => sectionPairingIntegrand F φ φ' a b R R' (torusIwasawaMap F p))
      (torusCoordinateBase F D D') :=
    integrable_sectionPairingIntegrand_torusIwasawaMap hD hD' hDF hD'F hμ hν hμ' hν' hαn hφ hφ' hφc hφ'c b R R' ha
  refine ⟨hiff.2 (hint.smul_measure hc_top), heq.trans ?_⟩
  have hexp := sectionPairingIntegrand_torusIwasawaMap hφ hφ' a b R R'
  have hint' := hint.congr (ae_of_all _ hexp)
  have hw : ∀ᵐ t ∂((NumberField.Idele.idelicHaar F).restrict D'), ENNReal.ofReal ((ideleNorm F t)⁻¹) < ∞ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hnn : ∀ t : (AdeleRing (𝓞 F) F)ˣ, 0 ≤ (ideleNorm F t)⁻¹ :=
    fun t => inv_nonneg.2 ((hα t).le.trans_eq (hαn t))
  have hz : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ∫ t in D', (((ideleNorm F t)⁻¹ : ℝ) : ℂ) *
          (((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
              (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ)) *
              (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))
              ∂(maximalCompactHaar F))) ∂(NumberField.Idele.idelicHaar F) =
        (∫ t in D',
          ((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
            (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ)) *
            (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (((ideleNorm F t)⁻¹ : ℝ) : ℂ) ∂(NumberField.Idele.idelicHaar F)) *
          (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))
            ∂(maximalCompactHaar F)) := fun z => by
    rw [← integral_mul_const]
    exact integral_congr_ae (ae_of_all _ fun t => by ring)
  calc ∫ p, sectionPairingIntegrand F φ φ' a b R R' (torusIwasawaMap F p) ∂(torusCoordinateMeasure F c D D')
      = c.toReal • ∫ p, sectionPairingIntegrand F φ φ' a b R R' (torusIwasawaMap F p)
          ∂(torusCoordinateBase F D D') := integral_smul_measure _ _
    _ = c.toReal • ∫ z, ∫ t, ∫ k,
          ((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
            (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ)) *
            (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))) ∂(maximalCompactHaar F)
          ∂(((NumberField.Idele.idelicHaar F).restrict D').withDensity
            fun t => ENNReal.ofReal ((ideleNorm F t)⁻¹))
          ∂((NumberField.Idele.idelicHaar F).restrict D) := by
        congr 1
        refine ((integral_congr_ae (ae_of_all _ hexp)).trans (integral_prod _ hint')).trans ?_
        refine integral_congr_ae ?_
        filter_upwards [hint'.prod_right_ae] with z hzint
        exact integral_prod _ hzint
    _ = c.toReal • ∫ z, ∫ t,
          ((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
            (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ)) *
            (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))
              ∂(maximalCompactHaar F))
          ∂(((NumberField.Idele.idelicHaar F).restrict D').withDensity
            fun t => ENNReal.ofReal ((ideleNorm F t)⁻¹))
          ∂((NumberField.Idele.idelicHaar F).restrict D) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        exact integral_const_mul _ _
    _ = c.toReal • ∫ z, ∫ t in D', (((ideleNorm F t)⁻¹ : ℝ) : ℂ) *
          (((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
            (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ)) *
            (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
            (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
            (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))
              ∂(maximalCompactHaar F))) ∂(NumberField.Idele.idelicHaar F)
          ∂((NumberField.Idele.idelicHaar F).restrict D) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        beta_reduce
        rw [integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_ideleNorm_inv F) hw]
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only [ENNReal.toReal_ofReal (hnn t), Complex.real_smul]
    _ = (c.toReal : ℂ) *
        (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * (starRingEnd ℂ) (φ' (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F)) *
        ∫ z in D, ∫ t in D',
            ((etaFst μ α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd ν α hα s z : ℂˣ) : ℂ) *
              (starRingEnd ℂ) (((etaFst μ' α hα s' (z * t) : ℂˣ) : ℂ) * ((etaSnd ν' α hα s' z : ℂˣ) : ℂ)) *
              (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (ideleNorm F z ^ 2 * ideleNorm F t) *
              (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) (ideleNorm F t) *
              (((ideleNorm F t)⁻¹ : ℝ) : ℂ)
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
        rw [Complex.real_smul, integral_congr_ae (ae_of_all _ hz), integral_mul_const]
        ring

end S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa
end P2MW
export P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa (solution)
