-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3d952c79-4d81-5e2a-975c-5c067bc54e1c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

section Prelim

variable (F : Type) [Field F] [NumberField F]

theorem secondCountableTopology_adele : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  NumberField.AdeleRing.secondCountableTopology F

theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_gl : SecondCountableTopology (AdelicGL2 (𝓞 F) F) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_idele F
  infer_instance

theorem sigmaFinite_adelicAddHaar : SigmaFinite (adelicAddHaar (𝓞 F) F) := by
  haveI := secondCountableTopology_adele F
  infer_instance

theorem isHaarMeasure_gl : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

theorem continuous_det :
    Continuous fun g : AdelicGL2 (𝓞 F) F => Matrix.GeneralLinearGroup.det g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    exact (Units.continuous_val.matrixVecCons continuous_const).matrix_diagonal
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    exact (Units.continuous_coe_inv.matrixVecCons continuous_const).matrix_diagonal

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal fun _ : Fin 2 => (u : AdeleRing (𝓞 F) F)
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun u : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

def word (p : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F) :
    AdelicGL2 (𝓞 F) F :=
  unipotentGL2 p.1.1.1 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F)

theorem continuous_word : Continuous (word F) := by
  unfold word
  exact (((AutomorphicForm.continuous_unipotentGL2.comp continuous_fst.fst.fst).mul
    ((continuous_centralScalar F).comp continuous_fst.fst.snd)).mul
    ((continuous_diagOne F).comp continuous_fst.snd)).mul (continuous_subtype_val.comp continuous_snd)

theorem measurable_word : Measurable (word F) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  exact (continuous_word F).measurable

def wt (p : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F) : ℝ≥0∞ :=
  ENNReal.ofReal ((ideleNorm F p.1.2)⁻¹)

theorem measurable_wt : Measurable (wt F) :=
  ENNReal.measurable_ofReal.comp
    (((NumberField.TateGlobal.continuous_ideleNorm F).measurable.comp measurable_fst.snd).inv)

end Prelim

section Bochner

variable (F : Type) [Field F] [NumberField F]

theorem integral_eq_mul_iwasawa (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc_top : c ≠ ∞)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨc : Continuous Ψ) (hΨs : HasCompactSupport Ψ) :
    ∫ g, Ψ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      (c.toReal : ℂ) * ∫ x, ∫ u, ∫ t, ∫ k,
          Ψ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            (((NumberField.TateGlobal.ideleNorm F t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI := sigmaFinite_idelicHaar F
  haveI := sigmaFinite_adelicAddHaar F
  haveI := isHaarMeasure_gl F
  set μG := adelicGLHaar (Fin 2) (𝓞 F) F with hμG
  set ν := NumberField.Idele.idelicHaar F with hν
  set dx := adelicAddHaar (𝓞 F) F with hdx
  set mK := maximalCompactHaar F with hmK
  set ρ : Measure (((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F) :=
    ((dx.prod ν).prod ν).prod mK with hρ
  have hψm : Measurable (word F) := measurable_word F
  have hwtm : Measurable (wt F) := measurable_wt F
  have hwt_top : ∀ p, wt F p < ⊤ := fun p => ENNReal.ofReal_lt_top

  have hc' : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μG = c * ∫⁻ p, φ (word F p) * wt F p ∂ρ := by
    intro φ hφ
    have hm : Measurable fun p => φ (word F p) * wt F p := (hφ.comp hψm).mul hwtm
    rw [hc φ hφ, hρ, lintegral_prod _ hm.aemeasurable,
      lintegral_prod _ (hm.lintegral_prod_right' (ν := mK)).aemeasurable,
      lintegral_prod _ ((hm.lintegral_prod_right' (ν := mK)).lintegral_prod_right' (ν := ν)).aemeasurable]
    rfl

  have hM : μG = c • (ρ.withDensity (wt F)).map (word F) := by
    ext E hE
    have h1 : μG E = ∫⁻ g, E.indicator (fun _ => (1 : ℝ≥0∞)) g ∂μG := (lintegral_indicator_one hE).symm
    rw [h1, hc' _ (measurable_const.indicator hE), Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hψm hE, withDensity_apply _ (hψm hE), ← lintegral_indicator (hψm hE)]
    congr 1
    refine lintegral_congr fun p => ?_
    by_cases h : word F p ∈ E
    · have h2 : p ∈ word F ⁻¹' E := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h2, one_mul]
    · have h2 : p ∉ word F ⁻¹' E := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h2, zero_mul]

  have hΨm : Measurable Ψ := hΨc.measurable
  have hΨi : Integrable Ψ μG := hΨc.integrable_of_hasCompactSupport hΨs
  have hΨi' : Integrable Ψ ((ρ.withDensity (wt F)).map (word F)) := by
    rw [hM] at hΨi
    exact (integrable_smul_measure hc0 hc_top).mp hΨi
  have hint' : Integrable (Ψ ∘ word F) (ρ.withDensity (wt F)) :=
    (integrable_map_measure hΨm.aestronglyMeasurable hψm.aemeasurable).mp hΨi'
  have hint : Integrable (fun p => ((wt F p).toReal : ℝ) • Ψ (word F p)) ρ := by
    have := (integrable_withDensity_iff_integrable_smul' hwtm (ae_of_all _ hwt_top)).mp hint'
    exact this

  rw [hM, integral_smul_measure, integral_map hψm.aemeasurable hΨm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hwtm (ae_of_all _ hwt_top)]
  change c.toReal • ∫ p, ((wt F p).toReal : ℝ) • Ψ (word F p) ∂ρ = _
  rw [hρ, integral_prod _ hint, integral_prod _ hint.integral_prod_left,
    integral_prod _ hint.integral_prod_left.integral_prod_left, Complex.real_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun u =>
    integral_congr_ae (ae_of_all _ fun t => integral_congr_ae (ae_of_all _ fun k => ?_))))
  show ((wt F (((x, u), t), k)).toReal : ℝ) • Ψ (word F (((x, u), t), k)) = _
  simp only [wt, word]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (ideleNorm_pos t).le), Complex.real_smul, mul_comm]

end Bochner

section Algebra

variable (F : Type) [Field F] [NumberField F]

theorem det_diagOne {A : Type*} [CommRing A] (t : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne t : GL (Fin 2) A) = t := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(t : A), 1]).det = t
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem ideleNorm_one : ideleNorm F 1 = 1 := by
  simp [ideleNorm]

theorem diagOne_mem_adelicBorel (t : (AdeleRing (𝓞 F) F)ˣ) : (diagOne t : AdelicGL2 (𝓞 F) F) ∈ adelicBorel (𝓞 F) F := by
  show (Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]) 1 0 = 0
  exact Matrix.diagonal_apply_ne _ (by decide)

theorem centralScalar_mul_diagOne_mem (z t : (AdeleRing (𝓞 F) F)ˣ) :
    centralScalar (𝓞 F) F z * diagOne t ∈ adelicBorel (𝓞 F) F :=
  Subgroup.mul_mem _ (centralScalar_mem_adelicBorel (𝓞 F) F z) (diagOne_mem_adelicBorel F t)

theorem coe_centralScalar_mul_diagOne (z t : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z * diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.diagonal fun i => (z : AdeleRing (𝓞 F) F) * ![(t : AdeleRing (𝓞 F) F), 1] i := by
  rw [Units.val_mul]
  show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) * Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1] = _
  rw [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]

theorem borelDiagFst_centralScalar_mul_diagOne (z t : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨centralScalar (𝓞 F) F z * diagOne t, centralScalar_mul_diagOne_mem F z t⟩ :
      ↥(adelicBorel (𝓞 F) F)) = z * t := by
  refine Units.ext ?_
  show ((centralScalar (𝓞 F) F z * diagOne t : AdelicGL2 (𝓞 F) F) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = z * t
  rw [coe_centralScalar_mul_diagOne, Matrix.diagonal_apply_eq]
  rfl

theorem borelDiagSnd_centralScalar_mul_diagOne (z t : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨centralScalar (𝓞 F) F z * diagOne t, centralScalar_mul_diagOne_mem F z t⟩ :
      ↥(adelicBorel (𝓞 F) F)) = z := by
  refine Units.ext ?_
  show ((centralScalar (𝓞 F) F z * diagOne t : AdelicGL2 (𝓞 F) F) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = z
  rw [coe_centralScalar_mul_diagOne, Matrix.diagonal_apply_eq]
  show (z : AdeleRing (𝓞 F) F) * 1 = z
  rw [mul_one]

theorem section_word {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (z t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ (centralScalar (𝓞 F) F z * diagOne t * g) = ((χ₁ (z * t) : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * φ g := by
  rw [hφ _ (centralScalar_mul_diagOne_mem F z t) g, borelDiagFst_centralScalar_mul_diagOne,
    borelDiagSnd_centralScalar_mul_diagOne]

theorem section_unipotent {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    φ (unipotentGL2 x * g) = φ g := by
  have hmem : (unipotentGL2 x : AdelicGL2 (𝓞 F) F) ∈ adelicBorel (𝓞 F) F := unipotentGL2_mem_borelSubgroup x
  rw [hφ _ hmem g]
  have h1 : borelDiagFst (⟨unipotentGL2 x, hmem⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
    refine Units.ext ?_
    show ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = 1
    rw [AutomorphicForm.unipotentGL2_coe]; rfl
  have h2 : borelDiagSnd (⟨unipotentGL2 x, hmem⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
    refine Units.ext ?_
    show ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = 1
    rw [AutomorphicForm.unipotentGL2_coe]; rfl
  rw [h1, h2, map_one, map_one, Units.val_one, one_mul, one_mul]

theorem det_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]
  simp only [mul_one, mul_zero, sub_zero, Units.val_one]

theorem ideleNorm_det_maximalCompact (k : adelicMaximalCompact F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) = 1 := by
  set f : adelicMaximalCompact F → ℝ := fun k =>
    ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) with hf
  have hfc : Continuous f :=
    (NumberField.TateGlobal.continuous_ideleNorm F).comp ((continuous_det F).comp continuous_subtype_val)
  have hmul : ∀ k k' : adelicMaximalCompact F, f (k * k') = f k * f k' := by
    intro k k'
    simp only [hf, Subgroup.coe_mul, map_mul, ideleNorm_mul]
  have hone : f 1 = 1 := by
    simp only [hf, OneMemClass.coe_one, map_one]
    exact ideleNorm_one F
  have hpow : ∀ (k : adelicMaximalCompact F) (n : ℕ), f (k ^ n) = f k ^ n := by
    intro k n
    induction n with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ n ih => rw [pow_succ, pow_succ, hmul, ih]
  have hinv : ∀ k : adelicMaximalCompact F, f k⁻¹ = (f k)⁻¹ := by
    intro k
    have h1 : f (k⁻¹ * k) = f k⁻¹ * f k := hmul _ _
    rw [inv_mul_cancel, hone] at h1
    have hpos : 0 < f k := ideleNorm_pos _
    field_simp
    linarith [h1]
  obtain ⟨M, hM⟩ := (isCompact_range hfc).bddAbove
  have hbound : ∀ k : adelicMaximalCompact F, f k ≤ M := fun k => hM ⟨k, rfl⟩
  have hle : ∀ k : adelicMaximalCompact F, f k ≤ 1 := by
    intro k
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
    exact (lt_irrefl M) (hn.trans_le (by rw [← hpow]; exact hbound _))
  have hge : 1 ≤ f k := by
    have h := hle k⁻¹
    rw [hinv] at h
    have hpos : 0 < f k := ideleNorm_pos _
    exact (inv_le_one₀ hpos).mp h
  exact le_antisymm (hle k) hge

theorem ideleNorm_det_word4 (x : AdeleRing (𝓞 F) F) (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det
      (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)))
      = ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * diagOne t)) := by
  rw [map_mul, map_mul, map_mul, det_unipotentGL2, one_mul, ideleNorm_mul, ideleNorm_det_maximalCompact, mul_one,
    map_mul]

end Algebra

end Ws31.Unfold

end

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

theorem main (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∃ c : ℝ, 0 < c ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (w : ℝ)
      (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
      (φf ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf p.1 p.2))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φf s (k : AdelicGL2 (𝓞 K) K) = φf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (t : ℝ),
    (∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
        conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      = (c : ℂ) * ∫ k, ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
          ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K) := by
  intro αm
  haveI := isHaarMeasure_gl K
  haveI := secondCountableTopology_gl K
  obtain ⟨cI, hc0, hc_top, hc⟩ := NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa K
  refine ⟨cI.toReal, ENNReal.toReal_pos hc0 hc_top, ?_⟩
  intro hαm μ ν hμc hνc w f₀ hf₀ hf₀c φf ψf hφf hψf hφfjc hψfjc hφflat hψflat t
  set s : ℂ := (t : ℂ) * Complex.I with hs

  set Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g => ψf s g *
      (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) with hΦ
  have hψsc : Continuous (ψf s) := hψfjc.comp (continuous_const.prodMk continuous_id)
  have hdetc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
      (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp ?_
    refine Continuous.rpow_const ((NumberField.TateGlobal.continuous_ideleNorm K).comp (continuous_det K)) ?_
    intro g; exact Or.inl (ideleNorm_pos _).ne'
  have hΦc : Continuous Φ := hψsc.mul hdetc

  have hinner : ∀ k : adelicMaximalCompact K,
      rightConv K Φ f₀ (k : AdelicGL2 (𝓞 K) K) =
        (cI.toReal : ℂ) * ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm s (u * t') : ℂˣ) : ℂ) * ((etaSnd ν αm hαm s u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K)
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) := by
    intro k

    set Ψ : AdelicGL2 (𝓞 K) K → ℂ := fun y => Φ y * f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ * y) with hΨ
    have hΨc : Continuous Ψ := hΦc.mul (hf₀.comp (continuous_const.mul continuous_id))
    have hΨs : HasCompactSupport Ψ := by
      have h1 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ * y)) := by
        have e : (fun y : AdelicGL2 (𝓞 K) K => f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ * y)) = f₀ ∘ (Homeomorph.mulLeft ((k : AdelicGL2 (𝓞 K) K)⁻¹)) := rfl
        rw [e]
        exact hf₀c.comp_homeomorph _
      exact h1.mul_left
    have hconv : rightConv K Φ f₀ (k : AdelicGL2 (𝓞 K) K) = ∫ y, Ψ y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
      rw [AutomorphicForm.rightConv_apply]
      have e : (fun y => Φ ((k : AdelicGL2 (𝓞 K) K) * y) * f₀ y) = fun y => Ψ ((k : AdelicGL2 (𝓞 K) K) * y) := by
        funext y
        simp only [hΨ, inv_mul_cancel_left]
      show (∫ y, Φ ((k : AdelicGL2 (𝓞 K) K) * y) * f₀ y ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = _
      rw [e, integral_mul_left_eq_self]
    rw [hconv, integral_eq_mul_iwasawa K cI hc0 hc_top hc Ψ hΨc hΨs]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun u =>
      integral_congr_ae (ae_of_all _ fun t' => integral_congr_ae (ae_of_all _ fun k' => ?_))))
    show Ψ (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K)) *
        (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) = _
    simp only [hΨ, hΦ]
    rw [ideleNorm_det_word4 K x u t' k']
    have hsec : ψf s (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))
        = ((etaFst μ αm hαm s (u * t') : ℂˣ) : ℂ) * ((etaSnd ν αm hαm s u : ℂˣ) : ℂ) * ψf 0 (k' : AdelicGL2 (𝓞 K) K) := by
      rw [mul_assoc, mul_assoc, section_unipotent K (hψf s), ← mul_assoc, section_word K (hψf s), hψflat]
    rw [hsec]
    ring

  have hout : ∀ k : adelicMaximalCompact K,
      rightConv K Φ f₀ (k : AdelicGL2 (𝓞 K) K) * conj (φf s (k : AdelicGL2 (𝓞 K) K)) =
        (cI.toReal : ℂ) * ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm s (u * t') : ℂˣ) : ℂ) * ((etaSnd ν αm hαm s u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) := by
    intro k
    rw [hinner k, hφflat, mul_assoc, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    beta_reduce
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun t' => ?_)
    beta_reduce
    rw [← integral_mul_const]
  show (∫ k, rightConv K Φ f₀ (k : AdelicGL2 (𝓞 K) K) * conj (φf s (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = _
  rw [integral_congr_ae (ae_of_all _ hout), integral_const_mul]

end Ws31.Unfold

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ c : ℝ, 0 < c ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (w : ℝ)
      (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
      (φf ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf p.1 p.2))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φf s (k : AdelicGL2 (𝓞 K) K) = φf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (t : ℝ),
    (∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
        conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      = (c : ℂ) * ∫ k, ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
          ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K) :=
  Ws31.Unfold.main K

end S_AutomorphicForm_exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat (solution)
