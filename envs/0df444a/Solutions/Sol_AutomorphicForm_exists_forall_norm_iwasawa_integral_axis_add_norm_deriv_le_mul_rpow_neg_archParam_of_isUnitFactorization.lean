-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b118a4e1-6121-5629-a6b6-e6798ccc0132

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
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Mathlib.MeasureTheory.Group.Integral
import Theorems.Thm_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
import Theorems.Thm_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped Classical

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm

namespace Ws31
namespace TorusDecay

variable (K : Type) [Field K] [NumberField K]

theorem exists_unit_extensionEmbedding_eq (v : InfinitePlace K) (r : ℝ) (hr : 0 < r) :
    ∃ x : (v.Completion)ˣ, InfinitePlace.Completion.extensionEmbedding v (x : v.Completion) = (r : ℂ) := by
  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  · obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hv r
    have hy0 : y ≠ 0 := by
      intro h; rw [h, map_zero] at hy; exact hr.ne' hy.symm
    refine ⟨Units.mk0 y hy0, ?_⟩
    rw [Units.val_mk0, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv y, hy]
  · obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hv (r : ℂ)
    have hy0 : y ≠ 0 := by
      intro h; rw [h, map_zero] at hy; exact (Complex.ofReal_ne_zero.mpr hr.ne') hy.symm
    exact ⟨Units.mk0 y hy0, by rw [Units.val_mk0, hy]⟩

theorem norm_eq_of_extensionEmbedding_eq (v : InfinitePlace K) (x : (v.Completion)ˣ) (r : ℝ) (hr : 0 < r)
    (hx : InfinitePlace.Completion.extensionEmbedding v (x : v.Completion) = (r : ℂ)) :
    ‖(x : v.Completion)‖ = r := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x : v.Completion)
  rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
  exact h.symm

theorem ideleNorm_archUnitHom (v : InfinitePlace K) (x : (v.Completion)ˣ) :
    ideleNorm K (archUnitHom v x) = ‖(x : v.Completion)‖ ^ v.mult := by
  have h2 : ((archUnitHom v x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ h2]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v)]
  have hv : ‖((archUnitHom v x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult = ‖(x : v.Completion)‖ ^ v.mult := by
    show ‖Function.update (1 : InfiniteAdeleRing K) v (x : v.Completion) v‖ ^ v.mult = _
    rw [Function.update_self]
  have hw : ∀ w ∈ (Finset.univ : Finset (InfinitePlace K)).erase v,
      ‖((archUnitHom v x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult = 1 := by
    intro w hw
    have hne : w ≠ v := (Finset.mem_erase.mp hw).1
    show ‖Function.update (1 : InfiniteAdeleRing K) v (x : v.Completion) w‖ ^ w.mult = 1
    rw [Function.update_of_ne hne]
    show ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one hw, hv, one_mul]

theorem etaFst_archUnitHom (v : InfinitePlace K) (x : (v.Completion)ˣ) (r : ℝ) (hr : 0 < r)
    (hx : InfinitePlace.Completion.extensionEmbedding v (x : v.Completion) = (r : ℂ))
    (αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hαm : ∀ z, 0 < ((αm z : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm K z)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ)
    (hτ : ((archLocalChar μ v x : ℂˣ) : ℂ) = ((ideleNorm K (archUnitHom v x) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
    (s : ℂ) :
    ((etaFst μ αm hαm s (archUnitHom v x) : ℂˣ) : ℂ)
      = ((r ^ v.mult : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I) * ((r ^ v.mult : ℝ) : ℂ) ^ (s + 1 / 2) := by
  have hN : ideleNorm K (archUnitHom v x) = r ^ v.mult := by
    rw [ideleNorm_archUnitHom, norm_eq_of_extensionEmbedding_eq K v x r hr hx]
  rw [etaFst_apply, Units.val_mul]
  have h1 : ((μ (archUnitHom v x) : ℂˣ) : ℂ) = ((r ^ v.mult : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I) := by
    rw [← hN, ← hτ]; rfl
  have h2 : ((cpowChar αm hαm (s + 1 / 2) (archUnitHom v x) : ℂˣ) : ℂ) = ((r ^ v.mult : ℝ) : ℂ) ^ (s + 1 / 2) := by
    show ((((αm (archUnitHom v x) : ℝˣ) : ℝ) : ℂ)) ^ (s + 1 / 2) = _
    rw [hαN, hN]
  rw [h1, h2]

end Ws31.TorusDecay

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

noncomputable section Majorant

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_mul_maximalCompact (W : Set (AdelicGL2 (𝓞 F) F)) (hW : IsCompact W) :
    IsCompact (Set.image2 (· * ·) W (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [← Set.image_prod]
  exact (hW.prod (isCompact_adelicMaximalCompact F)).image continuous_mul

theorem lintegral_iwasawa_indicator_lt_top (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc_top : c ≠ ∞)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
    (W : Set (AdelicGL2 (𝓞 F) F)) (hW : IsCompact W) :
    ∫⁻ x, ∫⁻ u, ∫⁻ t, W.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F) < ∞ := by
  haveI := isHaarMeasure_gl F
  haveI := secondCountableTopology_gl F
  set W₃ : Set (AdelicGL2 (𝓞 F) F) := Set.image2 (· * ·) W (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) with hW₃
  have hW₃c : IsCompact W₃ := isCompact_mul_maximalCompact F W hW
  have hW₃m : MeasurableSet W₃ := hW₃c.isClosed.measurableSet

  have hpt : ∀ b : AdelicGL2 (𝓞 F) F, W.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) b ≤
      ∫⁻ k, W₃.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (b * (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F) := by
    intro b
    by_cases hb : b ∈ W
    · have h1 : ∀ k : adelicMaximalCompact F, W₃.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (b * (k : AdelicGL2 (𝓞 F) F)) = 1 := by
        intro k
        rw [Set.indicator_of_mem (Set.mem_image2_of_mem hb k.2), Pi.one_apply]
      simp_rw [h1]
      rw [lintegral_const, measure_univ, mul_one, Set.indicator_of_mem hb, Pi.one_apply]
    · rw [Set.indicator_of_notMem hb]; exact zero_le'

  have hle : ∫⁻ x, ∫⁻ u, ∫⁻ t, W.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F)
      ≤ ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
          W₃.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞)
            (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F) := by
    refine lintegral_mono fun x => lintegral_mono fun u => lintegral_mono fun t => ?_
    have hm : Measurable fun k : adelicMaximalCompact F => W₃.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞)
        (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) :=
      (measurable_one.indicator hW₃m).comp ((continuous_const.mul continuous_subtype_val).measurable)
    rw [lintegral_mul_const _ hm]
    exact mul_le_mul_left (hpt _) _
  refine lt_of_le_of_lt hle ?_
  have hform := hc (W₃.indicator 1) (measurable_one.indicator hW₃m)
  rw [lintegral_indicator_one hW₃m] at hform

  have hfin : adelicGLHaar (Fin 2) (𝓞 F) F W₃ < ∞ := hW₃c.measure_lt_top
  rw [hform] at hfin
  exact lt_top_iff_ne_top.mpr fun h => by
    rw [h, ENNReal.mul_top hc0] at hfin
    exact lt_irrefl _ hfin

end Majorant

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Scaling

variable (F : Type) [Field F] [NumberField F]

abbrev Pspace : Type :=
  ((((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F

def πP : Measure (Pspace F) :=
  ((((maximalCompactHaar F).prod (adelicAddHaar (𝓞 F) F)).prod (NumberField.Idele.idelicHaar F)).prod
    (NumberField.Idele.idelicHaar F)).prod (maximalCompactHaar F)

def scaleT (δ : (AdeleRing (𝓞 F) F)ˣ) (p : Pspace F) : Pspace F :=
  ((p.1.1, δ * p.1.2), p.2)

def scaleU (δ : (AdeleRing (𝓞 F) F)ˣ) (p : Pspace F) : Pspace F :=
  ((((p.1.1.1.1, p.1.1.1.2), δ * p.1.1.2), δ⁻¹ * p.1.2), p.2)

theorem measurePreserving_scaleT (δ : (AdeleRing (𝓞 F) F)ˣ) :
    MeasurePreserving (scaleT F δ) (πP F) (πP F) := by
  haveI := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F
  haveI := secondCountableTopology_adele F
  haveI := sigmaFinite_adelicAddHaar F
  unfold πP scaleT
  have h1 : MeasurePreserving (fun q : (((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) ×
      (AdeleRing (𝓞 F) F)ˣ => (q.1, δ * q.2))
      ((((maximalCompactHaar F).prod (adelicAddHaar (𝓞 F) F)).prod (NumberField.Idele.idelicHaar F)).prod
        (NumberField.Idele.idelicHaar F))
      ((((maximalCompactHaar F).prod (adelicAddHaar (𝓞 F) F)).prod (NumberField.Idele.idelicHaar F)).prod
        (NumberField.Idele.idelicHaar F)) :=
    (MeasurePreserving.id _).prod (measurePreserving_mul_left (NumberField.Idele.idelicHaar F) δ)
  exact h1.prod (MeasurePreserving.id _)

theorem measurePreserving_scaleU (δ : (AdeleRing (𝓞 F) F)ˣ) :
    MeasurePreserving (scaleU F δ) (πP F) (πP F) := by
  haveI := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F
  haveI := secondCountableTopology_adele F
  haveI := sigmaFinite_adelicAddHaar F
  unfold πP scaleU
  have h0 : MeasurePreserving (fun q : ((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ =>
      ((q.1.1, q.1.2), δ * q.2))
      (((maximalCompactHaar F).prod (adelicAddHaar (𝓞 F) F)).prod (NumberField.Idele.idelicHaar F))
      (((maximalCompactHaar F).prod (adelicAddHaar (𝓞 F) F)).prod (NumberField.Idele.idelicHaar F)) := by
    have := (MeasurePreserving.id ((maximalCompactHaar F).prod (adelicAddHaar (𝓞 F) F))).prod
      (measurePreserving_mul_left (NumberField.Idele.idelicHaar F) δ)
    exact this
  have h1 := h0.prod (measurePreserving_mul_left (NumberField.Idele.idelicHaar F) δ⁻¹)
  exact h1.prod (MeasurePreserving.id _)

end Scaling

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Height

variable (F : Type) [Field F] [NumberField F]

theorem adelicHeight_borel_mul {b : AdelicGL2 (𝓞 F) F} (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    NumberField.AdelicHeight.adelicHeight F (b * g) =
      ideleNorm F (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) *
        (ideleNorm F (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))))⁻¹ *
          NumberField.AdelicHeight.adelicHeight F g := by
  obtain ⟨hpos, -, hsec⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have h := hsec hpos (1 / 2) b hb g
  have hhalf : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  simp only [hhalf, Complex.cpow_one, etaFst_apply, etaSnd_apply, cpowChar_apply_val,
    Complex.cpow_neg_one, MonoidHom.one_apply, one_mul] at h
  have e1 : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
      ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits x :
        ℝˣ) : ℝ) = ideleNorm F x := fun x => rfl
  rw [e1, e1] at h
  have hg0 : ((ideleNorm F (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ideleNorm_pos _).ne'
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

theorem adelicHeight_maximalCompact (k : adelicMaximalCompact F) :
    NumberField.AdelicHeight.adelicHeight F (k : AdelicGL2 (𝓞 F) F) = 1 := by
  rw [NumberField.AdelicHeight.adelicHeight_eq_archHeight_of_mem k.2.1]
  have h := AutomorphicForm.WindowedSiegel.archHeight_mul_rowIsometry F 1
    (k := glArch (𝓞 F) F (k : AdelicGL2 (𝓞 F) F)) k.2.2
  rwa [one_mul, AutomorphicForm.WindowedSiegel.archHeight_one] at h

theorem adelicHeight_word4 (x : AdeleRing (𝓞 F) F) (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    NumberField.AdelicHeight.adelicHeight F
      (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) = ideleNorm F t := by
  have hmem : (unipotentGL2 x : AdelicGL2 (𝓞 F) F) ∈ adelicBorel (𝓞 F) F := unipotentGL2_mem_borelSubgroup x
  have h1 : borelDiagFst (⟨unipotentGL2 x, hmem⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
    refine Units.ext ?_
    show ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = 1
    rw [AutomorphicForm.unipotentGL2_coe]; rfl
  have h2 : borelDiagSnd (⟨unipotentGL2 x, hmem⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
    refine Units.ext ?_
    show ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = 1
    rw [AutomorphicForm.unipotentGL2_coe]; rfl
  rw [mul_assoc, mul_assoc, adelicHeight_borel_mul F hmem, h1, h2, ideleNorm_one, inv_one, one_mul, one_mul, ← mul_assoc,
    adelicHeight_borel_mul F (centralScalar_mul_diagOne_mem F z t), borelDiagFst_centralScalar_mul_diagOne,
    borelDiagSnd_centralScalar_mul_diagOne, adelicHeight_maximalCompact, ideleNorm_mul, mul_one]
  have hz : ideleNorm F z ≠ 0 := (ideleNorm_pos z).ne'
  field_simp

end Height

noncomputable section Integrand

variable (F : Type) [Field F] [NumberField F]

def word4 (p : Pspace F) : AdelicGL2 (𝓞 F) F :=
  unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F)

theorem continuous_word4 : Continuous (word4 F) := by
  unfold word4
  exact (((AutomorphicForm.continuous_unipotentGL2.comp continuous_fst.fst.fst.snd).mul
    ((continuous_centralScalar F).comp continuous_fst.fst.snd)).mul
    ((continuous_diagOne F).comp continuous_fst.snd)).mul (continuous_subtype_val.comp continuous_snd)

def Iint (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F) : ℂ :=
  ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (p.1.1.2 * p.1.2) : ℂˣ) : ℂ) *
  ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) p.1.1.2 : ℂˣ) : ℂ) *
  (((NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) : ℝ) : ℂ) *
  (((NumberField.TateGlobal.ideleNorm F p.1.2)⁻¹ : ℝ) : ℂ) *
  f₀ ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * word4 F p) * ψ0 (p.2 : AdelicGL2 (𝓞 F) F) * conj (φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F))

theorem norm_eta_pair (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (t : ℝ) (u t' : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
      ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ)‖ = (ideleNorm F t') ^ (1 / 2 : ℝ) := by
  rw [etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul, norm_mul, norm_mul, norm_mul, hμ, hν, one_mul, one_mul,
    cpowChar_apply_val, cpowChar_apply_val, hαN, hαN, Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos _), ideleNorm_mul]
  have hre1 : ((t : ℂ) * Complex.I + 1 / 2).re = 1 / 2 := by simp
  have hre2 : (-((t : ℂ) * Complex.I + 1 / 2)).re = -(1 / 2) := by simp
  rw [hre1, hre2, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, Real.rpow_neg (ideleNorm_pos _).le]
  have hu : (ideleNorm F u) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (ideleNorm_pos _) _).ne'
  field_simp

end Integrand

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Bound

variable (F : Type) [Field F] [NumberField F]

def Wset (f₀ : AdelicGL2 (𝓞 F) F → ℂ) : Set (AdelicGL2 (𝓞 F) F) :=
  (fun q : (adelicMaximalCompact F) × AdelicGL2 (𝓞 F) F => (q.1 : AdelicGL2 (𝓞 F) F) * q.2) '' (Set.univ ×ˢ tsupport f₀)

theorem isCompact_Wset (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀c : HasCompactSupport f₀) : IsCompact (Wset F f₀) :=
  (isCompact_univ.prod hf₀c).image (by fun_prop)

theorem mem_Wset_of_ne_zero (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (k : adelicMaximalCompact F) (y : AdelicGL2 (𝓞 F) F)
    (h : f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * y) ≠ 0) : y ∈ Wset F f₀ := by
  refine ⟨(k, (k : AdelicGL2 (𝓞 F) F)⁻¹ * y), ⟨Set.mem_univ _, subset_tsupport _ h⟩, ?_⟩
  show (k : AdelicGL2 (𝓞 F) F) * ((k : AdelicGL2 (𝓞 F) F)⁻¹ * y) = y
  rw [mul_inv_cancel_left]

theorem exists_bound_Iint (w : ℝ) (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
        (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
        (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
        (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F),
      ‖Iint F αm hαm μ ν w f₀ φ0 ψ0 t p‖ ≤
        C₀ * (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) * (ideleNorm F p.1.2)⁻¹ *
          ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖ := by

  set b : AdelicGL2 (𝓞 F) F → ℝ := fun y => (NumberField.AdelicHeight.adelicHeight F y) ^ (1 / 2 : ℝ) *
    (ideleNorm F (Matrix.GeneralLinearGroup.det y)) ^ (w / 2) with hb
  have hbc : Continuous b := by
    refine Continuous.mul ?_ ?_
    · exact (NumberField.AdelicHeight.continuous_adelicHeight F).rpow_const fun y => Or.inr (by norm_num)
    · refine ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_det F)).rpow_const fun y => ?_
      exact Or.inl (ideleNorm_pos _).ne'
  obtain ⟨M, hM⟩ := (isCompact_Wset F f₀ hf₀c).exists_bound_of_continuousOn hbc.continuousOn
  obtain ⟨B, hB⟩ := hf₀.bounded_above_of_compact_support hf₀c
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨max M 0 * max B 0, mul_nonneg hM0 hB0, ?_⟩
  intro αm hαm hαN μ ν hμ hν φ0 ψ0 t p
  obtain ⟨⟨⟨⟨k, x⟩, u⟩, t'⟩, k'⟩ := p
  by_cases hW : word4 F ((((k, x), u), t'), k') ∈ Wset F f₀
  · rw [Set.indicator_of_mem hW, mul_one]
    simp only [Iint]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_eta_pair F αm hαm hαN μ ν hμ hν,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (ideleNorm_pos _).le _), abs_of_pos (inv_pos.mpr (ideleNorm_pos _))]
    have hbw : (ideleNorm F t') ^ (1 / 2 : ℝ) *
        (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u * diagOne t'))) ^ (w / 2)
        = b (word4 F ((((k, x), u), t'), k')) := by
      simp only [hb, word4]
      rw [adelicHeight_word4, ideleNorm_det_word4]
    have h1 : (ideleNorm F t') ^ (1 / 2 : ℝ) *
        (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u * diagOne t'))) ^ (w / 2) ≤ max M 0 := by
      rw [hbw]; exact (le_of_abs_le (hM _ hW)).trans (le_max_left _ _)
    have h2 : ‖f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * word4 F ((((k, x), u), t'), k'))‖ ≤ max B 0 := (hB _).trans (le_max_left _ _)
    have hpos : 0 ≤ (ideleNorm F t')⁻¹ := (inv_pos.mpr (ideleNorm_pos _)).le

    have eq1 : (ideleNorm F t') ^ (1 / 2 : ℝ) *
          (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u * diagOne t'))) ^ (w / 2) *
          (ideleNorm F t')⁻¹ * ‖f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * word4 F ((((k, x), u), t'), k'))‖ *
          ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖
        = ((ideleNorm F t') ^ (1 / 2 : ℝ) *
            (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u * diagOne t'))) ^ (w / 2) *
            ‖f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * word4 F ((((k, x), u), t'), k'))‖) *
          ((ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖) := by ring
    have eq2 : max M 0 * max B 0 * (ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖
        = (max M 0 * max B 0) * ((ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖) := by ring
    rw [eq1, eq2]
    have hrest : 0 ≤ (ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ := by positivity
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hM0) le_rfl hrest (mul_nonneg hM0 hB0)
  · have h0 : f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * word4 F ((((k, x), u), t'), k')) = 0 := by
      by_contra h; exact hW (mem_Wset_of_ne_zero F f₀ k _ h)
    simp only [Iint, h0, mul_zero, zero_mul, norm_zero]
    rw [Set.indicator_of_notMem hW]
    simp

end Bound

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Integrability

variable (F : Type) [Field F] [NumberField F]

theorem continuous_cpowChar (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z) (s : ℂ) :
    Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((cpowChar αm hαm s z : ℂˣ) : ℂ) := by
  have e : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((cpowChar αm hαm s z : ℂˣ) : ℂ)) =
      fun z => (((ideleNorm F z : ℝ) : ℂ)) ^ s := by
    funext z; rw [cpowChar_apply_val, hαN]
  rw [e]
  refine Continuous.cpow (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F))
    continuous_const fun z => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (ideleNorm_pos _)

theorem continuous_etaFst (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z) (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ)) (s : ℂ) :
    Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((etaFst μ αm hαm s z : ℂˣ) : ℂ) := by
  have e : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((etaFst μ αm hαm s z : ℂˣ) : ℂ)) =
      fun z => ((μ z : ℂˣ) : ℂ) * ((cpowChar αm hαm (s + 1 / 2) z : ℂˣ) : ℂ) := by
    funext z; rw [etaFst_apply, Units.val_mul]
  rw [e]; exact hμc.mul (continuous_cpowChar F αm hαm hαN _)

theorem continuous_etaSnd (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z) (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ)) (s : ℂ) :
    Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((etaSnd ν αm hαm s z : ℂˣ) : ℂ) := by
  have e : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((etaSnd ν αm hαm s z : ℂˣ) : ℂ)) =
      fun z => ((ν z : ℂˣ) : ℂ) * ((cpowChar αm hαm (-(s + 1 / 2)) z : ℂˣ) : ℂ) := by
    funext z; rw [etaSnd_apply, Units.val_mul]
  rw [e]; exact hνc.mul (continuous_cpowChar F αm hαm hαN _)

theorem continuous_Iint (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
    (hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ))
    (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0)
    (t : ℝ) : Continuous (Iint F αm hαm μ ν w f₀ φ0 ψ0 t) := by
  unfold Iint
  have hu : Continuous fun p : Pspace F => p.1.1.2 := continuous_fst.fst.snd
  have ht' : Continuous fun p : Pspace F => p.1.2 := continuous_fst.snd
  refine ((((((continuous_etaFst F αm hαm hαN μ hμc _).comp (hu.mul ht')).mul
    ((continuous_etaSnd F αm hαm hαN ν hνc _).comp hu)).mul ?_).mul ?_).mul ?_).mul ?_ |>.mul ?_
  · refine Complex.continuous_ofReal.comp ?_
    refine Continuous.rpow_const ((NumberField.TateGlobal.continuous_ideleNorm F).comp
      ((continuous_det F).comp (((continuous_centralScalar F).comp hu).mul ((continuous_diagOne F).comp ht')))) ?_
    intro p; exact Or.inl (ideleNorm_pos _).ne'
  · exact Complex.continuous_ofReal.comp (((NumberField.TateGlobal.continuous_ideleNorm F).comp ht').inv₀
      fun p => (ideleNorm_pos _).ne')
  · exact hf₀.comp (((continuous_subtype_val.comp continuous_fst.fst.fst.fst).inv).mul (continuous_word4 F))
  · exact hψ0.comp (continuous_subtype_val.comp continuous_snd)
  · exact Complex.continuous_conj.comp (hφ0.comp (continuous_subtype_val.comp continuous_fst.fst.fst.fst))

end Integrability

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section IntegrableP

variable (F : Type) [Field F] [NumberField F]

theorem lintegral_piP_mid (g : (AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ p, g ((p.1.1.1.2, p.1.1.2), p.1.2) ∂(πP F) =
      ∫⁻ x, ∫⁻ u, ∫⁻ t, g ((x, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F
  haveI := secondCountableTopology_adele F
  haveI := sigmaFinite_adelicAddHaar F

  have m3 : Measurable fun q : (((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) ×
      (AdeleRing (𝓞 F) F)ˣ => g ((q.1.1.2, q.1.2), q.2) :=
    hg.comp (by fun_prop)
  have m4 : Measurable fun p : Pspace F => g ((p.1.1.1.2, p.1.1.2), p.1.2) := m3.comp measurable_fst
  unfold πP
  rw [lintegral_prod _ m4.aemeasurable]
  have e1 : (fun q : (((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ k' : adelicMaximalCompact F, g ((q.1.1.2, q.1.2), q.2) ∂(maximalCompactHaar F)) =
      fun q => g ((q.1.1.2, q.1.2), q.2) := by
    funext q; rw [lintegral_const, measure_univ, mul_one]
  rw [e1, lintegral_prod _ m3.aemeasurable]

  have m2 : Measurable fun q : ((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ t, g ((q.1.2, q.2), t) ∂(NumberField.Idele.idelicHaar F) := by
    have := m3.lintegral_prod_right' (ν := NumberField.Idele.idelicHaar F)
    exact this
  rw [lintegral_prod _ m2.aemeasurable]
  have m1 : Measurable fun q : (adelicMaximalCompact F) × AdeleRing (𝓞 F) F =>
      ∫⁻ u, ∫⁻ t, g ((q.2, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
    have := m2.lintegral_prod_right' (ν := NumberField.Idele.idelicHaar F)
    exact this
  rw [lintegral_prod _ m1.aemeasurable]

  have m0 : Measurable fun x : AdeleRing (𝓞 F) F =>
      ∫⁻ u, ∫⁻ t, g ((x, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
    have := m1.comp (measurable_const (a := (1 : adelicMaximalCompact F)) |>.prodMk measurable_id)
    exact this
  have e2 : (fun k : adelicMaximalCompact F => ∫⁻ x, ∫⁻ u, ∫⁻ t, g (((k, x).2, u), t)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F)) =
      fun _ => ∫⁻ x, ∫⁻ u, ∫⁻ t, g ((x, u), t)
        ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F) := rfl
  rw [e2, lintegral_const, measure_univ, mul_one]

end IntegrableP

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section IntegrableI

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

def WK (f₀ : AdelicGL2 (𝓞 F) F → ℂ) : Set (AdelicGL2 (𝓞 F) F) :=
  Set.image2 (· * ·) (Wset F f₀) (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F))

theorem indicator_W_le_indicator_WK (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (p : Pspace F) :
    (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) ≤
      (WK F f₀).indicator (fun _ => (1 : ℝ))
        (unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2) := by
  by_cases h : word4 F p ∈ Wset F f₀
  · have hmem : unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2 ∈ WK F f₀ := by
      refine ⟨word4 F p, h, ((p.2)⁻¹ : adelicMaximalCompact F), ((p.2)⁻¹).2, ?_⟩
      show word4 F p * (((p.2)⁻¹ : adelicMaximalCompact F) : AdelicGL2 (𝓞 F) F) = _
      simp only [word4, Subgroup.coe_inv, mul_inv_cancel_right]
    rw [Set.indicator_of_mem h, Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem h]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem integrable_majorant (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc_top : c ≠ ∞)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
    (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀)
    (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    Integrable (fun p : Pspace F =>
      C₀ * (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) * (ideleNorm F p.1.2)⁻¹ *
        ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖) (πP F) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _

  obtain ⟨Cφ, hCφ⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hφ0.comp continuous_subtype_val).continuousOn (s := (Set.univ : Set (adelicMaximalCompact F))))
  obtain ⟨Cψ, hCψ⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hψ0.comp continuous_subtype_val).continuousOn (s := (Set.univ : Set (adelicMaximalCompact F))))
  have hCφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 1 (Set.mem_univ _))
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 1 (Set.mem_univ _))

  have hWc : IsClosed (Wset F f₀) := (isCompact_Wset F f₀ hf₀c).isClosed
  have hmeas : Measurable fun p : Pspace F =>
      C₀ * (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) * (ideleNorm F p.1.2)⁻¹ *
        ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖ := by
    refine (((measurable_const.mul ((measurable_const.indicator hWc.measurableSet).comp
      (continuous_word4 F).measurable)).mul ?_).mul ?_).mul ?_
    · exact ((NumberField.TateGlobal.continuous_ideleNorm F).measurable.comp (by fun_prop)).inv
    · exact (hψ0.comp (continuous_subtype_val.comp continuous_snd)).measurable.norm
    · exact (hφ0.comp (continuous_subtype_val.comp continuous_fst.fst.fst.fst)).measurable.norm
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩

  have hWKc : IsCompact (WK F f₀) := isCompact_mul_maximalCompact F _ (isCompact_Wset F f₀ hf₀c)
  set g : (AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞ := fun q =>
    (WK F f₀).indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (unipotentGL2 q.1.1 * centralScalar (𝓞 F) F q.1.2 * diagOne q.2) *
      ENNReal.ofReal ((ideleNorm F q.2)⁻¹) with hg
  have hgm : Measurable g := by
    refine ((measurable_one.indicator hWKc.isClosed.measurableSet).comp ?_).mul
      (ENNReal.measurable_ofReal.comp (((NumberField.TateGlobal.continuous_ideleNorm F).measurable.comp measurable_snd).inv))
    exact (((AutomorphicForm.continuous_unipotentGL2.comp continuous_fst.fst).mul
      ((continuous_centralScalar F).comp continuous_fst.snd)).mul ((continuous_diagOne F).comp continuous_snd)).measurable
  have hpt : ∀ p : Pspace F,
      ‖C₀ * (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) * (ideleNorm F p.1.2)⁻¹ *
        ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖‖ₑ
        ≤ ENNReal.ofReal (C₀ * Cψ * Cφ) * g ((p.1.1.1.2, p.1.1.2), p.1.2) := by
    intro p
    rw [Real.enorm_eq_ofReal (by
      have := Set.indicator_nonneg (s := Wset F f₀) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) (word4 F p)
      have := (inv_pos.mpr (ideleNorm_pos p.1.2)).le
      positivity)]
    simp only [hg]
    by_cases hW : unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2 ∈ WK F f₀
    · rw [Set.indicator_of_mem hW, Pi.one_apply, one_mul, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) ≤ 1 :=
        Set.indicator_le_self' (fun _ _ => zero_le_one) _ |>.trans le_rfl
      have h2 := hCψ p.2 (Set.mem_univ _)
      have h3 := hCφ p.1.1.1.1 (Set.mem_univ _)
      have hi := (inv_pos.mpr (ideleNorm_pos p.1.2)).le
      have h0 := Set.indicator_nonneg (s := Wset F f₀) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) (word4 F p)
      calc C₀ * (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) * (ideleNorm F p.1.2)⁻¹ *
            ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖
          ≤ C₀ * 1 * (ideleNorm F p.1.2)⁻¹ * Cψ * Cφ := by
              gcongr <;> first | exact h1 | exact h2 | exact h3
        _ = C₀ * Cψ * Cφ * (ideleNorm F p.1.2)⁻¹ := by ring
    · have h0 : (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) = 0 := by
        have := indicator_W_le_indicator_WK F f₀ p
        rw [Set.indicator_of_notMem hW] at this
        exact le_antisymm this (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      rw [h0]; simp
  calc ∫⁻ p, ‖C₀ * (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) * (ideleNorm F p.1.2)⁻¹ *
        ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖‖ₑ ∂(πP F)
      ≤ ∫⁻ p, ENNReal.ofReal (C₀ * Cψ * Cφ) * g ((p.1.1.1.2, p.1.1.2), p.1.2) ∂(πP F) := lintegral_mono hpt
    _ = ENNReal.ofReal (C₀ * Cψ * Cφ) * ∫⁻ p, g ((p.1.1.1.2, p.1.1.2), p.1.2) ∂(πP F) := by
        have hm' : Measurable (fun p : Pspace F => g ((p.1.1.1.2, p.1.1.2), p.1.2)) := hgm.comp (by fun_prop)
        rw [lintegral_const_mul _ hm']
    _ < ∞ := by
        rw [lintegral_piP_mid F g hgm]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        simp only [hg]
        exact lintegral_iwasawa_indicator_lt_top F c hc0 hc_top hc _ hWKc

end IntegrableI

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section ProductForm

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

theorem integrable_Iint (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc_top : c ≠ ∞)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
    (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
    (hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ))
    (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀)
    (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0) (t : ℝ) :
    Integrable (Iint F αm hαm μ ν w f₀ φ0 ψ0 t) (πP F) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨C₀, hC₀, hbound⟩ := exists_bound_Iint F w f₀ hf₀ hf₀c
  refine (integrable_majorant F c hc0 hc_top hc f₀ hf₀ hf₀c φ0 ψ0 hφ0 hψ0 C₀ hC₀).mono'
    (continuous_Iint F αm hαm hαN μ ν hμc hνc w f₀ φ0 ψ0 hf₀ hφ0 hψ0 t).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  have h := hbound αm hαm hαN μ ν hμ hν φ0 ψ0 t p
  calc ‖Iint F αm hαm μ ν w f₀ φ0 ψ0 t p‖ ≤ _ := h
    _ = _ := by ring

theorem nested_eq_integral_prod (G : Pspace F → ℂ) (hG : Integrable G (πP F)) :
    ∫ k, ∫ x, ∫ u, ∫ t', ∫ k', G ((((k, x), u), t'), k')
      ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      ∂(adelicAddHaar (𝓞 F) F) ∂(maximalCompactHaar F) = ∫ p, G p ∂(πP F) := by
  haveI := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F
  haveI := secondCountableTopology_adele F
  haveI := sigmaFinite_adelicAddHaar F
  unfold πP at hG ⊢
  rw [integral_prod _ hG, integral_prod _ hG.integral_prod_left, integral_prod _ hG.integral_prod_left.integral_prod_left,
    integral_prod _ hG.integral_prod_left.integral_prod_left.integral_prod_left]

end ProductForm

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section PosUnits

variable (F : Type) [Field F] [NumberField F]

theorem ofReal_exp_mem_range (v : InfinitePlace F) (s : ℝ) :
    ((Real.exp s : ℝ) : ℂ) ∈ Set.range (InfinitePlace.Completion.extensionEmbedding v) := by
  obtain ⟨x, hx⟩ := Ws31.TorusDecay.exists_unit_extensionEmbedding_eq F v (Real.exp s) (Real.exp_pos s)
  exact ⟨(x : v.Completion), hx⟩

def embHomeo (v : InfinitePlace F) : v.Completion ≃ₜ Set.range (InfinitePlace.Completion.extensionEmbedding v) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.toHomeomorph

def posElt (v : InfinitePlace F) (s : ℝ) : v.Completion :=
  (embHomeo F v).symm ⟨((Real.exp s : ℝ) : ℂ), ofReal_exp_mem_range F v s⟩

theorem extensionEmbedding_posElt (v : InfinitePlace F) (s : ℝ) :
    InfinitePlace.Completion.extensionEmbedding v (posElt F v s) = ((Real.exp s : ℝ) : ℂ) := by
  have h := (embHomeo F v).apply_symm_apply ⟨((Real.exp s : ℝ) : ℂ), ofReal_exp_mem_range F v s⟩
  have h2 := congrArg Subtype.val h
  exact h2

theorem continuous_posElt (v : InfinitePlace F) : Continuous (posElt F v) := by
  unfold posElt
  refine (embHomeo F v).symm.continuous.comp ?_
  exact Continuous.subtype_mk (Complex.continuous_ofReal.comp Real.continuous_exp) _

theorem posElt_add (v : InfinitePlace F) (s s' : ℝ) : posElt F v (s + s') = posElt F v s * posElt F v s' := by
  apply (InfinitePlace.Completion.isometry_extensionEmbedding v).injective
  rw [map_mul, extensionEmbedding_posElt, extensionEmbedding_posElt, extensionEmbedding_posElt, Real.exp_add,
    Complex.ofReal_mul]

theorem posElt_zero (v : InfinitePlace F) : posElt F v 0 = 1 := by
  apply (InfinitePlace.Completion.isometry_extensionEmbedding v).injective
  rw [extensionEmbedding_posElt, map_one, Real.exp_zero, Complex.ofReal_one]

theorem posElt_ne_zero (v : InfinitePlace F) (s : ℝ) : posElt F v s ≠ 0 := by
  intro h
  have := extensionEmbedding_posElt F v s
  rw [h, map_zero] at this
  exact (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne') this.symm

def posUnit (v : InfinitePlace F) (s : ℝ) : (v.Completion)ˣ := Units.mk0 (posElt F v s) (posElt_ne_zero F v s)

theorem posUnit_inv_eq (v : InfinitePlace F) (s : ℝ) : (posUnit F v s)⁻¹ = posUnit F v (-s) := by
  rw [← mul_eq_one_iff_inv_eq, ← Units.val_inj, Units.val_mul]
  show posElt F v s * posElt F v (-s) = 1
  rw [← posElt_add, add_neg_cancel, posElt_zero]

theorem continuous_posUnit (v : InfinitePlace F) : Continuous (posUnit F v) := by
  refine Units.continuous_iff.mpr ⟨continuous_posElt F v, ?_⟩
  have e : (fun s => ((posUnit F v s)⁻¹ : (v.Completion)ˣ).val) = fun s => posElt F v (-s) := by
    funext s; rw [posUnit_inv_eq]; rfl
  rw [e]
  exact (continuous_posElt F v).comp continuous_neg

theorem continuous_archUnitHom (v : InfinitePlace F) :
    Continuous (archUnitHom (F := F) v : (v.Completion)ˣ → (AdeleRing (𝓞 F) F)ˣ) := by
  have hupd : Continuous fun x : v.Completion => (Function.update (1 : InfiniteAdeleRing F) v x, (1 : FiniteAdeleRing (𝓞 F) F)) :=
    (continuous_const.update v continuous_id).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hupd.comp Units.continuous_val
  · have e : (fun x : (v.Completion)ˣ => ((archUnitHom v x)⁻¹ : (AdeleRing (𝓞 F) F)ˣ).val) =
        fun x => (Function.update (1 : InfiniteAdeleRing F) v ((x⁻¹ : (v.Completion)ˣ) : v.Completion), (1 : FiniteAdeleRing (𝓞 F) F)) := by
      funext x; rw [← map_inv]; rfl
    rw [e]
    exact hupd.comp Units.continuous_coe_inv

def delta (v : InfinitePlace F) (s : ℝ) : (AdeleRing (𝓞 F) F)ˣ := archUnitHom v (posUnit F v s)

theorem continuous_delta (v : InfinitePlace F) : Continuous (delta F v) :=
  (continuous_archUnitHom F v).comp (continuous_posUnit F v)

theorem ideleNorm_delta (v : InfinitePlace F) (s : ℝ) : ideleNorm F (delta F v s) = Real.exp (v.mult * s) := by
  unfold delta
  rw [Ws31.TorusDecay.ideleNorm_archUnitHom F v]
  have h : ‖((posUnit F v s : (v.Completion)ˣ) : v.Completion)‖ = Real.exp s :=
    Ws31.TorusDecay.norm_eq_of_extensionEmbedding_eq F v (posUnit F v s) (Real.exp s) (Real.exp_pos s)
      (extensionEmbedding_posElt F v s)
  rw [h, ← Real.exp_nat_mul]

end PosUnits

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Averaging

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

theorem continuous_scaleT_delta (v : InfinitePlace F) :
    Continuous fun q : ℝ × Pspace F => scaleT F (delta F v q.1) q.2 := by
  unfold scaleT
  refine ((continuous_fst.comp continuous_snd).fst.prodMk ?_).prodMk (continuous_snd.comp continuous_snd)
  exact ((continuous_delta F v).comp continuous_fst).mul (continuous_fst.comp continuous_snd).snd

theorem integral_comp_scaleT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : (AdeleRing (𝓞 F) F)ˣ) (G : Pspace F → E) (hGm : AEStronglyMeasurable G (πP F)) :
    ∫ p, G (scaleT F δ p) ∂(πP F) = ∫ p, G p ∂(πP F) := by
  have h := measurePreserving_scaleT F δ
  have hG' : AEStronglyMeasurable G (Measure.map (scaleT F δ) (πP F)) := by rw [h.map_eq]; exact hGm
  have e := integral_map h.measurable.aemeasurable hG'
  rw [h.map_eq] at e
  exact e.symm

theorem integrable_comp_scaleT (δ : (AdeleRing (𝓞 F) F)ˣ) (G : Pspace F → ℂ) (hGm : AEStronglyMeasurable G (πP F))
    (hG : Integrable G (πP F)) : Integrable (fun p => G (scaleT F δ p)) (πP F) := by
  have h := measurePreserving_scaleT F δ
  have hG' : Integrable G (Measure.map (scaleT F δ) (πP F)) := by rw [h.map_eq]; exact hG
  exact (integrable_map_measure hG'.aestronglyMeasurable h.measurable.aemeasurable).mp hG'

theorem integral_eq_integral_average (v : InfinitePlace F) (ρ : ℝ → ℝ) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ1 : ∫ s, ρ s = 1)
    (G : Pspace F → ℂ) (hGc : Continuous G) (hG : Integrable G (πP F)) :
    ∫ p, G p ∂(πP F) = ∫ p, (∫ s : ℝ, (ρ s : ℂ) * G (scaleT F (delta F v s) p)) ∂(πP F) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := sigmaFinite_idelicHaar F
  haveI := sigmaFinite_adelicAddHaar F
  haveI : SigmaFinite (πP F) := by unfold πP; infer_instance
  have hGm : AEStronglyMeasurable G (πP F) := hG.aestronglyMeasurable

  set Φ : ℝ × Pspace F → ℂ := Function.uncurry fun (s : ℝ) (p : Pspace F) => (ρ s : ℂ) * G (scaleT F (delta F v s) p) with hΦ
  have hΦc : Continuous Φ := by
    show Continuous fun q : ℝ × Pspace F => (ρ q.1 : ℂ) * G (scaleT F (delta F v q.1) q.2)
    exact (Complex.continuous_ofReal.comp (hρc.comp continuous_fst)).mul (hGc.comp (continuous_scaleT_delta F v))
  have hΦm : AEStronglyMeasurable Φ ((volume : Measure ℝ).prod (πP F)) := hΦc.aestronglyMeasurable

  have hnorm : ∀ s : ℝ, ∫ p, ‖Φ (s, p)‖ ∂(πP F) = ‖ρ s‖ * ∫ p, ‖G p‖ ∂(πP F) := by
    intro s
    show (∫ p, ‖(ρ s : ℂ) * G (scaleT F (delta F v s) p)‖ ∂(πP F)) = _
    simp only [norm_mul, Complex.norm_real]
    rw [integral_const_mul]
    congr 1
    exact integral_comp_scaleT F (delta F v s) (fun p => ‖G p‖) hGm.norm
  have hInt : Integrable Φ ((volume : Measure ℝ).prod (πP F)) := by
    rw [integrable_prod_iff hΦm]
    constructor
    · refine ae_of_all _ fun s => ?_
      show Integrable (fun p => (ρ s : ℂ) * G (scaleT F (delta F v s) p)) (πP F)
      exact (integrable_comp_scaleT F _ G hGm hG).const_mul _
    · have e : (fun s : ℝ => ∫ p, ‖Φ (s, p)‖ ∂(πP F)) = fun s => ‖ρ s‖ * ∫ p, ‖G p‖ ∂(πP F) := funext hnorm
      rw [e]
      exact (hρc.integrable_of_hasCompactSupport hρs).norm.mul_const _

  have hswap := integral_integral_swap hInt

  have h1 : ∫ s : ℝ, ∫ p, (ρ s : ℂ) * G (scaleT F (delta F v s) p) ∂(πP F) = ∫ p, G p ∂(πP F) := by
    have e : (fun s : ℝ => ∫ p, (ρ s : ℂ) * G (scaleT F (delta F v s) p) ∂(πP F)) = fun s => (ρ s : ℂ) * ∫ p, G p ∂(πP F) := by
      funext s
      show (∫ p, (ρ s : ℂ) * G (scaleT F (delta F v s) p) ∂(πP F)) = _
      rw [integral_const_mul, integral_comp_scaleT F _ G hGm]
    rw [e, integral_mul_const, integral_complex_ofReal, hρ1, Complex.ofReal_one, one_mul]
  rw [← h1]
  exact hswap

end Averaging

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Phase

variable (F : Type) [Field F] [NumberField F]

def IintS (v : InfinitePlace F) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t s : ℝ) (p : Pspace F) : ℂ :=
  ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (p.1.1.2 * p.1.2) : ℂˣ) : ℂ) *
  ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) p.1.1.2 : ℂˣ) : ℂ) *
  (((NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) : ℝ) : ℂ) *
  (((NumberField.TateGlobal.ideleNorm F p.1.2)⁻¹ : ℝ) : ℂ) *
  f₀ ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ *
    (unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2 * (diagOne (delta F v s) * (p.2 : AdelicGL2 (𝓞 F) F)))) *
  ψ0 (p.2 : AdelicGL2 (𝓞 F) F) * conj (φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F))

theorem ofReal_exp_cpow (a : ℝ) (z : ℂ) : ((Real.exp a : ℝ) : ℂ) ^ z = Complex.exp ((a : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos a).ne'), ← Complex.ofReal_log (Real.exp_pos a).le,
    Real.log_exp]

theorem Iint_scaleT_delta (v : InfinitePlace F) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (τ : ℝ)
    (hτ : ∀ x : (v.Completion)ˣ,
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar μ v x : ℂˣ) : ℂ) = ((ideleNorm F (archUnitHom v x) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
    (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t s : ℝ) (p : Pspace F) :
    Iint F αm hαm μ ν w f₀ φ0 ψ0 t (scaleT F (delta F v s) p) =
      Complex.exp (Complex.I * (((v.mult : ℝ) * (τ + t) : ℝ) : ℂ) * (s : ℂ)) *
      ((Real.exp ((v.mult : ℝ) * s * ((w - 1) / 2)) : ℝ) : ℂ) *
      IintS F v αm hαm μ ν w f₀ φ0 ψ0 t s p := by
  obtain ⟨⟨⟨⟨k, x⟩, u⟩, t'⟩, k'⟩ := p

  set δ := delta F v s with hδ
  set m : ℝ := (v.mult : ℝ) with hm
  have hNδ : ideleNorm F δ = Real.exp (m * s) := ideleNorm_delta F v s
  have hre : 0 < (InfinitePlace.Completion.extensionEmbedding v ((posUnit F v s : (v.Completion)ˣ) : v.Completion)).re := by
    rw [show ((posUnit F v s : (v.Completion)ˣ) : v.Completion) = posElt F v s from rfl, extensionEmbedding_posElt,
      Complex.ofReal_re]; exact Real.exp_pos s
  have him : (InfinitePlace.Completion.extensionEmbedding v ((posUnit F v s : (v.Completion)ˣ) : v.Completion)).im = 0 := by
    rw [show ((posUnit F v s : (v.Completion)ˣ) : v.Completion) = posElt F v s from rfl, extensionEmbedding_posElt,
      Complex.ofReal_im]
  have hη : ((etaFst μ αm hαm ((t : ℂ) * Complex.I) δ : ℂˣ) : ℂ) =
      Complex.exp (Complex.I * ((m * (τ + t) : ℝ) : ℂ) * (s : ℂ)) * ((Real.exp (m * s * (1 / 2)) : ℝ) : ℂ) := by
    have h := Ws31.TorusDecay.etaFst_archUnitHom F v (posUnit F v s) (Real.exp s) (Real.exp_pos s)
      (extensionEmbedding_posElt F v s) αm hαm hαN μ τ (hτ _ hre him) ((t : ℂ) * Complex.I)
    rw [hδ, show delta F v s = archUnitHom v (posUnit F v s) from rfl, h, ← Real.exp_nat_mul, ofReal_exp_cpow, ofReal_exp_cpow,
      ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [hm]
    push_cast
    ring

  have e_eta : ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * (δ * t')) : ℂˣ) : ℂ) =
      ((etaFst μ αm hαm ((t : ℂ) * Complex.I) δ : ℂˣ) : ℂ) * ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) := by
    rw [mul_left_comm, map_mul, Units.val_mul]
  have e_det : ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u * diagOne (δ * t'))) =
      ideleNorm F δ * ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u * diagOne t')) := by
    rw [map_mul Matrix.GeneralLinearGroup.det, map_mul Matrix.GeneralLinearGroup.det, det_diagOne, det_diagOne,
      ideleNorm_mul, ideleNorm_mul, ideleNorm_mul]; ring
  have e_word : unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne (δ * t') * (k' : AdelicGL2 (𝓞 F) F) =
      unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t' * (diagOne δ * (k' : AdelicGL2 (𝓞 F) F)) := by
    rw [mul_comm δ t', map_mul]; simp only [mul_assoc]

  simp only [Iint, IintS, scaleT, word4]
  rw [e_eta, hη, e_det, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, ideleNorm_mul, mul_inv, hNδ, e_word]

  have hsc : ((Real.exp (m * s * ((w - 1) / 2)) : ℝ) : ℂ) = ((Real.exp (m * s * (1 / 2)) : ℝ) : ℂ) *
      (((Real.exp (m * s)) ^ (w / 2) : ℝ) : ℂ) * (((Real.exp (m * s))⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [← Real.exp_mul, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hsc]
  push_cast
  ring

end Phase

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section PhaseU

variable (F : Type) [Field F] [NumberField F]

theorem etaSnd_archUnitHom (v : InfinitePlace F) (x : (v.Completion)ˣ) (r : ℝ) (hr : 0 < r)
    (hx : InfinitePlace.Completion.extensionEmbedding v (x : v.Completion) = (r : ℂ))
    (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ z, 0 < ((αm z : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (τ : ℝ)
    (hτ : ((archLocalChar ν v x : ℂˣ) : ℂ) = ((ideleNorm F (archUnitHom v x) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
    (s : ℂ) :
    ((etaSnd ν αm hαm s (archUnitHom v x) : ℂˣ) : ℂ)
      = ((r ^ v.mult : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I) * ((r ^ v.mult : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
  have hN : ideleNorm F (archUnitHom v x) = r ^ v.mult := by
    rw [Ws31.TorusDecay.ideleNorm_archUnitHom, Ws31.TorusDecay.norm_eq_of_extensionEmbedding_eq F v x r hr hx]
  rw [etaSnd_apply, Units.val_mul]
  have h1 : ((ν (archUnitHom v x) : ℂˣ) : ℂ) = ((r ^ v.mult : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I) := by
    rw [← hN, ← hτ]; rfl
  have h2 : ((cpowChar αm hαm (-(s + 1 / 2)) (archUnitHom v x) : ℂˣ) : ℂ) = ((r ^ v.mult : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
    show ((((αm (archUnitHom v x) : ℝˣ) : ℝ) : ℂ)) ^ (-(s + 1 / 2)) = _
    rw [hαN, hN]
  rw [h1, h2]

theorem det_centralScalar (u : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u) = u * u := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F)).det = u * u
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

theorem centralScalar_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  apply Units.ext
  change Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

def IintSU (v : InfinitePlace F) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t s : ℝ) (p : Pspace F) : ℂ :=
  ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (p.1.1.2 * p.1.2) : ℂˣ) : ℂ) *
  ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) p.1.1.2 : ℂˣ) : ℂ) *
  (((NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) : ℝ) : ℂ) *
  (((NumberField.TateGlobal.ideleNorm F p.1.2)⁻¹ : ℝ) : ℂ) *
  f₀ ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ *
    (unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2 *
      (centralScalar (𝓞 F) F (delta F v s) * diagOne (delta F v s)⁻¹ * (p.2 : AdelicGL2 (𝓞 F) F)))) *
  ψ0 (p.2 : AdelicGL2 (𝓞 F) F) * conj (φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F))

theorem Iint_scaleU_delta (v : InfinitePlace F) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (τ : ℝ)
    (hτ : ∀ x : (v.Completion)ˣ,
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar ν v x : ℂˣ) : ℂ) = ((ideleNorm F (archUnitHom v x) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
    (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t s : ℝ) (p : Pspace F) :
    Iint F αm hαm μ ν w f₀ φ0 ψ0 t (scaleU F (delta F v s) p) =
      Complex.exp (Complex.I * (((v.mult : ℝ) * (τ - t) : ℝ) : ℂ) * (s : ℂ)) *
      ((Real.exp ((v.mult : ℝ) * s * ((w + 1) / 2)) : ℝ) : ℂ) *
      IintSU F v αm hαm μ ν w f₀ φ0 ψ0 t s p := by
  obtain ⟨⟨⟨⟨k, x⟩, u⟩, t'⟩, k'⟩ := p
  set δ := delta F v s with hδ
  set m : ℝ := (v.mult : ℝ) with hm
  have hNδ : ideleNorm F δ = Real.exp (m * s) := ideleNorm_delta F v s
  have hNδi : ideleNorm F δ⁻¹ = (Real.exp (m * s))⁻¹ := by
    have h := ideleNorm_mul (F := F) δ δ⁻¹
    rw [mul_inv_cancel, ideleNorm_one, hNδ] at h
    have hpos : Real.exp (m * s) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    linarith [h]
  have hre : 0 < (InfinitePlace.Completion.extensionEmbedding v ((posUnit F v s : (v.Completion)ˣ) : v.Completion)).re := by
    rw [show ((posUnit F v s : (v.Completion)ˣ) : v.Completion) = posElt F v s from rfl, extensionEmbedding_posElt,
      Complex.ofReal_re]; exact Real.exp_pos s
  have him : (InfinitePlace.Completion.extensionEmbedding v ((posUnit F v s : (v.Completion)ˣ) : v.Completion)).im = 0 := by
    rw [show ((posUnit F v s : (v.Completion)ˣ) : v.Completion) = posElt F v s from rfl, extensionEmbedding_posElt,
      Complex.ofReal_im]
  have hη : ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) δ : ℂˣ) : ℂ) =
      Complex.exp (Complex.I * ((m * (τ - t) : ℝ) : ℂ) * (s : ℂ)) * ((Real.exp (-(m * s * (1 / 2))) : ℝ) : ℂ) := by
    have h := etaSnd_archUnitHom F v (posUnit F v s) (Real.exp s) (Real.exp_pos s)
      (extensionEmbedding_posElt F v s) αm hαm hαN ν τ (hτ _ hre him) ((t : ℂ) * Complex.I)
    rw [hδ, show delta F v s = archUnitHom v (posUnit F v s) from rfl, h, ← Real.exp_nat_mul, ofReal_exp_cpow, ofReal_exp_cpow,
      ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [hm]
    push_cast
    ring

  have e_prod : δ * u * (δ⁻¹ * t') = u * t' := by
    rw [mul_comm δ u, mul_assoc, ← mul_assoc δ, mul_inv_cancel, one_mul]
  have e_eta2 : ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) (δ * u) : ℂˣ) : ℂ) =
      ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) δ : ℂˣ) : ℂ) * ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) := by
    rw [map_mul, Units.val_mul]
  have e_det : ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (δ * u) * diagOne (δ⁻¹ * t'))) =
      ideleNorm F δ * ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u * diagOne t')) := by
    rw [map_mul Matrix.GeneralLinearGroup.det, map_mul Matrix.GeneralLinearGroup.det, det_diagOne, det_diagOne,
      det_centralScalar, det_centralScalar, ideleNorm_mul, ideleNorm_mul, ideleNorm_mul, ideleNorm_mul, ideleNorm_mul, ideleNorm_mul,
      hNδi, hNδ]
    have hpos : Real.exp (m * s) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  have e_word : unipotentGL2 x * centralScalar (𝓞 F) F (δ * u) * diagOne (δ⁻¹ * t') * (k' : AdelicGL2 (𝓞 F) F) =
      unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t' *
        (centralScalar (𝓞 F) F δ * diagOne δ⁻¹ * (k' : AdelicGL2 (𝓞 F) F)) := by
    have hd : (diagOne (δ⁻¹ * t') : AdelicGL2 (𝓞 F) F) = diagOne t' * diagOne δ⁻¹ := by rw [mul_comm, map_mul]
    rw [map_mul (centralScalar (𝓞 F) F), hd]
    have hc := centralScalar_comm F δ (centralScalar (𝓞 F) F u * diagOne t')
    have h1 : unipotentGL2 x * (centralScalar (𝓞 F) F δ * centralScalar (𝓞 F) F u) * (diagOne t' * diagOne δ⁻¹) *
        (k' : AdelicGL2 (𝓞 F) F) =
        unipotentGL2 x * (centralScalar (𝓞 F) F δ * (centralScalar (𝓞 F) F u * diagOne t')) *
          (diagOne δ⁻¹ * (k' : AdelicGL2 (𝓞 F) F)) := by simp only [mul_assoc]
    rw [h1, hc]
    simp only [mul_assoc]
  simp only [Iint, IintSU, scaleU, word4]
  rw [e_prod, e_eta2, hη, e_det, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, ideleNorm_mul, mul_inv, hNδi, inv_inv, hNδ,
    e_word]
  have hsc : ((Real.exp (m * s * ((w + 1) / 2)) : ℝ) : ℂ) = ((Real.exp (-(m * s * (1 / 2))) : ℝ) : ℂ) *
      (((Real.exp (m * s)) ^ (w / 2) : ℝ) : ℂ) * ((Real.exp (m * s) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hsc]
  push_cast
  ring

end PhaseU

end Ws31.Unfold

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Entries

variable (F : Type) [Field F] [NumberField F]

abbrev Ent : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

scoped instance entNormedAddCommGroup : NormedAddCommGroup (Ent F) := Pi.normedAddCommGroup
scoped instance entNormedSpace : NormedSpace ℝ (Ent F) := Pi.normedSpace

theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_archEntries : Continuous (archEntries F) := by
  have hval : Continuous fun a : GL (Fin 2) (InfiniteAdeleRing F) =>
      (a.val : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => (continuous_ringEquiv_mixedSpace F).comp ?_
  exact (continuous_apply j).comp
    ((continuous_apply i : Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) => m i).comp hval)

theorem of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix.of (archEntries F g) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  funext i j
  rfl

theorem of_archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix.of (archEntries F (a * z)) = Matrix.of (archEntries F a) * Matrix.of (archEntries F z) := by
  simp only [of_archEntries, Units.val_mul, map_mul]

theorem archEntries_mul3 (a b z : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (a * b * z) = Matrix.of.symm (Matrix.of (archEntries F a) * Matrix.of (archEntries F b) *
      Matrix.of (archEntries F z)) := by
  rw [← of_archEntries_mul, ← of_archEntries_mul, Equiv.symm_apply_apply]

def mvec (v : InfinitePlace F) (s : ℝ) : mixedEmbedding.mixedSpace F :=
  InfiniteAdeleRing.ringEquiv_mixedSpace F (((delta F v s : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1)

theorem delta_fst (v : InfinitePlace F) (s : ℝ) :
    (((delta F v s : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1) =
      Function.update (1 : InfiniteAdeleRing F) v (posElt F v s) := rfl

theorem delta_snd (v : InfinitePlace F) (s : ℝ) :
    (((delta F v s : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) = 1 := rfl

theorem mvec_fst_apply (v : InfinitePlace F) (s : ℝ) (w : {w : InfinitePlace F // w.IsReal}) :
    (mvec F v s).1 w = if (w : InfinitePlace F) = v then Real.exp s else 1 := by
  obtain ⟨w, hw⟩ := w
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (Function.update (1 : InfiniteAdeleRing F) v (posElt F v s) w) = _
  by_cases h : w = v
  · subst h
    rw [if_pos rfl, Function.update_self]
    apply Complex.ofReal_injective
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    exact extensionEmbedding_posElt F w s
  · rw [if_neg h, Function.update_of_ne h]
    have e1 : (1 : InfiniteAdeleRing F) w = 1 := rfl
    rw [e1, map_one]

theorem mvec_snd_apply (v : InfinitePlace F) (s : ℝ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (mvec F v s).2 w = if (w : InfinitePlace F) = v then ((Real.exp s : ℝ) : ℂ) else 1 := by
  obtain ⟨w, hw⟩ := w
  show InfinitePlace.Completion.extensionEmbedding w (Function.update (1 : InfiniteAdeleRing F) v (posElt F v s) w) = _
  by_cases h : w = v
  · subst h
    rw [if_pos rfl, Function.update_self]
    exact extensionEmbedding_posElt F w s
  · rw [if_neg h, Function.update_of_ne h]
    have e1 : (1 : InfiniteAdeleRing F) w = 1 := rfl
    rw [e1, map_one]

theorem contDiff_mvec (v : InfinitePlace F) : ContDiff ℝ (⊤ : ℕ∞) (mvec F v) := by
  have e : mvec F v = fun s => ((fun w : {w : InfinitePlace F // w.IsReal} => if (w : InfinitePlace F) = v then Real.exp s else 1),
      (fun w : {w : InfinitePlace F // w.IsComplex} => if (w : InfinitePlace F) = v then ((Real.exp s : ℝ) : ℂ) else 1)) := by
    funext s
    exact Prod.ext (funext (mvec_fst_apply F v s)) (funext (mvec_snd_apply F v s))
  rw [e]
  refine ContDiff.prodMk (contDiff_pi.2 fun w => ?_) (contDiff_pi.2 fun w => ?_)
  · by_cases h : (w : InfinitePlace F) = v
    · simp only [if_pos h]; exact Real.contDiff_exp
    · simp only [if_neg h]; exact contDiff_const
  · by_cases h : (w : InfinitePlace F) = v
    · simp only [if_pos h]; exact Complex.ofRealCLM.contDiff.comp Real.contDiff_exp
    · simp only [if_neg h]; exact contDiff_const

theorem continuous_mvec (v : InfinitePlace F) : Continuous (mvec F v) := (contDiff_mvec F v).continuous

end Entries

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section ZMat

variable (F : Type) [Field F] [NumberField F]

theorem adele_fst_mul (a b : AdeleRing (𝓞 F) F) : (a * b).1 = a.1 * b.1 := rfl
theorem adele_fst_one : (1 : AdeleRing (𝓞 F) F).1 = 1 := rfl
theorem adele_fst_zero : (0 : AdeleRing (𝓞 F) F).1 = 0 := rfl
theorem adele_snd_one : (1 : AdeleRing (𝓞 F) F).2 = 1 := rfl
theorem adele_snd_zero : (0 : AdeleRing (𝓞 F) F).2 = 0 := rfl

theorem posUnit_add (v : InfinitePlace F) (s s' : ℝ) : posUnit F v (s + s') = posUnit F v s * posUnit F v s' := by
  apply Units.ext
  show posElt F v (s + s') = posElt F v s * posElt F v s'
  exact posElt_add F v s s'

theorem delta_add (v : InfinitePlace F) (s s' : ℝ) : delta F v (s + s') = delta F v s * delta F v s' := by
  unfold delta; rw [posUnit_add, map_mul]

theorem delta_zero (v : InfinitePlace F) : delta F v 0 = 1 := by
  unfold delta
  have : posUnit F v 0 = 1 := Units.ext (posElt_zero F v)
  rw [this, map_one]

theorem delta_neg (v : InfinitePlace F) (s : ℝ) : delta F v (-s) = (delta F v s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← delta_add, neg_add_cancel, delta_zero]

theorem mvec_add (v : InfinitePlace F) (s s' : ℝ) : mvec F v (s + s') = mvec F v s * mvec F v s' := by
  unfold mvec
  rw [delta_add, Units.val_mul, adele_fst_mul, map_mul]

theorem mvec_zero (v : InfinitePlace F) : mvec F v 0 = 1 := by
  unfold mvec
  rw [delta_zero, Units.val_one, adele_fst_one, map_one]

theorem mvec_neg_mul (v : InfinitePlace F) (s : ℝ) : mvec F v (-s) * mvec F v s = 1 := by
  rw [← mvec_add, neg_add_cancel, mvec_zero]

theorem mvec_mul_neg (v : InfinitePlace F) (s : ℝ) : mvec F v s * mvec F v (-s) = 1 := by
  rw [← mvec_add, add_neg_cancel, mvec_zero]

abbrev ZT (v : InfinitePlace F) (s : ℝ) : AdelicGL2 (𝓞 F) F := diagOne (delta F v s)

abbrev ZU (v : InfinitePlace F) (s : ℝ) : AdelicGL2 (𝓞 F) F := centralScalar (𝓞 F) F (delta F v s) * diagOne (delta F v s)⁻¹

def NT (v : InfinitePlace F) (s : ℝ) : Ent F := fun i j => Matrix.diagonal ![mvec F v s, 1] i j

def NU (v : InfinitePlace F) (s : ℝ) : Ent F := fun i j => Matrix.diagonal ![1, mvec F v s] i j

theorem archEntries_glArch_diagOne_delta (v : InfinitePlace F) (s : ℝ) :
    archEntries F (glArch (𝓞 F) F (diagOne (delta F v s))) = NT F v s := by
  funext i j
  rw [archEntries_apply, glArch_apply, diagOne_coe_apply]
  show _ = Matrix.diagonal ![mvec F v s, 1] i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    fin_cases i
    · rfl
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F ((1 : AdeleRing (𝓞 F) F).1) = 1
      rw [adele_fst_one, map_one]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, adele_fst_zero, map_zero]

theorem archEntries_glArch_centralScalar_delta (v : InfinitePlace F) (s : ℝ) :
    archEntries F (glArch (𝓞 F) F (centralScalar (𝓞 F) F (delta F v s))) =
      fun i j => Matrix.diagonal (fun _ => mvec F v s) i j := by
  funext i j
  rw [archEntries_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [NumberField.AdelicVolume.centralScalar_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [NumberField.AdelicVolume.centralScalar_apply_ne _ h, Matrix.diagonal_apply_ne _ h, adele_fst_zero, map_zero]

theorem archEntries_glArch_ZT (v : InfinitePlace F) (s : ℝ) :
    archEntries F (glArch (𝓞 F) F (ZT F v s)) = NT F v s :=
  archEntries_glArch_diagOne_delta F v s

theorem archEntries_glArch_ZU (v : InfinitePlace F) (s : ℝ) :
    archEntries F (glArch (𝓞 F) F (ZU F v s)) = NU F v s := by
  unfold ZU
  rw [map_mul, ← delta_neg]
  apply Matrix.of.injective
  rw [of_archEntries_mul, archEntries_glArch_centralScalar_delta, archEntries_glArch_diagOne_delta]
  change Matrix.diagonal (fun _ => mvec F v s) * Matrix.diagonal ![mvec F v (-s), 1] = Matrix.diagonal ![1, mvec F v s]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · exact mvec_mul_neg F v s
  · exact mul_one _

theorem glFin_diagOne_delta (v : InfinitePlace F) (s : ℝ) : glFin (𝓞 F) F (diagOne (delta F v s)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply, diagOne_coe_apply, Units.val_one]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    fin_cases i
    · rfl
    · rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    rfl

theorem glFin_ZT (v : InfinitePlace F) (s : ℝ) : glFin (𝓞 F) F (ZT F v s) = 1 := glFin_diagOne_delta F v s

theorem glFin_centralScalar_delta (v : InfinitePlace F) (s : ℝ) : glFin (𝓞 F) F (centralScalar (𝓞 F) F (delta F v s)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply, Units.val_one]
  by_cases h : i = j
  · subst h; rw [NumberField.AdelicVolume.centralScalar_apply_eq, Matrix.one_apply_eq]; rfl
  · rw [NumberField.AdelicVolume.centralScalar_apply_ne _ h, Matrix.one_apply_ne h]; rfl

theorem glFin_ZU (v : InfinitePlace F) (s : ℝ) : glFin (𝓞 F) F (ZU F v s) = 1 := by
  unfold ZU
  rw [map_mul, ← delta_neg, glFin_centralScalar_delta, glFin_diagOne_delta, mul_one]

theorem contDiff_NT (v : InfinitePlace F) : ContDiff ℝ (⊤ : ℕ∞) (NT F v) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  by_cases h : i = j
  · subst h
    have e : (fun s => NT F v s i i) = fun s => ![mvec F v s, 1] i := by
      funext s; exact Matrix.diagonal_apply_eq _ _
    rw [e]
    fin_cases i
    · exact contDiff_mvec F v
    · exact contDiff_const
  · have e : (fun s => NT F v s i j) = fun _ => 0 := by
      funext s; exact Matrix.diagonal_apply_ne _ h
    rw [e]; exact contDiff_const

theorem contDiff_NU (v : InfinitePlace F) : ContDiff ℝ (⊤ : ℕ∞) (NU F v) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  by_cases h : i = j
  · subst h
    have e : (fun s => NU F v s i i) = fun s => ![1, mvec F v s] i := by
      funext s; exact Matrix.diagonal_apply_eq _ _
    rw [e]
    fin_cases i
    · exact contDiff_const
    · exact contDiff_mvec F v
  · have e : (fun s => NU F v s i j) = fun _ => 0 := by
      funext s; exact Matrix.diagonal_apply_ne _ h
    rw [e]; exact contDiff_const

theorem continuous_ZT (v : InfinitePlace F) : Continuous (ZT F v) := (continuous_diagOne F).comp (continuous_delta F v)

theorem continuous_ZU (v : InfinitePlace F) : Continuous (ZU F v) :=
  ((continuous_centralScalar F).comp (continuous_delta F v)).mul ((continuous_diagOne F).comp (continuous_delta F v).inv)

end ZMat
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Amplitude

variable (F : Type) [Field F] [NumberField F]

abbrev Par : Type := (Ent F × Ent F) × ℝ

scoped instance entProdNormedAddCommGroup : NormedAddCommGroup (Ent F × Ent F) := Prod.normedAddCommGroup
scoped instance entProdNormedSpace : NormedSpace ℝ (Ent F × Ent F) := Prod.normedSpace
scoped instance parNormedAddCommGroup : NormedAddCommGroup (Par F) := Prod.normedAddCommGroup
scoped instance parNormedSpace : NormedSpace ℝ (Par F) := Prod.normedSpace
scoped instance parProdNormedAddCommGroup : NormedAddCommGroup (Par F × ℝ) := Prod.normedAddCommGroup
scoped instance parProdNormedSpace : NormedSpace ℝ (Par F × ℝ) := Prod.normedSpace
scoped instance parFiniteDimensional : FiniteDimensional ℝ (Par F) := inferInstance

theorem contDiff_tripleMul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ∞}
    {A B C : X → Ent F} (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) (hC : ContDiff ℝ n C) :
    ContDiff ℝ n (fun x => Matrix.of.symm (Matrix.of (A x) * Matrix.of (B x) * Matrix.of (C x))) := by
  have pA : ∀ i j, ContDiff ℝ n fun x => A x i j := fun i j => contDiff_pi.1 (contDiff_pi.1 hA i) j
  have pB : ∀ i j, ContDiff ℝ n fun x => B x i j := fun i j => contDiff_pi.1 (contDiff_pi.1 hB i) j
  have pC : ∀ i j, ContDiff ℝ n fun x => C x i j := fun i j => contDiff_pi.1 (contDiff_pi.1 hC i) j
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
  exact ((((pA i 0).mul (pB 0 0)).add ((pA i 1).mul (pB 1 0))).mul (pC 0 j)).add
    ((((pA i 0).mul (pB 0 1)).add ((pA i 1).mul (pB 1 1))).mul (pC 1 j))

def Psi (Φ : Ent F → ℂ) (N : ℝ → Ent F) (ρ : ℝ → ℝ) (c m : ℝ) (j : ℕ) (a : Par F) (s : ℝ) : ℂ :=
  (ρ s : ℂ) * ((Real.exp (c * s) : ℝ) : ℂ) * (Complex.I * ((m * s + a.2 : ℝ) : ℂ)) ^ j *
    Φ (Matrix.of.symm (Matrix.of a.1.1 * Matrix.of (N s) * Matrix.of a.1.2))

theorem contDiff_Psi (Φ : Ent F → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (N : ℝ → Ent F) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (c m : ℝ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Par F × ℝ => Psi F Φ N ρ c m j p.1 p.2) := by
  unfold Psi
  refine ((ContDiff.mul ?_ ?_).mul ?_).mul ?_
  · exact Complex.ofRealCLM.contDiff.comp (hρ.comp contDiff_snd)
  · exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd))
  · refine (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_)).pow j
    exact (contDiff_const.mul contDiff_snd).add (contDiff_snd.comp contDiff_fst)
  · exact hΦ.comp (contDiff_tripleMul F (contDiff_fst.comp (contDiff_fst.comp contDiff_fst)) (hN.comp contDiff_snd)
      (contDiff_snd.comp (contDiff_fst.comp contDiff_fst)))

theorem tsupport_Psi_subset (Φ : Ent F → ℂ) (N : ℝ → Ent F) (ρ : ℝ → ℝ) (c m : ℝ) (j : ℕ) (a : Par F) :
    tsupport (Psi F Φ N ρ c m j a) ⊆ tsupport ρ := by
  refine closure_mono fun s hs => ?_
  rw [Function.mem_support] at hs ⊢
  intro h
  apply hs
  show (ρ s : ℂ) * _ * _ * _ = 0
  rw [h, Complex.ofReal_zero, zero_mul, zero_mul, zero_mul]

theorem tsupport_iteratedDeriv_subset' {f : ℝ → ℂ} (n : ℕ) : tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => rw [iteratedDeriv_zero]
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem integral_norm_le_of_support_subset_Icc {g : ℝ → ℂ} {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hsupp : Function.support g ⊆ Set.Icc (-R) R) (hle : ∀ u ∈ Set.Icc (-R) R, ‖g u‖ ≤ C) :
    ∫ u, ‖g u‖ ≤ 2 * R * C := by
  have h0 : ∀ u, u ∉ Set.Icc (-R) R → ‖g u‖ = 0 := fun u hu => by
    rw [norm_eq_zero]; exact Function.notMem_support.mp fun h => hu (hsupp h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0]
  have h1 := norm_setIntegral_le_of_norm_le_const (measure_Icc_lt_top (μ := volume) (a := -R) (b := R))
    (fun u hu => show ‖‖g u‖‖ ≤ C by rw [norm_norm]; exact hle u hu)
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at h1
  have h2 : (∫ u in Set.Icc (-R) R, ‖g u‖) ≤ ‖∫ u in Set.Icc (-R) R, ‖g u‖‖ := Real.le_norm_self _
  linarith

theorem Psi_osc_bound (Φ : Ent F → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (N : ℝ → Ent F) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (R : ℝ) (hR : 0 ≤ R) (hρR : tsupport ρ ⊆ Set.Icc (-R) R)
    (c m : ℝ) (j : ℕ) (S : Set (Par F)) (hS : IsCompact S) (Nn : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a ∈ S, ∀ l : ℝ,
      ‖∫ u : ℝ, Psi F Φ N ρ c m j a u * Complex.exp (Complex.I * (l : ℂ) * (u : ℂ))‖ ≤ L * (1 + |l|) ^ (-(Nn : ℝ)) := by
  obtain ⟨hcd, C, hC0, hC⟩ := ContDiff.exists_forall_norm_iteratedDeriv_slice_le_of_isCompact (Psi F Φ N ρ c m j)
    (contDiff_Psi F Φ hΦ N hN ρ hρ c m j) S hS R Nn
  refine ⟨2 ^ Nn * (2 * R * C + 2 * R * C), by positivity, fun a ha l => ?_⟩
  have hsub : tsupport (Psi F Φ N ρ c m j a) ⊆ Set.Icc (-R) R := (tsupport_Psi_subset F Φ N ρ c m j a).trans hρR
  have hHc : HasCompactSupport (Psi F Φ N ρ c m j a) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsub
  have key := MeasureTheory.norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport Nn
    (Psi F Φ N ρ c m j a) (hcd a) hHc l
  refine key.trans ?_
  have hpow : 0 ≤ (1 + |l|) ^ (-(Nn : ℝ)) := Real.rpow_nonneg (by positivity) _
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)) hpow
  · refine integral_norm_le_of_support_subset_Icc hR hC0 ((subset_tsupport _).trans hsub) fun u hu => ?_
    have := hC a ha u hu 0 (Nat.zero_le _)
    rwa [iteratedDeriv_zero] at this
  · refine integral_norm_le_of_support_subset_Icc hR hC0 ?_ fun u hu => hC a ha u hu Nn le_rfl
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset' Nn).trans hsub)

end Amplitude
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section SupportSets

variable (F : Type) [Field F] [NumberField F]

abbrev word3 (p : Pspace F) : AdelicGL2 (𝓞 F) F :=
  unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2

theorem word4_eq (p : Pspace F) : word4 F p = word3 F p * (p.2 : AdelicGL2 (𝓞 F) F) := rfl

theorem continuous_word3 : Continuous (word3 F) := by
  unfold word3
  exact ((AutomorphicForm.continuous_unipotentGL2.comp continuous_fst.fst.fst.snd).mul
    ((continuous_centralScalar F).comp continuous_fst.fst.snd)).mul ((continuous_diagOne F).comp continuous_fst.snd)

def W3 (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (Z : ℝ → AdelicGL2 (𝓞 F) F) (R : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  (fun q : (((adelicMaximalCompact F) × AdelicGL2 (𝓞 F) F) × adelicMaximalCompact F) × ℝ =>
      (q.1.1.1 : AdelicGL2 (𝓞 F) F) * q.1.1.2 * ((q.1.2 : AdelicGL2 (𝓞 F) F))⁻¹ * (Z q.2)⁻¹) ''
    (((Set.univ ×ˢ tsupport f₀) ×ˢ Set.univ) ×ˢ Set.Icc (-R) R)

theorem isCompact_W3 (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀c : HasCompactSupport f₀) (Z : ℝ → AdelicGL2 (𝓞 F) F)
    (hZ : Continuous Z) (R : ℝ) : IsCompact (W3 F f₀ Z R) := by
  refine (((isCompact_univ.prod hf₀c).prod isCompact_univ).prod isCompact_Icc).image ?_
  exact (((continuous_subtype_val.comp continuous_fst.fst.fst).mul continuous_fst.fst.snd).mul
    (continuous_subtype_val.comp continuous_fst.snd).inv).mul (hZ.comp continuous_snd).inv

theorem mem_W3 {f₀ : AdelicGL2 (𝓞 F) F → ℂ} {Z : ℝ → AdelicGL2 (𝓞 F) F} {R : ℝ} (k k' : adelicMaximalCompact F)
    (y : AdelicGL2 (𝓞 F) F) (s : ℝ) (hs : s ∈ Set.Icc (-R) R)
    (h : f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * (y * (Z s * (k' : AdelicGL2 (𝓞 F) F)))) ≠ 0) : y ∈ W3 F f₀ Z R := by
  refine ⟨(((k, (k : AdelicGL2 (𝓞 F) F)⁻¹ * (y * (Z s * (k' : AdelicGL2 (𝓞 F) F)))), k'), s),
    ⟨⟨⟨Set.mem_univ _, subset_tsupport _ h⟩, Set.mem_univ _⟩, hs⟩, ?_⟩
  show (k : AdelicGL2 (𝓞 F) F) * ((k : AdelicGL2 (𝓞 F) F)⁻¹ * (y * (Z s * (k' : AdelicGL2 (𝓞 F) F)))) *
    ((k' : AdelicGL2 (𝓞 F) F))⁻¹ * (Z s)⁻¹ = y
  group

def W4 (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (Z : ℝ → AdelicGL2 (𝓞 F) F) (R : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  Set.image2 (· * ·) (W3 F f₀ Z R) (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F))

theorem isCompact_W4 (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀c : HasCompactSupport f₀) (Z : ℝ → AdelicGL2 (𝓞 F) F)
    (hZ : Continuous Z) (R : ℝ) : IsCompact (W4 F f₀ Z R) :=
  isCompact_mul_maximalCompact F _ (isCompact_W3 F f₀ hf₀c Z hZ R)

theorem word4_mem_W4 {f₀ : AdelicGL2 (𝓞 F) F → ℂ} {Z : ℝ → AdelicGL2 (𝓞 F) F} {R : ℝ} (p : Pspace F)
    (hp : word3 F p ∈ W3 F f₀ Z R) : word4 F p ∈ W4 F f₀ Z R :=
  Set.mem_image2_of_mem hp p.2.2

def parOf (p : Pspace F) : Par F :=
  ((archEntries F (glArch (𝓞 F) F ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * word3 F p)),
    archEntries F (glArch (𝓞 F) F (p.2 : AdelicGL2 (𝓞 F) F))), Real.log (ideleNorm F p.1.2))

def ParS (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (Z : ℝ → AdelicGL2 (𝓞 F) F) (R : ℝ) : Set (Par F) :=
  ((fun q : ((adelicMaximalCompact F) × AdelicGL2 (𝓞 F) F) × adelicMaximalCompact F =>
      (archEntries F (glArch (𝓞 F) F ((q.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * q.1.2)),
        archEntries F (glArch (𝓞 F) F (q.2 : AdelicGL2 (𝓞 F) F)))) ''
    ((Set.univ ×ˢ W3 F f₀ Z R) ×ˢ Set.univ)) ×ˢ
  (Real.log '' ((NumberField.AdelicHeight.adelicHeight F) '' W4 F f₀ Z R))

theorem isCompact_ParS (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀c : HasCompactSupport f₀) (Z : ℝ → AdelicGL2 (𝓞 F) F)
    (hZ : Continuous Z) (R : ℝ) : IsCompact (ParS F f₀ Z R) := by
  refine IsCompact.prod ?_ ?_
  · refine (((isCompact_univ.prod (isCompact_W3 F f₀ hf₀c Z hZ R)).prod isCompact_univ)).image ?_
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_archEntries F).comp ((continuous_glArch (𝓞 F) F).comp
        ((continuous_subtype_val.comp continuous_fst.fst).inv.mul continuous_fst.snd))
    · exact (continuous_archEntries F).comp ((continuous_glArch (𝓞 F) F).comp (continuous_subtype_val.comp continuous_snd))
  · have h1 : IsCompact ((NumberField.AdelicHeight.adelicHeight F) '' W4 F f₀ Z R) :=
      (isCompact_W4 F f₀ hf₀c Z hZ R).image (NumberField.AdelicHeight.continuous_adelicHeight F)
    refine h1.image_of_continuousOn (Real.continuousOn_log.mono ?_)
    rintro _ ⟨y, _, rfl⟩
    exact (NumberField.AdelicHeight.adelicHeight_pos y).ne'

theorem parOf_mem_ParS {f₀ : AdelicGL2 (𝓞 F) F → ℂ} {Z : ℝ → AdelicGL2 (𝓞 F) F} {R : ℝ} (p : Pspace F)
    (hp : word3 F p ∈ W3 F f₀ Z R) : parOf F p ∈ ParS F f₀ Z R := by
  refine ⟨⟨((p.1.1.1.1, word3 F p), p.2), ⟨⟨Set.mem_univ _, hp⟩, Set.mem_univ _⟩, rfl⟩, ?_⟩
  refine ⟨NumberField.AdelicHeight.adelicHeight F (word4 F p), ⟨word4 F p, word4_mem_W4 F p hp, rfl⟩, ?_⟩
  show Real.log (NumberField.AdelicHeight.adelicHeight F (word4 F p)) = Real.log (ideleNorm F p.1.2)
  rw [show word4 F p = unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2 * (p.2 : AdelicGL2 (𝓞 F) F)
    from rfl, adelicHeight_word4]

theorem exists_bound_log_ideleNorm (W : Set (AdelicGL2 (𝓞 F) F)) (hW : IsCompact W) :
    ∃ LB : ℝ, 0 ≤ LB ∧ ∀ p : Pspace F, word4 F p ∈ W → |Real.log (ideleNorm F p.1.2)| ≤ LB := by
  have hc : Continuous fun y : AdelicGL2 (𝓞 F) F => Real.log (NumberField.AdelicHeight.adelicHeight F y) :=
    (NumberField.AdelicHeight.continuous_adelicHeight F).log fun y => (NumberField.AdelicHeight.adelicHeight_pos y).ne'
  obtain ⟨M, hM⟩ := hW.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun p hp => ?_⟩
  have h := hM _ hp
  rw [Real.norm_eq_abs, show word4 F p = unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2 *
    (p.2 : AdelicGL2 (𝓞 F) F) from rfl, adelicHeight_word4] at h
  exact h.trans (le_max_left _ _)

end SupportSets
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section LoneLtwo

variable (F : Type) [Field F] [NumberField F]

theorem integral_norm_le_one (φ0 : AdelicGL2 (𝓞 F) F → ℂ) (hφ0 : Continuous φ0)
    (hφn : ∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) ≤ 1) :
    ∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ∂(maximalCompactHaar F) ≤ 1 := by
  have hfc : Continuous fun k : adelicMaximalCompact F => ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ :=
    (hφ0.comp continuous_subtype_val).norm
  obtain ⟨Cf, hCf⟩ := isCompact_univ.exists_bound_of_continuousOn hfc.continuousOn
  have hF : MemLp (fun k : adelicMaximalCompact F => ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖) (ENNReal.ofReal 2) (maximalCompactHaar F) :=
    (memLp_top_of_bound hfc.aestronglyMeasurable Cf (Eventually.of_forall fun k => hCf k (Set.mem_univ _))).mono_exponent
      le_top
  have hG : MemLp (fun _ : adelicMaximalCompact F => (1 : ℝ)) (ENNReal.ofReal 2) (maximalCompactHaar F) :=
    (memLp_top_const 1).mono_exponent le_top
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := maximalCompactHaar F) Real.HolderConjugate.two_two
    (f := fun k : adelicMaximalCompact F => ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖) (g := fun _ => (1 : ℝ))
    (Eventually.of_forall fun k => norm_nonneg (φ0 (k : AdelicGL2 (𝓞 F) F))) (Eventually.of_forall fun _ => zero_le_one) hF hG
  have e1 : (∫ k : adelicMaximalCompact F, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ * (1 : ℝ) ∂(maximalCompactHaar F)) =
      ∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ∂(maximalCompactHaar F) := by
    simp only [mul_one]
  have e2 : (∫ _ : adelicMaximalCompact F, (1 : ℝ) ^ (2 : ℝ) ∂(maximalCompactHaar F)) = 1 := by
    rw [Real.one_rpow, integral_const]
    show ((maximalCompactHaar F) Set.univ).toReal • (1 : ℝ) = 1
    rw [measure_univ, ENNReal.toReal_one, one_smul]
  have e3 : (∫ k : adelicMaximalCompact F, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ (2 : ℝ) ∂(maximalCompactHaar F)) =
      ∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) := by
    simp_rw [Real.rpow_two]
  rw [e1, e2, e3, Real.one_rpow, mul_one] at h2
  have h3 : (∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F)) ^ ((1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one (integral_nonneg fun k => by positivity) hφn (by norm_num)
  exact h2.trans h3

end LoneLtwo
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Split

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

theorem lintegral_piP_split (a b : adelicMaximalCompact F → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b)
    (g : (AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p, a p.1.1.1.1 * g ((p.1.1.1.2, p.1.1.2), p.1.2) * b p.2 ∂(πP F) =
      (∫⁻ k, a k ∂(maximalCompactHaar F)) *
      (∫⁻ x, ∫⁻ u, ∫⁻ t, g ((x, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F)) *
      (∫⁻ k, b k ∂(maximalCompactHaar F)) := by
  haveI := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F
  haveI := secondCountableTopology_adele F
  haveI := sigmaFinite_adelicAddHaar F

  have m3 : Measurable fun q : (((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) ×
      (AdeleRing (𝓞 F) F)ˣ => a q.1.1.1 * g ((q.1.1.2, q.1.2), q.2) :=
    (ha.comp measurable_fst.fst.fst).mul (hg.comp ((measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd))
  have m4 : Measurable fun p : Pspace F => a p.1.1.1.1 * g ((p.1.1.1.2, p.1.1.2), p.1.2) * b p.2 :=
    (m3.comp measurable_fst).mul (hb.comp measurable_snd)
  unfold πP
  rw [lintegral_prod _ m4.aemeasurable]
  have e1 : (fun q : (((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ k' : adelicMaximalCompact F, a q.1.1.1 * g ((q.1.1.2, q.1.2), q.2) * b k' ∂(maximalCompactHaar F)) =
      fun q => a q.1.1.1 * g ((q.1.1.2, q.1.2), q.2) * ∫⁻ k', b k' ∂(maximalCompactHaar F) := by
    funext q; rw [lintegral_const_mul _ hb]
  rw [e1, lintegral_mul_const _ m3, lintegral_prod _ m3.aemeasurable]

  have m2g : Measurable fun q : ((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ t, g ((q.1.2, q.2), t) ∂(NumberField.Idele.idelicHaar F) := by
    have : Measurable fun q : (((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) ×
      (AdeleRing (𝓞 F) F)ˣ => g ((q.1.1.2, q.1.2), q.2) :=
      hg.comp ((measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd)
    exact this.lintegral_prod_right'
  have e2 : (fun q : ((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ t, a (q, t).1.1.1 * g (((q, t).1.1.2, (q, t).1.2), (q, t).2) ∂(NumberField.Idele.idelicHaar F)) =
      fun q => a q.1.1 * ∫⁻ t, g ((q.1.2, q.2), t) ∂(NumberField.Idele.idelicHaar F) := by
    funext q
    show ∫⁻ t, a q.1.1 * g ((q.1.2, q.2), t) ∂(NumberField.Idele.idelicHaar F) = _
    exact lintegral_const_mul _ (hg.comp ((measurable_const.prodMk measurable_const).prodMk measurable_id))
  rw [e2]
  have m2 : Measurable fun q : ((adelicMaximalCompact F) × AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ =>
      a q.1.1 * ∫⁻ t, g ((q.1.2, q.2), t) ∂(NumberField.Idele.idelicHaar F) := (ha.comp (by fun_prop)).mul m2g
  rw [lintegral_prod _ m2.aemeasurable]

  have m1g : Measurable fun q : (adelicMaximalCompact F) × AdeleRing (𝓞 F) F =>
      ∫⁻ u, ∫⁻ t, g ((q.2, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
    m2g.lintegral_prod_right'
  have e3 : (fun q : (adelicMaximalCompact F) × AdeleRing (𝓞 F) F =>
      ∫⁻ u, a (q, u).1.1 * ∫⁻ t, g (((q, u).1.2, (q, u).2), t) ∂(NumberField.Idele.idelicHaar F)
        ∂(NumberField.Idele.idelicHaar F)) =
      fun q => a q.1 * ∫⁻ u, ∫⁻ t, g ((q.2, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
    funext q
    show ∫⁻ u, a q.1 * ∫⁻ t, g ((q.2, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) = _
    exact lintegral_const_mul _ (m2g.comp ((measurable_const.prodMk measurable_const).prodMk measurable_id))
  rw [e3]
  have m1 : Measurable fun q : (adelicMaximalCompact F) × AdeleRing (𝓞 F) F =>
      a q.1 * ∫⁻ u, ∫⁻ t, g ((q.2, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
    (ha.comp measurable_fst).mul m1g
  rw [lintegral_prod _ m1.aemeasurable]

  have m0g : Measurable fun x : AdeleRing (𝓞 F) F =>
      ∫⁻ u, ∫⁻ t, g ((x, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
    m1g.comp (measurable_const (a := (1 : adelicMaximalCompact F)) |>.prodMk measurable_id)
  have e4 : (fun k : adelicMaximalCompact F => ∫⁻ x, a (k, x).1 * ∫⁻ u, ∫⁻ t, g (((k, x).2, u), t)
      ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F)) =
      fun k => a k * ∫⁻ x, ∫⁻ u, ∫⁻ t, g ((x, u), t)
        ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F) := by
    funext k
    show ∫⁻ x, a k * ∫⁻ u, ∫⁻ t, g ((x, u), t) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      ∂(adelicAddHaar (𝓞 F) F) = _
    exact lintegral_const_mul _ m0g
  rw [e4, lintegral_mul_const _ ha]

def G0 (W : Set (AdelicGL2 (𝓞 F) F)) (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (p : Pspace F) : ℝ :=
  W.indicator (fun _ => (1 : ℝ)) (word3 F p) * (ideleNorm F p.1.2)⁻¹ *
    ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖

theorem G0_nonneg (W : Set (AdelicGL2 (𝓞 F) F)) (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (p : Pspace F) : 0 ≤ G0 F W φ0 ψ0 p := by
  unfold G0
  have h1 := Set.indicator_nonneg (s := W) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) (word3 F p)
  have h2 := (inv_pos.mpr (ideleNorm_pos p.1.2)).le
  positivity

def I0 (W : Set (AdelicGL2 (𝓞 F) F)) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ u, ∫⁻ t, W.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t) *
      ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
    ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F)

theorem measurable_G0 (W : Set (AdelicGL2 (𝓞 F) F)) (hW : IsCompact W) (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0) : Measurable (G0 F W φ0 ψ0) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
  unfold G0
  refine ((((measurable_const.indicator hW.isClosed.measurableSet).comp (continuous_word3 F).measurable).mul ?_).mul ?_).mul ?_
  · exact ((NumberField.TateGlobal.continuous_ideleNorm F).measurable.comp (by fun_prop)).inv
  · exact (hψ0.comp (continuous_subtype_val.comp continuous_snd)).measurable.norm
  · exact (hφ0.comp (continuous_subtype_val.comp continuous_fst.fst.fst.fst)).measurable.norm

theorem lintegral_G0_eq (W : Set (AdelicGL2 (𝓞 F) F)) (hW : IsCompact W) (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0) :
    ∫⁻ p, ENNReal.ofReal (G0 F W φ0 ψ0 p) ∂(πP F) =
      (∫⁻ k, ENNReal.ofReal ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ∂(maximalCompactHaar F)) * I0 F W *
      (∫⁻ k, ENNReal.ofReal ‖ψ0 (k : AdelicGL2 (𝓞 F) F)‖ ∂(maximalCompactHaar F)) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
  set g : (AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞ := fun q =>
    W.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (unipotentGL2 q.1.1 * centralScalar (𝓞 F) F q.1.2 * diagOne q.2) *
      ENNReal.ofReal ((ideleNorm F q.2)⁻¹) with hg
  have hgm : Measurable g := by
    refine ((measurable_one.indicator hW.isClosed.measurableSet).comp ?_).mul
      (ENNReal.measurable_ofReal.comp (((NumberField.TateGlobal.continuous_ideleNorm F).measurable.comp measurable_snd).inv))
    exact (((AutomorphicForm.continuous_unipotentGL2.comp continuous_fst.fst).mul
      ((continuous_centralScalar F).comp continuous_fst.snd)).mul ((continuous_diagOne F).comp continuous_snd)).measurable
  have ha : Measurable fun k : adelicMaximalCompact F => ENNReal.ofReal ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ :=
    ENNReal.measurable_ofReal.comp (hφ0.comp continuous_subtype_val).measurable.norm
  have hb : Measurable fun k : adelicMaximalCompact F => ENNReal.ofReal ‖ψ0 (k : AdelicGL2 (𝓞 F) F)‖ :=
    ENNReal.measurable_ofReal.comp (hψ0.comp continuous_subtype_val).measurable.norm
  have e : ∀ p : Pspace F, ENNReal.ofReal (G0 F W φ0 ψ0 p) =
      ENNReal.ofReal ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖ * g ((p.1.1.1.2, p.1.1.2), p.1.2) *
        ENNReal.ofReal ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ := by
    intro p
    simp only [G0, hg]
    have h1 := Set.indicator_nonneg (s := W) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) (word3 F p)
    have h2 := (inv_pos.mpr (ideleNorm_pos p.1.2)).le
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul h1]
    have hind : ENNReal.ofReal (W.indicator (fun _ => (1 : ℝ)) (word3 F p)) =
        W.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (unipotentGL2 p.1.1.1.2 * centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2) := by
      show ENNReal.ofReal (W.indicator (fun _ => (1 : ℝ)) (word3 F p)) = W.indicator 1 (word3 F p)
      by_cases h : word3 F p ∈ W
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, ENNReal.ofReal_one]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.ofReal_zero]
    rw [hind]
    ring
  simp_rw [e]
  rw [lintegral_piP_split F _ _ ha hb g hgm]
  rfl

theorem lintegral_ofReal_norm_le_one (φ0 : AdelicGL2 (𝓞 F) F → ℂ) (hφ0 : Continuous φ0)
    (hφn : ∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) ≤ 1) :
    ∫⁻ k, ENNReal.ofReal ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ∂(maximalCompactHaar F) ≤ 1 := by
  have hi : Integrable (fun k : adelicMaximalCompact F => ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖) (maximalCompactHaar F) :=
    ((hφ0.comp continuous_subtype_val).norm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun k => norm_nonneg _), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (integral_norm_le_one F φ0 hφ0 hφn)

theorem integrable_G0_and_integral_le (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc_top : c ≠ ∞)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
    (W : Set (AdelicGL2 (𝓞 F) F)) (hW : IsCompact W) (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0)
    (hφn : ∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) ≤ 1)
    (hψn : ∫ k, ‖ψ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) ≤ 1) :
    I0 F W < ∞ ∧ Integrable (G0 F W φ0 ψ0) (πP F) ∧ ∫ p, G0 F W φ0 ψ0 p ∂(πP F) ≤ (I0 F W).toReal := by
  have hI : I0 F W < ∞ := lintegral_iwasawa_indicator_lt_top F c hc0 hc_top hc W hW
  have hmeas := measurable_G0 F W hW φ0 ψ0 hφ0 hψ0
  have hle : ∫⁻ p, ENNReal.ofReal (G0 F W φ0 ψ0 p) ∂(πP F) ≤ I0 F W := by
    rw [lintegral_G0_eq F W hW φ0 ψ0 hφ0 hψ0]
    calc _ ≤ 1 * I0 F W * 1 := by
          gcongr
          · exact lintegral_ofReal_norm_le_one F φ0 hφ0 hφn
          · exact lintegral_ofReal_norm_le_one F ψ0 hψ0 hψn
      _ = I0 F W := by rw [one_mul, mul_one]
  have hfin : HasFiniteIntegral (G0 F W φ0 ψ0) (πP F) := by
    rw [hasFiniteIntegral_iff_norm]
    have e : (fun p => ENNReal.ofReal ‖G0 F W φ0 ψ0 p‖) = fun p => ENNReal.ofReal (G0 F W φ0 ψ0 p) := by
      funext p; rw [Real.norm_eq_abs, abs_of_nonneg (G0_nonneg F W φ0 ψ0 p)]
    rw [e]
    exact lt_of_le_of_lt hle hI
  have hint : Integrable (G0 F W φ0 ψ0) (πP F) := ⟨hmeas.aestronglyMeasurable, hfin⟩
  refine ⟨hI, hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (G0_nonneg F W φ0 ψ0)) hint.aestronglyMeasurable]
  exact ENNReal.toReal_mono hI.ne hle

end Split
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Deriv

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

theorem etaPair_eq (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (t : ℝ)
    (u t' : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) * ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) =
      ((μ (u * t') : ℂˣ) : ℂ) * ((ν u : ℂˣ) : ℂ) *
        Complex.exp ((Real.log (ideleNorm F t') : ℂ) * ((t : ℂ) * Complex.I + 1 / 2)) := by
  rw [etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val, hαN, hαN,
    ← Real.exp_log (ideleNorm_pos (u * t')), ← Real.exp_log (ideleNorm_pos u), ofReal_exp_cpow, ofReal_exp_cpow,
    ideleNorm_mul, Real.log_mul (ideleNorm_pos u).ne' (ideleNorm_pos t').ne']
  have key : Complex.exp (((Real.log (ideleNorm F u) + Real.log (ideleNorm F t') : ℝ) : ℂ) * ((t : ℂ) * Complex.I + 1 / 2)) *
      Complex.exp ((Real.log (ideleNorm F u) : ℂ) * (-((t : ℂ) * Complex.I + 1 / 2))) =
      Complex.exp ((Real.log (ideleNorm F t') : ℂ) * ((t : ℂ) * Complex.I + 1 / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (((μ (u * t') : ℂˣ) : ℂ) * ((ν u : ℂˣ) : ℂ)) * key

def IintJ (j : ℕ) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F) : ℂ :=
  (Complex.I * (Real.log (ideleNorm F p.1.2) : ℂ)) ^ j * Iint F αm hαm μ ν w f₀ φ0 ψ0 t p

theorem IintJ_zero (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F) :
    IintJ F 0 αm hαm μ ν w f₀ φ0 ψ0 t p = Iint F αm hαm μ ν w f₀ φ0 ψ0 t p := by
  rw [IintJ, pow_zero, one_mul]

theorem norm_IintJ (j : ℕ) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F) :
    ‖IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t p‖ = |Real.log (ideleNorm F p.1.2)| ^ j * ‖Iint F αm hαm μ ν w f₀ φ0 ψ0 t p‖ := by
  rw [IintJ, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem Iint_eq_exp (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ)
    (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F) :
    Iint F αm hαm μ ν w f₀ φ0 ψ0 t p =
      Complex.exp ((Real.log (ideleNorm F p.1.2) : ℂ) * ((t : ℂ) * Complex.I + 1 / 2)) *
      (((μ (p.1.1.2 * p.1.2) : ℂˣ) : ℂ) * ((ν p.1.1.2 : ℂˣ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) : ℝ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm F p.1.2)⁻¹ : ℝ) : ℂ) *
        f₀ ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * word4 F p) * ψ0 (p.2 : AdelicGL2 (𝓞 F) F) *
          conj (φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F))) := by
  simp only [Iint]
  rw [etaPair_eq F αm hαm hαN μ ν t]
  ring

theorem hasDerivAt_Iint (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ)
    (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (p : Pspace F) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Iint F αm hαm μ ν w f₀ φ0 ψ0 t p) (IintJ F 1 αm hαm μ ν w f₀ φ0 ψ0 t p) t := by
  set L : ℝ := Real.log (ideleNorm F p.1.2) with hL
  set R : ℂ := ((μ (p.1.1.2 * p.1.2) : ℂˣ) : ℂ) * ((ν p.1.1.2 : ℂˣ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) : ℝ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm F p.1.2)⁻¹ : ℝ) : ℂ) *
        f₀ ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * word4 F p) * ψ0 (p.2 : AdelicGL2 (𝓞 F) F) *
          conj (φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)) with hR
  have hfun : (fun t : ℝ => Iint F αm hαm μ ν w f₀ φ0 ψ0 t p) =
      fun t : ℝ => Complex.exp ((L : ℂ) * ((t : ℂ) * Complex.I + 1 / 2)) * R := by
    funext t; exact Iint_eq_exp F αm hαm hαN μ ν w f₀ φ0 ψ0 t p
  have h1 : HasDerivAt (fun t : ℝ => (L : ℂ) * ((t : ℂ) * Complex.I + 1 / 2)) ((L : ℂ) * Complex.I) t := by
    have h := (((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).add_const (1 / 2 : ℂ)).const_mul (L : ℂ)
    simpa using h
  have h2 := (h1.cexp).mul_const R
  rw [hfun]
  convert h2 using 1 <;> try with_reducible_and_instances rfl
  simp only [IintJ]
  rw [pow_one, Iint_eq_exp F αm hαm hαN μ ν w f₀ φ0 ψ0 t p]
  ring

theorem continuous_IintJ_t (j : ℕ) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ)
    (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (p : Pspace F) :
    Continuous fun t : ℝ => IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t p := by
  unfold IintJ
  refine continuous_const.mul ?_
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_Iint F αm hαm hαN μ ν w f₀ φ0 ψ0 p t).continuousAt

theorem continuous_IintJ (j : ℕ) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
    (hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ))
    (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0) (t : ℝ) :
    Continuous (IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t) := by
  unfold IintJ
  refine Continuous.mul ?_ (continuous_Iint F αm hαm hαN μ ν hμc hνc w f₀ φ0 ψ0 hf₀ hφ0 hψ0 t)
  refine (continuous_const.mul (Complex.continuous_ofReal.comp ?_)).pow j
  exact ((NumberField.TateGlobal.continuous_ideleNorm F).comp continuous_fst.snd).log fun p => (ideleNorm_pos _).ne'

end Deriv
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Identity

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

theorem f0_insert (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (faK : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (Φ : Ent F → ℂ) (hΦ : ∀ g, faK g = Φ (archEntries F g))
    (hf : ∀ g, f₀ g = faK (glArch (𝓞 F) F g) * ff₀ (glFin (𝓞 F) F g))
    (Z : ℝ → AdelicGL2 (𝓞 F) F) (N : ℝ → Ent F) (hZN : ∀ s, archEntries F (glArch (𝓞 F) F (Z s)) = N s)
    (hZf : ∀ s, glFin (𝓞 F) F (Z s) = 1)
    (k k' : adelicMaximalCompact F) (y : AdelicGL2 (𝓞 F) F) (s : ℝ) :
    f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * (y * (Z s * (k' : AdelicGL2 (𝓞 F) F)))) =
      Φ (Matrix.of.symm (Matrix.of (archEntries F (glArch (𝓞 F) F ((k : AdelicGL2 (𝓞 F) F)⁻¹ * y))) * Matrix.of (N s) *
        Matrix.of (archEntries F (glArch (𝓞 F) F (k' : AdelicGL2 (𝓞 F) F))))) *
      ff₀ (glFin (𝓞 F) F ((k : AdelicGL2 (𝓞 F) F)⁻¹ * y) * glFin (𝓞 F) F (k' : AdelicGL2 (𝓞 F) F)) := by
  rw [hf, hΦ]
  congr 1
  · congr 1
    rw [← hZN, ← archEntries_mul3]
    congr 1
    simp only [map_mul, mul_assoc]
  · congr 1
    simp only [map_mul, hZf, one_mul, mul_assoc]

def kap (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℝ) (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F) : ℂ :=
  ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (p.1.1.2 * p.1.2) : ℂˣ) : ℂ) *
  ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) p.1.1.2 : ℂˣ) : ℂ) *
  (((NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) : ℝ) : ℂ) *
  (((NumberField.TateGlobal.ideleNorm F p.1.2)⁻¹ : ℝ) : ℂ) *
  ff₀ (glFin (𝓞 F) F ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * word3 F p) * glFin (𝓞 F) F (p.2 : AdelicGL2 (𝓞 F) F)) *
  ψ0 (p.2 : AdelicGL2 (𝓞 F) F) * conj (φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F))

theorem norm_kap_le (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (w : ℝ) (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (Bff : ℝ) (hBff : ∀ h, ‖ff₀ h‖ ≤ Bff)
    (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F) (Mb : ℝ) (hMb0 : 0 ≤ Mb)
    (hMb : (ideleNorm F p.1.2) ^ (1 / 2 : ℝ) *
      (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) ≤ Mb) :
    ‖kap F αm hαm μ ν w ff₀ φ0 ψ0 t p‖ ≤
      Mb * Bff * ((ideleNorm F p.1.2)⁻¹ * ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖) := by
  unfold kap
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_eta_pair F αm hαm hαN μ ν hμ hν,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (ideleNorm_pos _).le _), abs_of_pos (inv_pos.mpr (ideleNorm_pos _))]
  have hi : 0 ≤ (ideleNorm F p.1.2)⁻¹ := (inv_pos.mpr (ideleNorm_pos _)).le
  have hff := hBff (glFin (𝓞 F) F ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * word3 F p) * glFin (𝓞 F) F (p.2 : AdelicGL2 (𝓞 F) F))
  calc (ideleNorm F p.1.2) ^ (1 / 2 : ℝ) *
        (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) *
        (ideleNorm F p.1.2)⁻¹ *
        ‖ff₀ (glFin (𝓞 F) F ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * word3 F p) * glFin (𝓞 F) F (p.2 : AdelicGL2 (𝓞 F) F))‖ *
        ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖
      = ((ideleNorm F p.1.2) ^ (1 / 2 : ℝ) *
          (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2)) *
        ‖ff₀ (glFin (𝓞 F) F ((p.1.1.1.1 : AdelicGL2 (𝓞 F) F)⁻¹ * word3 F p) * glFin (𝓞 F) F (p.2 : AdelicGL2 (𝓞 F) F))‖ *
        ((ideleNorm F p.1.2)⁻¹ * ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖) := by ring
    _ ≤ Mb * Bff * ((ideleNorm F p.1.2)⁻¹ * ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖) := by
        refine mul_le_mul (mul_le_mul hMb hff (norm_nonneg _) hMb0) le_rfl (by positivity) (mul_nonneg hMb0 ?_)
        exact (norm_nonneg _).trans hff

theorem ident_T (v : InfinitePlace F) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (τ : ℝ)
    (hτ : ∀ x : (v.Completion)ˣ,
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar μ v x : ℂˣ) : ℂ) = ((ideleNorm F (archUnitHom v x) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
    (w : ℝ) (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (faK : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (Φ : Ent F → ℂ) (hΦ : ∀ g, faK g = Φ (archEntries F g))
    (hf : ∀ g, f₀ g = faK (glArch (𝓞 F) F g) * ff₀ (glFin (𝓞 F) F g))
    (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (ρ : ℝ → ℝ) (j : ℕ) (t s : ℝ) (p : Pspace F) :
    (ρ s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleT F (delta F v s) p) =
      Complex.exp (Complex.I * (((v.mult : ℝ) * (τ + t) : ℝ) : ℂ) * (s : ℂ)) *
      (kap F αm hαm μ ν w ff₀ φ0 ψ0 t p *
        Psi F Φ (NT F v) ρ ((v.mult : ℝ) * ((w - 1) / 2)) (v.mult : ℝ) j (parOf F p) s) := by
  obtain ⟨⟨⟨⟨k, x⟩, u⟩, t'⟩, k'⟩ := p
  have hlog : Real.log (ideleNorm F (delta F v s * t')) = (v.mult : ℝ) * s + Real.log (ideleNorm F t') := by
    rw [ideleNorm_mul, ideleNorm_delta, Real.log_mul (Real.exp_pos _).ne' (ideleNorm_pos _).ne', Real.log_exp]
  have hf0 := f0_insert F f₀ faK ff₀ Φ hΦ hf (ZT F v) (NT F v) (archEntries_glArch_ZT F v) (glFin_ZT F v) k k'
    (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t') s
  have ec : Real.exp ((v.mult : ℝ) * ((w - 1) / 2) * s) = Real.exp ((v.mult : ℝ) * s * ((w - 1) / 2)) := by
    congr 1; ring
  rw [IintJ, Iint_scaleT_delta F v αm hαm hαN μ ν τ hτ w f₀ φ0 ψ0 t s]
  simp only [scaleT, IintS, kap, Psi, parOf, word3, ZT] at hf0 ⊢
  rw [hlog, hf0, ec]
  push_cast
  ring

theorem ident_U (v : InfinitePlace F) (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (τ : ℝ)
    (hτ : ∀ x : (v.Completion)ˣ,
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar ν v x : ℂˣ) : ℂ) = ((ideleNorm F (archUnitHom v x) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
    (w : ℝ) (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (faK : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (Φ : Ent F → ℂ) (hΦ : ∀ g, faK g = Φ (archEntries F g))
    (hf : ∀ g, f₀ g = faK (glArch (𝓞 F) F g) * ff₀ (glFin (𝓞 F) F g))
    (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (ρ : ℝ → ℝ) (j : ℕ) (t s : ℝ) (p : Pspace F) :
    (ρ s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleU F (delta F v s) p) =
      Complex.exp (Complex.I * (((v.mult : ℝ) * (τ - t) : ℝ) : ℂ) * (s : ℂ)) *
      (kap F αm hαm μ ν w ff₀ φ0 ψ0 t p *
        Psi F Φ (NU F v) ρ ((v.mult : ℝ) * ((w + 1) / 2)) (-(v.mult : ℝ)) j (parOf F p) s) := by
  obtain ⟨⟨⟨⟨k, x⟩, u⟩, t'⟩, k'⟩ := p
  have hlog : Real.log (ideleNorm F ((delta F v s)⁻¹ * t')) = -(v.mult : ℝ) * s + Real.log (ideleNorm F t') := by
    rw [← delta_neg, ideleNorm_mul, ideleNorm_delta, Real.log_mul (Real.exp_pos _).ne' (ideleNorm_pos _).ne', Real.log_exp]
    ring
  have hf0 := f0_insert F f₀ faK ff₀ Φ hΦ hf (ZU F v) (NU F v) (archEntries_glArch_ZU F v) (glFin_ZU F v) k k'
    (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t') s
  have ec : Real.exp ((v.mult : ℝ) * ((w + 1) / 2) * s) = Real.exp ((v.mult : ℝ) * s * ((w + 1) / 2)) := by
    congr 1; ring
  rw [IintJ, Iint_scaleU_delta F v αm hαm hαN μ ν τ hτ w f₀ φ0 ψ0 t s]
  simp only [scaleU, IintSU, kap, Psi, parOf, word3, ZU] at hf0 ⊢
  rw [hlog, hf0, ec]
  push_cast
  ring

end Identity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section AveragingU

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

theorem continuous_scaleU_delta (v : InfinitePlace F) :
    Continuous fun q : ℝ × Pspace F => scaleU F (delta F v q.1) q.2 := by
  unfold scaleU
  have hd : Continuous fun q : ℝ × Pspace F => delta F v q.1 := (continuous_delta F v).comp continuous_fst
  have hp : Continuous fun q : ℝ × Pspace F => q.2 := continuous_snd
  refine ((((hp.fst.fst.fst.fst.prodMk hp.fst.fst.fst.snd).prodMk (hd.mul hp.fst.fst.snd)).prodMk
    (hd.inv.mul hp.fst.snd)).prodMk hp.snd)

theorem integral_comp_scaleU {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : (AdeleRing (𝓞 F) F)ˣ) (G : Pspace F → E) (hGm : AEStronglyMeasurable G (πP F)) :
    ∫ p, G (scaleU F δ p) ∂(πP F) = ∫ p, G p ∂(πP F) := by
  have h := measurePreserving_scaleU F δ
  have hG' : AEStronglyMeasurable G (Measure.map (scaleU F δ) (πP F)) := by rw [h.map_eq]; exact hGm
  have e := integral_map h.measurable.aemeasurable hG'
  rw [h.map_eq] at e
  exact e.symm

theorem integrable_comp_scaleU (δ : (AdeleRing (𝓞 F) F)ˣ) (G : Pspace F → ℂ) (hGm : AEStronglyMeasurable G (πP F))
    (hG : Integrable G (πP F)) : Integrable (fun p => G (scaleU F δ p)) (πP F) := by
  have h := measurePreserving_scaleU F δ
  have hG' : Integrable G (Measure.map (scaleU F δ) (πP F)) := by rw [h.map_eq]; exact hG
  exact (integrable_map_measure hG'.aestronglyMeasurable h.measurable.aemeasurable).mp hG'

theorem integral_eq_integral_average_U (v : InfinitePlace F) (ρ : ℝ → ℝ) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ1 : ∫ s, ρ s = 1)
    (G : Pspace F → ℂ) (hGc : Continuous G) (hG : Integrable G (πP F)) :
    ∫ p, G p ∂(πP F) = ∫ p, (∫ s : ℝ, (ρ s : ℂ) * G (scaleU F (delta F v s) p)) ∂(πP F) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := sigmaFinite_idelicHaar F
  haveI := sigmaFinite_adelicAddHaar F
  haveI : SigmaFinite (πP F) := by unfold πP; infer_instance
  have hGm : AEStronglyMeasurable G (πP F) := hG.aestronglyMeasurable
  set Φ : ℝ × Pspace F → ℂ := Function.uncurry fun (s : ℝ) (p : Pspace F) => (ρ s : ℂ) * G (scaleU F (delta F v s) p) with hΦ
  have hΦc : Continuous Φ := by
    show Continuous fun q : ℝ × Pspace F => (ρ q.1 : ℂ) * G (scaleU F (delta F v q.1) q.2)
    exact (Complex.continuous_ofReal.comp (hρc.comp continuous_fst)).mul (hGc.comp (continuous_scaleU_delta F v))
  have hΦm : AEStronglyMeasurable Φ ((volume : Measure ℝ).prod (πP F)) := hΦc.aestronglyMeasurable
  have hnorm : ∀ s : ℝ, ∫ p, ‖Φ (s, p)‖ ∂(πP F) = ‖ρ s‖ * ∫ p, ‖G p‖ ∂(πP F) := by
    intro s
    show (∫ p, ‖(ρ s : ℂ) * G (scaleU F (delta F v s) p)‖ ∂(πP F)) = _
    simp only [norm_mul, Complex.norm_real]
    rw [integral_const_mul]
    congr 1
    exact integral_comp_scaleU F (delta F v s) (fun p => ‖G p‖) hGm.norm
  have hInt : Integrable Φ ((volume : Measure ℝ).prod (πP F)) := by
    rw [integrable_prod_iff hΦm]
    constructor
    · refine ae_of_all _ fun s => ?_
      show Integrable (fun p => (ρ s : ℂ) * G (scaleU F (delta F v s) p)) (πP F)
      exact (integrable_comp_scaleU F _ G hGm hG).const_mul _
    · have e : (fun s : ℝ => ∫ p, ‖Φ (s, p)‖ ∂(πP F)) = fun s => ‖ρ s‖ * ∫ p, ‖G p‖ ∂(πP F) := funext hnorm
      rw [e]
      exact (hρc.integrable_of_hasCompactSupport hρs).norm.mul_const _
  have hswap := integral_integral_swap hInt
  have h1 : ∫ s : ℝ, ∫ p, (ρ s : ℂ) * G (scaleU F (delta F v s) p) ∂(πP F) = ∫ p, G p ∂(πP F) := by
    have e : (fun s : ℝ => ∫ p, (ρ s : ℂ) * G (scaleU F (delta F v s) p) ∂(πP F)) = fun s => (ρ s : ℂ) * ∫ p, G p ∂(πP F) := by
      funext s
      show (∫ p, (ρ s : ℂ) * G (scaleU F (delta F v s) p) ∂(πP F)) = _
      rw [integral_const_mul, integral_comp_scaleU F _ G hGm]
    rw [e, integral_mul_const, integral_complex_ofReal, hρ1, Complex.ofReal_one, one_mul]
  rw [← h1]
  exact hswap

end AveragingU
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Bound

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

def bump0 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

def rho : ℝ → ℝ := (bump0).normed volume

theorem rho_contDiff : ContDiff ℝ (⊤ : ℕ∞) rho := (bump0).contDiff_normed
theorem rho_continuous : Continuous rho := (bump0).continuous_normed
theorem rho_integral : ∫ s, rho s = 1 := (bump0).integral_normed
theorem rho_hasCompactSupport : HasCompactSupport rho := (bump0).hasCompactSupport_normed
theorem rho_tsupport : tsupport rho ⊆ Set.Icc (-2) 2 := by
  rw [rho, ContDiffBump.tsupport_normed_eq]
  intro s hs
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hs
  exact abs_le.mp hs

omit [NumberField F] in
theorem rho_eq_zero_of_not_mem {s : ℝ} (hs : s ∉ Set.Icc (-2 : ℝ) 2) : rho s = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hs (rho_tsupport h)

theorem exists_norm_IintJ_le (j : ℕ) (w : ℝ) (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ LB : ℝ, 0 ≤ LB ∧
      ∀ (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
        (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
        (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
        (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) (p : Pspace F),
      ‖IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t p‖ ≤
        LB ^ j * (C₀ * (Wset F f₀).indicator (fun _ => (1 : ℝ)) (word4 F p) * (ideleNorm F p.1.2)⁻¹ *
          ‖ψ0 (p.2 : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (p.1.1.1.1 : AdelicGL2 (𝓞 F) F)‖) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_bound_Iint F w f₀ hf₀ hf₀c
  obtain ⟨LB, hLB0, hLB⟩ := exists_bound_log_ideleNorm F (Wset F f₀) (isCompact_Wset F f₀ hf₀c)
  refine ⟨C₀, hC₀, LB, hLB0, fun αm hαm hαN μ ν hμ hν φ0 ψ0 t p => ?_⟩
  rw [norm_IintJ]
  have h2 := hbound αm hαm hαN μ ν hμ hν φ0 ψ0 t p
  by_cases hW : word4 F p ∈ Wset F f₀
  · have h1 : |Real.log (ideleNorm F p.1.2)| ^ j ≤ LB ^ j := pow_le_pow_left₀ (abs_nonneg _) (hLB p hW) j
    refine mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg hLB0 j)
  · rw [Set.indicator_of_notMem hW, mul_zero, zero_mul, zero_mul, zero_mul] at h2
    have h0 : ‖Iint F αm hαm μ ν w f₀ φ0 ψ0 t p‖ = 0 := le_antisymm h2 (norm_nonneg _)
    rw [h0, mul_zero, Set.indicator_of_notMem hW, mul_zero, zero_mul, zero_mul, zero_mul, mul_zero]

theorem integral_IintJ_props (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc_top : c ≠ ∞)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
    (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
    (hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ))
    (w : ℝ) (f₀ φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀)
    (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0) :
    (∀ (j : ℕ) (t : ℝ), Integrable (IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t) (πP F)) ∧
    (∀ t₀ : ℝ, HasDerivAt (fun t => ∫ p, Iint F αm hαm μ ν w f₀ φ0 ψ0 t p ∂(πP F))
      (∫ p, IintJ F 1 αm hαm μ ν w f₀ φ0 ψ0 t₀ p ∂(πP F)) t₀) ∧
    Continuous (fun t => ∫ p, IintJ F 1 αm hαm μ ν w f₀ φ0 ψ0 t p ∂(πP F)) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
  have hmaj : ∀ j : ℕ, ∃ bound : Pspace F → ℝ, Integrable bound (πP F) ∧
      ∀ t p, ‖IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t p‖ ≤ bound p := by
    intro j
    obtain ⟨C₀, hC₀, LB, hLB0, hle⟩ := exists_norm_IintJ_le F j w f₀ hf₀ hf₀c
    exact ⟨_, (integrable_majorant F c hc0 hc_top hc f₀ hf₀ hf₀c φ0 ψ0 hφ0 hψ0 C₀ hC₀).const_mul (LB ^ j),
      fun t p => hle αm hαm hαN μ ν hμ hν φ0 ψ0 t p⟩
  have hcont : ∀ (j : ℕ) (t : ℝ), Continuous (IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t) := fun j t =>
    continuous_IintJ F j αm hαm hαN μ ν hμc hνc w f₀ φ0 ψ0 hf₀ hφ0 hψ0 t
  have hint : ∀ (j : ℕ) (t : ℝ), Integrable (IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t) (πP F) := by
    intro j t
    obtain ⟨bound, hbi, hle⟩ := hmaj j
    exact hbi.mono' (hcont j t).aestronglyMeasurable (ae_of_all _ fun p => hle t p)
  obtain ⟨bound, hbi, hle⟩ := hmaj 1
  refine ⟨hint, fun t₀ => ?_, ?_⟩
  · have hI0 : Integrable (Iint F αm hαm μ ν w f₀ φ0 ψ0 t₀) (πP F) := by
      have e : IintJ F 0 αm hαm μ ν w f₀ φ0 ψ0 t₀ = Iint F αm hαm μ ν w f₀ φ0 ψ0 t₀ :=
        funext fun p => IintJ_zero F αm hαm μ ν w f₀ φ0 ψ0 t₀ p
      exact e ▸ hint 0 t₀
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Filter.univ_mem)
      (Eventually.of_forall fun t => (continuous_Iint F αm hαm hαN μ ν hμc hνc w f₀ φ0 ψ0 hf₀ hφ0 hψ0 t).aestronglyMeasurable)
      hI0 (hcont 1 t₀).aestronglyMeasurable (Eventually.of_forall fun p t _ => hle t p) hbi
      (Eventually.of_forall fun p t _ => hasDerivAt_Iint F αm hαm hαN μ ν w f₀ φ0 ψ0 p t)).2
  · exact continuous_of_dominated (fun t => (hcont 1 t).aestronglyMeasurable) (fun t => Eventually.of_forall fun p => hle t p)
      hbi (Eventually.of_forall fun p => continuous_IintJ_t F 1 αm hαm hαN μ ν w f₀ φ0 ψ0 p)

theorem exists_bound_weight (w : ℝ) (W : Set (AdelicGL2 (𝓞 F) F)) (hW : IsCompact W) :
    ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ p : Pspace F, word4 F p ∈ W →
      (ideleNorm F p.1.2) ^ (1 / 2 : ℝ) *
        (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F p.1.1.2 * diagOne p.1.2))) ^ (w / 2) ≤ Mb := by
  set b : AdelicGL2 (𝓞 F) F → ℝ := fun y => (NumberField.AdelicHeight.adelicHeight F y) ^ (1 / 2 : ℝ) *
    (ideleNorm F (Matrix.GeneralLinearGroup.det y)) ^ (w / 2) with hb
  have hbc : Continuous b := by
    refine Continuous.mul ?_ ?_
    · exact (NumberField.AdelicHeight.continuous_adelicHeight F).rpow_const fun y => Or.inr (by norm_num)
    · refine ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_det F)).rpow_const fun y => ?_
      exact Or.inl (ideleNorm_pos _).ne'
  obtain ⟨M, hM⟩ := hW.exists_bound_of_continuousOn hbc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun p hp => ?_⟩
  obtain ⟨⟨⟨⟨k, x⟩, u⟩, t'⟩, k'⟩ := p
  have h := hM _ hp
  have hbw : b (word4 F ((((k, x), u), t'), k')) = (ideleNorm F t') ^ (1 / 2 : ℝ) *
      (ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F u * diagOne t'))) ^ (w / 2) := by
    simp only [hb, word4]
    rw [adelicHeight_word4, ideleNorm_det_word4]
  rw [hbw] at h
  exact (le_of_abs_le h).trans (le_max_left _ _)

end Bound
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section PerPlace

set_option synthInstance.maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F]

theorem perPlace_T (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc_top : c ≠ ∞)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
    (w : ℝ) (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀)
    (faK : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (Φ : Ent F → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : ∀ g, faK g = Φ (archEntries F g))
    (hf : ∀ g, f₀ g = faK (glArch (𝓞 F) F g) * ff₀ (glFin (𝓞 F) F g))
    (Bff : ℝ) (hBff : ∀ h, ‖ff₀ h‖ ≤ Bff) (v : InfinitePlace F) (j Nn : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
        (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
        (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
        (hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
        (hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ))
        (τ : ℝ)
        (hτ : ∀ x : (v.Completion)ˣ,
          0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
          ((archLocalChar μ v x : ℂˣ) : ℂ) = ((ideleNorm F (archUnitHom v x) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
        (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0)
        (hφn : ∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) ≤ 1)
        (hψn : ∫ k, ‖ψ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) ≤ 1) (t : ℝ),
      ‖∫ p, IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t p ∂(πP F)‖ ≤ C * (1 + |(v.mult : ℝ) * (τ + t)|) ^ (-(Nn : ℝ)) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
  set W := W3 F f₀ (ZT F v) 2 with hW
  have hWc : IsCompact W := isCompact_W3 F f₀ hf₀c (ZT F v) (continuous_ZT F v) 2
  obtain ⟨L, hL0, hL⟩ := Psi_osc_bound F Φ hΦs (NT F v) (contDiff_NT F v) rho rho_contDiff 2 (by norm_num) rho_tsupport
    ((v.mult : ℝ) * ((w - 1) / 2)) (v.mult : ℝ) j (ParS F f₀ (ZT F v) 2) (isCompact_ParS F f₀ hf₀c (ZT F v) (continuous_ZT F v) 2) Nn
  obtain ⟨Mb, hMb0, hMb⟩ := exists_bound_weight F w (W4 F f₀ (ZT F v) 2) (isCompact_W4 F f₀ hf₀c _ (continuous_ZT F v) 2)
  have hBff0 : 0 ≤ Bff := (norm_nonneg _).trans (hBff 1)
  have hI : I0 F W < ∞ := lintegral_iwasawa_indicator_lt_top F c hc0 hc_top hc W hWc
  refine ⟨L * (Mb * Bff) * (I0 F W).toReal, mul_nonneg (mul_nonneg hL0 (mul_nonneg hMb0 hBff0)) ENNReal.toReal_nonneg, ?_⟩
  intro αm hαm hαN μ ν hμ hν hμc hνc τ hτ φ0 ψ0 hφ0 hψ0 hφn hψn t
  set l : ℝ := (v.mult : ℝ) * (τ + t) with hl
  obtain ⟨hint, -, -⟩ := integral_IintJ_props F c hc0 hc_top hc αm hαm hαN μ ν hμ hν hμc hνc w f₀ φ0 ψ0 hf₀ hf₀c hφ0 hψ0
  have hGc := continuous_IintJ F j αm hαm hαN μ ν hμc hνc w f₀ φ0 ψ0 hf₀ hφ0 hψ0 t
  rw [integral_eq_integral_average F v rho rho_continuous rho_hasCompactSupport rho_integral _ hGc (hint j t)]
  have hpow : 0 ≤ (1 + |l|) ^ (-(Nn : ℝ)) := Real.rpow_nonneg (by positivity) _
  set A : ℝ := L * (Mb * Bff) * (1 + |l|) ^ (-(Nn : ℝ)) with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg (by positivity) hpow
  have hinner : ∀ p : Pspace F,
      ‖∫ s : ℝ, (rho s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleT F (delta F v s) p)‖ ≤ A * G0 F W φ0 ψ0 p := by
    intro p
    obtain ⟨⟨⟨⟨k, x⟩, u⟩, t'⟩, k'⟩ := p
    by_cases hp : word3 F ((((k, x), u), t'), k') ∈ W
    · have e : ∀ s : ℝ, (rho s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleT F (delta F v s) ((((k, x), u), t'), k')) =
          kap F αm hαm μ ν w ff₀ φ0 ψ0 t ((((k, x), u), t'), k') *
            (Psi F Φ (NT F v) rho ((v.mult : ℝ) * ((w - 1) / 2)) (v.mult : ℝ) j (parOf F ((((k, x), u), t'), k')) s *
              Complex.exp (Complex.I * (l : ℂ) * (s : ℂ))) := by
        intro s
        rw [ident_T F v αm hαm hαN μ ν τ hτ w f₀ faK ff₀ Φ hΦ hf φ0 ψ0 rho j t s]
        ring
      simp_rw [e]
      rw [integral_const_mul, norm_mul]
      have h1 := hL _ (parOf_mem_ParS F _ hp) l
      have h2 := norm_kap_le F αm hαm hαN μ ν hμ hν w ff₀ Bff hBff φ0 ψ0 t ((((k, x), u), t'), k') Mb hMb0
        (hMb _ (word4_mem_W4 F _ hp))
      have hG0 : G0 F W φ0 ψ0 ((((k, x), u), t'), k') =
          (ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ := by
        simp only [G0]
        rw [Set.indicator_of_mem hp, one_mul]
      rw [hG0]
      calc ‖kap F αm hαm μ ν w ff₀ φ0 ψ0 t ((((k, x), u), t'), k')‖ *
            ‖∫ s : ℝ, Psi F Φ (NT F v) rho ((v.mult : ℝ) * ((w - 1) / 2)) (v.mult : ℝ) j (parOf F ((((k, x), u), t'), k')) s *
              Complex.exp (Complex.I * (l : ℂ) * (s : ℂ))‖
          ≤ (Mb * Bff * ((ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖)) *
            (L * (1 + |l|) ^ (-(Nn : ℝ))) :=
            mul_le_mul h2 h1 (norm_nonneg _) (mul_nonneg (mul_nonneg hMb0 hBff0)
              (mul_nonneg (mul_nonneg (inv_pos.mpr (ideleNorm_pos _)).le (norm_nonneg _)) (norm_nonneg _)))
        _ = A * ((ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖) := by
            rw [hA]; ring
    · have e : ∀ s : ℝ, (rho s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleT F (delta F v s) ((((k, x), u), t'), k')) = 0 := by
        intro s
        by_cases hs : s ∈ Set.Icc (-2 : ℝ) 2
        · have h0 : f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t' *
              (ZT F v s * (k' : AdelicGL2 (𝓞 F) F)))) = 0 := by
            by_contra h
            exact hp (mem_W3 F k k' _ s hs h)
          rw [IintJ, Iint_scaleT_delta F v αm hαm hαN μ ν τ hτ w f₀ φ0 ψ0 t s]
          simp only [IintS, ZT] at h0 ⊢
          rw [h0]
          simp
        · rw [rho_eq_zero_of_not_mem hs, Complex.ofReal_zero, zero_mul]
      simp_rw [e]
      rw [integral_zero, norm_zero]
      exact mul_nonneg hA0 (G0_nonneg F W φ0 ψ0 _)
  obtain ⟨-, hGint, hGle⟩ := integrable_G0_and_integral_le F c hc0 hc_top hc W hWc φ0 ψ0 hφ0 hψ0 hφn hψn
  calc ‖∫ p, (∫ s : ℝ, (rho s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleT F (delta F v s) p)) ∂(πP F)‖
      ≤ ∫ p, A * G0 F W φ0 ψ0 p ∂(πP F) := norm_integral_le_of_norm_le (hGint.const_mul A) (ae_of_all _ hinner)
    _ = A * ∫ p, G0 F W φ0 ψ0 p ∂(πP F) := integral_const_mul _ _
    _ ≤ A * (I0 F W).toReal := mul_le_mul_of_nonneg_left hGle hA0
    _ = L * (Mb * Bff) * (I0 F W).toReal * (1 + |l|) ^ (-(Nn : ℝ)) := by rw [hA]; ring

theorem perPlace_U (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc_top : c ≠ ∞)
    (hc : ∀ φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable φ →
        ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                φ (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
    (w : ℝ) (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀)
    (faK : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (Φ : Ent F → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : ∀ g, faK g = Φ (archEntries F g))
    (hf : ∀ g, f₀ g = faK (glArch (𝓞 F) F g) * ff₀ (glFin (𝓞 F) F g))
    (Bff : ℝ) (hBff : ∀ h, ‖ff₀ h‖ ≤ Bff) (v : InfinitePlace F) (j Nn : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
        (hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm F z)
        (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
        (hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
        (hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ))
        (τ : ℝ)
        (hτ : ∀ x : (v.Completion)ˣ,
          0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
          ((archLocalChar ν v x : ℂˣ) : ℂ) = ((ideleNorm F (archUnitHom v x) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
        (φ0 ψ0 : AdelicGL2 (𝓞 F) F → ℂ) (hφ0 : Continuous φ0) (hψ0 : Continuous ψ0)
        (hφn : ∫ k, ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) ≤ 1)
        (hψn : ∫ k, ‖ψ0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(maximalCompactHaar F) ≤ 1) (t : ℝ),
      ‖∫ p, IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t p ∂(πP F)‖ ≤ C * (1 + |(v.mult : ℝ) * (τ - t)|) ^ (-(Nn : ℝ)) := by
  haveI := secondCountableTopology_idele F
  haveI := secondCountableTopology_adele F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (adelicMaximalCompact F) := TopologicalSpace.Subtype.secondCountableTopology _
  set W := W3 F f₀ (ZU F v) 2 with hW
  have hWc : IsCompact W := isCompact_W3 F f₀ hf₀c (ZU F v) (continuous_ZU F v) 2
  obtain ⟨L, hL0, hL⟩ := Psi_osc_bound F Φ hΦs (NU F v) (contDiff_NU F v) rho rho_contDiff 2 (by norm_num) rho_tsupport
    ((v.mult : ℝ) * ((w + 1) / 2)) (-(v.mult : ℝ)) j (ParS F f₀ (ZU F v) 2) (isCompact_ParS F f₀ hf₀c (ZU F v) (continuous_ZU F v) 2) Nn
  obtain ⟨Mb, hMb0, hMb⟩ := exists_bound_weight F w (W4 F f₀ (ZU F v) 2) (isCompact_W4 F f₀ hf₀c _ (continuous_ZU F v) 2)
  have hBff0 : 0 ≤ Bff := (norm_nonneg _).trans (hBff 1)
  have hI : I0 F W < ∞ := lintegral_iwasawa_indicator_lt_top F c hc0 hc_top hc W hWc
  refine ⟨L * (Mb * Bff) * (I0 F W).toReal, mul_nonneg (mul_nonneg hL0 (mul_nonneg hMb0 hBff0)) ENNReal.toReal_nonneg, ?_⟩
  intro αm hαm hαN μ ν hμ hν hμc hνc τ hτ φ0 ψ0 hφ0 hψ0 hφn hψn t
  set l : ℝ := (v.mult : ℝ) * (τ - t) with hl
  obtain ⟨hint, -, -⟩ := integral_IintJ_props F c hc0 hc_top hc αm hαm hαN μ ν hμ hν hμc hνc w f₀ φ0 ψ0 hf₀ hf₀c hφ0 hψ0
  have hGc := continuous_IintJ F j αm hαm hαN μ ν hμc hνc w f₀ φ0 ψ0 hf₀ hφ0 hψ0 t
  rw [integral_eq_integral_average_U F v rho rho_continuous rho_hasCompactSupport rho_integral _ hGc (hint j t)]
  have hpow : 0 ≤ (1 + |l|) ^ (-(Nn : ℝ)) := Real.rpow_nonneg (by positivity) _
  set A : ℝ := L * (Mb * Bff) * (1 + |l|) ^ (-(Nn : ℝ)) with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg (by positivity) hpow
  have hinner : ∀ p : Pspace F,
      ‖∫ s : ℝ, (rho s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleU F (delta F v s) p)‖ ≤ A * G0 F W φ0 ψ0 p := by
    intro p
    obtain ⟨⟨⟨⟨k, x⟩, u⟩, t'⟩, k'⟩ := p
    by_cases hp : word3 F ((((k, x), u), t'), k') ∈ W
    · have e : ∀ s : ℝ, (rho s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleU F (delta F v s) ((((k, x), u), t'), k')) =
          kap F αm hαm μ ν w ff₀ φ0 ψ0 t ((((k, x), u), t'), k') *
            (Psi F Φ (NU F v) rho ((v.mult : ℝ) * ((w + 1) / 2)) (-(v.mult : ℝ)) j (parOf F ((((k, x), u), t'), k')) s *
              Complex.exp (Complex.I * (l : ℂ) * (s : ℂ))) := by
        intro s
        rw [ident_U F v αm hαm hαN μ ν τ hτ w f₀ faK ff₀ Φ hΦ hf φ0 ψ0 rho j t s]
        ring
      simp_rw [e]
      rw [integral_const_mul, norm_mul]
      have h1 := hL _ (parOf_mem_ParS F _ hp) l
      have h2 := norm_kap_le F αm hαm hαN μ ν hμ hν w ff₀ Bff hBff φ0 ψ0 t ((((k, x), u), t'), k') Mb hMb0
        (hMb _ (word4_mem_W4 F _ hp))
      have hG0 : G0 F W φ0 ψ0 ((((k, x), u), t'), k') =
          (ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖ := by
        simp only [G0]
        rw [Set.indicator_of_mem hp, one_mul]
      rw [hG0]
      calc ‖kap F αm hαm μ ν w ff₀ φ0 ψ0 t ((((k, x), u), t'), k')‖ *
            ‖∫ s : ℝ, Psi F Φ (NU F v) rho ((v.mult : ℝ) * ((w + 1) / 2)) (-(v.mult : ℝ)) j (parOf F ((((k, x), u), t'), k')) s *
              Complex.exp (Complex.I * (l : ℂ) * (s : ℂ))‖
          ≤ (Mb * Bff * ((ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖)) *
            (L * (1 + |l|) ^ (-(Nn : ℝ))) :=
            mul_le_mul h2 h1 (norm_nonneg _) (mul_nonneg (mul_nonneg hMb0 hBff0)
              (mul_nonneg (mul_nonneg (inv_pos.mpr (ideleNorm_pos _)).le (norm_nonneg _)) (norm_nonneg _)))
        _ = A * ((ideleNorm F t')⁻¹ * ‖ψ0 (k' : AdelicGL2 (𝓞 F) F)‖ * ‖φ0 (k : AdelicGL2 (𝓞 F) F)‖) := by
            rw [hA]; ring
    · have e : ∀ s : ℝ, (rho s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleU F (delta F v s) ((((k, x), u), t'), k')) = 0 := by
        intro s
        by_cases hs : s ∈ Set.Icc (-2 : ℝ) 2
        · have h0 : f₀ ((k : AdelicGL2 (𝓞 F) F)⁻¹ * (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t' *
              (ZU F v s * (k' : AdelicGL2 (𝓞 F) F)))) = 0 := by
            by_contra h
            exact hp (mem_W3 F k k' _ s hs h)
          rw [IintJ, Iint_scaleU_delta F v αm hαm hαN μ ν τ hτ w f₀ φ0 ψ0 t s]
          simp only [IintSU, ZU] at h0 ⊢
          rw [h0]
          simp
        · rw [rho_eq_zero_of_not_mem hs, Complex.ofReal_zero, zero_mul]
      simp_rw [e]
      rw [integral_zero, norm_zero]
      exact mul_nonneg hA0 (G0_nonneg F W φ0 ψ0 _)
  obtain ⟨-, hGint, hGle⟩ := integrable_G0_and_integral_le F c hc0 hc_top hc W hWc φ0 ψ0 hφ0 hψ0 hφn hψn
  calc ‖∫ p, (∫ s : ℝ, (rho s : ℂ) * IintJ F j αm hαm μ ν w f₀ φ0 ψ0 t (scaleU F (delta F v s) p)) ∂(πP F)‖
      ≤ ∫ p, A * G0 F W φ0 ψ0 p ∂(πP F) := norm_integral_le_of_norm_le (hGint.const_mul A) (ae_of_all _ hinner)
    _ = A * ∫ p, G0 F W φ0 ψ0 p ∂(πP F) := integral_const_mul _ _
    _ ≤ A * (I0 F W).toReal := mul_le_mul_of_nonneg_left hGle hA0
    _ = L * (Mb * Bff) * (I0 F W).toReal * (1 + |l|) ^ (-(Nn : ℝ)) := by rw [hA]; ring

end PerPlace
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

namespace Ws31
namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section Collect

variable (F : Type) [Field F] [NumberField F]

omit [Field F] [NumberField F] in

theorem rpow_neg_le_of_le_mul (a b κ : ℝ) (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ) (h : a ≤ κ * b) (N : ℕ) :
    b ^ (-(N : ℝ)) ≤ κ ^ N * a ^ (-(N : ℝ)) := by
  rw [Real.rpow_neg hb.le, Real.rpow_neg ha.le, Real.rpow_natCast, Real.rpow_natCast]
  have h1 : a ^ N ≤ (κ * b) ^ N := pow_le_pow_left₀ ha.le h N
  rw [mul_pow] at h1
  have h2 : (κ ^ N * b ^ N)⁻¹ ≤ (a ^ N)⁻¹ := inv_anti₀ (pow_pos ha N) h1
  have hκN : κ ^ N ≠ 0 := (pow_pos hκ N).ne'
  calc (b ^ N)⁻¹ = κ ^ N * (κ ^ N * b ^ N)⁻¹ := by field_simp
    _ ≤ κ ^ N * (a ^ N)⁻¹ := mul_le_mul_of_nonneg_left h2 (pow_nonneg hκ.le N)

end Collect
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

theorem main
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (_hfact : IsUnitFactorization K SK f₀ faK ff₀ fSK)
    (N' : ℕ) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ C : ℝ, 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (φf ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hφfK : ∀ s, IsArchKFinite K (φf s)) (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hφff : ∀ s, IsKfSmooth K (φf s)) (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf p.1 p.2))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g)) (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hφfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => φf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φf s (k : AdelicGL2 (𝓞 K) K) = φf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φf s (g * u) = φf s g)
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hφfty : ∀ s : ℂ, φf s ∈ archCutSubmodule K tysK) (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hφfn : ∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1),
    let a : ℝ → ℂ := fun t => ∫ k, ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
          ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K)
    let D : ℝ → ℝ := fun t => ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)
    ∃ a' : ℝ → ℂ, (∀ t : ℝ, HasDerivAt a (a' t) t) ∧ Continuous a' ∧
      ∀ t : ℝ, ‖a t‖ + ‖a' t‖ ≤ C * (1 + D t) ^ (-(N' : ℝ)) := by
  intro αm
  haveI := secondCountableTopology_idele K
  haveI := secondCountableTopology_adele K
  haveI := secondCountableTopology_gl K
  haveI : SecondCountableTopology (adelicMaximalCompact K) := TopologicalSpace.Subtype.secondCountableTopology _

  obtain ⟨c, hc0, hc_top, hc⟩ := NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa K
  obtain ⟨⟨Φ, hΦs, hΦ⟩, -⟩ := _hfact.1
  have hff : IsFinTestFactor K ff₀ := _hfact.2.1
  have hf : ∀ g, f₀ g = faK (glArch (𝓞 K) K g) * ff₀ (glFin (𝓞 K) K g) := _hfact.2.2.2.2.2
  obtain ⟨Bff, hBff⟩ := hff.1.continuous.bounded_above_of_compact_support hff.2
  have hαN : ∀ z, ((αm z : ℝˣ) : ℝ) = ideleNorm K z := fun _ => rfl

  choose CT0 hCT0p hCT0 using fun v : InfinitePlace K =>
    perPlace_T K c hc0 hc_top hc w f₀ _hf₀ _hf₀c faK ff₀ Φ hΦs hΦ hf Bff hBff v 0 N'
  choose CT1 hCT1p hCT1 using fun v : InfinitePlace K =>
    perPlace_T K c hc0 hc_top hc w f₀ _hf₀ _hf₀c faK ff₀ Φ hΦs hΦ hf Bff hBff v 1 N'
  choose CU0 hCU0p hCU0 using fun v : InfinitePlace K =>
    perPlace_U K c hc0 hc_top hc w f₀ _hf₀ _hf₀c faK ff₀ Φ hΦs hΦ hf Bff hBff v 0 N'
  choose CU1 hCU1p hCU1 using fun v : InfinitePlace K =>
    perPlace_U K c hc0 hc_top hc w f₀ _hf₀ _hf₀c faK ff₀ Φ hΦs hΦ hf Bff hBff v 1 N'
  set S : ℝ := ∑ v : InfinitePlace K, (CT0 v + CT1 v + CU0 v + CU1 v) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun v _ => by
    have := hCT0p v; have := hCT1p v; have := hCU0p v; have := hCU1p v; positivity
  have hSv : ∀ v, CT0 v + CT1 v + CU0 v + CU1 v ≤ S := fun v =>
    Finset.single_le_sum (f := fun v => CT0 v + CT1 v + CU0 v + CU1 v)
      (fun v _ => by have := hCT0p v; have := hCT1p v; have := hCU0p v; have := hCU1p v; positivity) (Finset.mem_univ v)
  set n : ℕ := Fintype.card (InfinitePlace K) with hn
  have hn1 : 1 ≤ (n : ℝ) := by
    rw [hn]; exact_mod_cast Fintype.card_pos
  refine ⟨(2 * (n : ℝ)) ^ N' * (S + 1), by positivity, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν φf ψf hφf hψf hφfK hψfK hφff hψff hφfjc hψfjc hφfhol hψfhol
    hφfKu hψfKu hφfflat hψfflat hφflev hψflev hφfty hψfty hφfn hψfn a D
  have hφ0 : Continuous (φf 0) := hφfjc.comp (continuous_const.prodMk continuous_id)
  have hψ0 : Continuous (ψf 0) := hψfjc.comp (continuous_const.prodMk continuous_id)
  obtain ⟨hint, hderiv, hcontJ⟩ :=
    integral_IintJ_props K c hc0 hc_top hc αm hαm hαN μ ν hμ hν hμc hνc w f₀ (φf 0) (ψf 0) _hf₀ _hf₀c hφ0 hψ0
  have hI : ∀ t, Integrable (Iint K αm hαm μ ν w f₀ (φf 0) (ψf 0) t) (πP K) := fun t => by
    have e : IintJ K 0 αm hαm μ ν w f₀ (φf 0) (ψf 0) t = Iint K αm hαm μ ν w f₀ (φf 0) (ψf 0) t :=
      funext fun p => IintJ_zero K αm hαm μ ν w f₀ (φf 0) (ψf 0) t p
    exact e ▸ hint 0 t
  have ha : ∀ t, a t = ∫ p, Iint K αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K) := fun t =>
    nested_eq_integral_prod K (Iint K αm hαm μ ν w f₀ (φf 0) (ψf 0) t) (hI t)
  have ha' : a = fun t => ∫ p, Iint K αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K) := funext ha
  refine ⟨fun t => ∫ p, IintJ K 1 αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K), fun t => ?_, hcontJ, fun t => ?_⟩
  · rw [ha']; exact hderiv t
  ·
    have e0 : ∫ p, Iint K αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K) = ∫ p, IintJ K 0 αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K) := by
      congr 1; funext p; exact (IintJ_zero K αm hαm μ ν w f₀ (φf 0) (ψf 0) t p).symm
    rw [ha t, e0]

    obtain ⟨v₀, -, hv₀⟩ := Finset.exists_max_image Finset.univ (fun v : InfinitePlace K => max |t + τμ v| |t - τν v|)
      Finset.univ_nonempty
    set M : ℝ := max |t + τμ v₀| |t - τν v₀| with hM
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
    have hD : D t ≤ (n : ℝ) * (2 * M) := by
      show (∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)) ≤ (n : ℝ) * (2 * M)
      have h := Finset.sum_le_card_nsmul Finset.univ (fun v : InfinitePlace K => |t + τμ v| + |t - τν v|) (2 * M)
        (fun v hv => by
          have h1 := hv₀ v hv
          have h2 : |t + τμ v| ≤ M := (le_max_left _ _).trans h1
          have h3 : |t - τν v| ≤ M := (le_max_right _ _).trans h1
          linarith)
      rwa [Finset.card_univ, nsmul_eq_mul] at h
    have hD0 : 0 ≤ D t := by
      show 0 ≤ ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)
      exact Finset.sum_nonneg fun v _ => by positivity
    have hkey : 1 + D t ≤ (2 * (n : ℝ)) * (1 + M) := by nlinarith
    have hm1 : (1 : ℝ) ≤ (v₀.mult : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (InfinitePlace.mult_pos).ne'

    have bT0 := hCT0 v₀ αm hαm hαN μ ν hμ hν hμc hνc (τμ v₀) (hτμ v₀) (φf 0) (ψf 0) hφ0 hψ0 hφfn hψfn t
    have bT1 := hCT1 v₀ αm hαm hαN μ ν hμ hν hμc hνc (τμ v₀) (hτμ v₀) (φf 0) (ψf 0) hφ0 hψ0 hφfn hψfn t
    have bU0 := hCU0 v₀ αm hαm hαN μ ν hμ hν hμc hνc (τν v₀) (hτν v₀) (φf 0) (ψf 0) hφ0 hψ0 hφfn hψfn t
    have bU1 := hCU1 v₀ αm hαm hαN μ ν hμ hν hμc hνc (τν v₀) (hτν v₀) (φf 0) (ψf 0) hφ0 hψ0 hφfn hψfn t
    have hDpos : 0 < 1 + D t := by linarith
    have hnpos : 0 < 2 * (n : ℝ) := by linarith
    have hlT : M ≤ |t + τμ v₀| → 1 + D t ≤ (2 * (n : ℝ)) * (1 + |(v₀.mult : ℝ) * (τμ v₀ + t)|) := fun h => by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (v₀.mult : ℝ)), add_comm (τμ v₀) t]
      have hx : |t + τμ v₀| ≤ (v₀.mult : ℝ) * |t + τμ v₀| := le_mul_of_one_le_left (abs_nonneg _) hm1
      have h1 : 1 + M ≤ 1 + (v₀.mult : ℝ) * |t + τμ v₀| := by linarith
      exact hkey.trans (mul_le_mul_of_nonneg_left h1 hnpos.le)
    have hlU : M ≤ |t - τν v₀| → 1 + D t ≤ (2 * (n : ℝ)) * (1 + |(v₀.mult : ℝ) * (τν v₀ - t)|) := fun h => by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (v₀.mult : ℝ)), abs_sub_comm (τν v₀) t]
      have hx : |t - τν v₀| ≤ (v₀.mult : ℝ) * |t - τν v₀| := le_mul_of_one_le_left (abs_nonneg _) hm1
      have h1 : 1 + M ≤ 1 + (v₀.mult : ℝ) * |t - τν v₀| := by linarith
      exact hkey.trans (mul_le_mul_of_nonneg_left h1 hnpos.le)
    rcases le_total |t - τν v₀| |t + τμ v₀| with hle | hle
    ·
      have hMle : M ≤ |t + τμ v₀| := max_le le_rfl hle
      have hcmp := rpow_neg_le_of_le_mul (1 + D t) (1 + |(v₀.mult : ℝ) * (τμ v₀ + t)|) (2 * (n : ℝ)) hDpos (by positivity)
        hnpos (hlT hMle) N'
      have hx0 : 0 ≤ (1 + |(v₀.mult : ℝ) * (τμ v₀ + t)|) ^ (-(N' : ℝ)) := Real.rpow_nonneg (by positivity) _
      have hy0 : 0 ≤ (1 + D t) ^ (-(N' : ℝ)) := Real.rpow_nonneg hDpos.le _
      calc ‖∫ p, IintJ K 0 αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K)‖ +
            ‖∫ p, IintJ K 1 αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K)‖
          ≤ (CT0 v₀ + CT1 v₀) * (1 + |(v₀.mult : ℝ) * (τμ v₀ + t)|) ^ (-(N' : ℝ)) := by linarith
        _ ≤ S * ((2 * (n : ℝ)) ^ N' * (1 + D t) ^ (-(N' : ℝ))) := by
            refine mul_le_mul ?_ hcmp hx0 hS0
            have := hSv v₀; have := hCU0p v₀; have := hCU1p v₀; linarith
        _ ≤ (2 * (n : ℝ)) ^ N' * (S + 1) * (1 + D t) ^ (-(N' : ℝ)) := by nlinarith [pow_nonneg hnpos.le N']
    ·
      have hMle : M ≤ |t - τν v₀| := max_le hle le_rfl
      have hcmp := rpow_neg_le_of_le_mul (1 + D t) (1 + |(v₀.mult : ℝ) * (τν v₀ - t)|) (2 * (n : ℝ)) hDpos (by positivity)
        hnpos (hlU hMle) N'
      have hx0 : 0 ≤ (1 + |(v₀.mult : ℝ) * (τν v₀ - t)|) ^ (-(N' : ℝ)) := Real.rpow_nonneg (by positivity) _
      have hy0 : 0 ≤ (1 + D t) ^ (-(N' : ℝ)) := Real.rpow_nonneg hDpos.le _
      calc ‖∫ p, IintJ K 0 αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K)‖ +
            ‖∫ p, IintJ K 1 αm hαm μ ν w f₀ (φf 0) (ψf 0) t p ∂(πP K)‖
          ≤ (CU0 v₀ + CU1 v₀) * (1 + |(v₀.mult : ℝ) * (τν v₀ - t)|) ^ (-(N' : ℝ)) := by linarith
        _ ≤ S * ((2 * (n : ℝ)) ^ N' * (1 + D t) ^ (-(N' : ℝ))) := by
            refine mul_le_mul ?_ hcmp hx0 hS0
            have := hSv v₀; have := hCT0p v₀; have := hCT1p v₀; linarith
        _ ≤ (2 * (n : ℝ)) ^ N' * (S + 1) * (1 + D t) ^ (-(N' : ℝ)) := by nlinarith [pow_nonneg hnpos.le N']

end Ws31.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31 P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization.Ws31.Unfold"

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (_hfact : IsUnitFactorization K SK f₀ faK ff₀ fSK)
    (N' : ℕ) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ C : ℝ, 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (φf ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hφfK : ∀ s, IsArchKFinite K (φf s)) (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hφff : ∀ s, IsKfSmooth K (φf s)) (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf p.1 p.2))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g)) (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hφfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => φf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φf s (k : AdelicGL2 (𝓞 K) K) = φf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φf s (g * u) = φf s g)
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hφfty : ∀ s : ℂ, φf s ∈ archCutSubmodule K tysK) (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hφfn : ∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1),
    let a : ℝ → ℂ := fun t => ∫ k, ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
          ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K)
    let D : ℝ → ℝ := fun t => ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v|)
    ∃ a' : ℝ → ℂ, (∀ t : ℝ, HasDerivAt a (a' t) t) ∧ Continuous a' ∧
      ∀ t : ℝ, ‖a t‖ + ‖a' t‖ ≤ C * (1 + D t) ^ (-(N' : ℝ)) :=
  Ws31.Unfold.main K SK ξK hξc hξt N hN tysK faK fSK w hξw f₀ _hf₀ _hf₀c ff₀ _hfact N'

end S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization (solution)
