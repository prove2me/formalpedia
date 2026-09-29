-- Prove2me | solution 1 for AutomorphicForm.constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/01193bdb-0522-5639-ab09-1e52fd2fb391

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_finite_support_pseudoEisenstein_summand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral
p2m_attr_erase "instance" "instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

section

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicBox
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "unipotentGL2 unipotentGL2_coe unipotentGL2_add constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply AdelicGL2 gl2Weyl_inv adelicWeyl weylIntertwiningIntegral weylIntertwiningIntegrand_integrable_of_re_gt_half isInducedSection_adelicHeight_cpow continuous_unipotentGL2 finite_support_pseudoEisenstein_summand"
namespace PseudoEisensteinConstantTerm
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem adelicWeyl_inv : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  unfold adelicWeyl
  rw [← map_inv, gl2Weyl_inv]

private theorem weylIntertwiningIntegral_eq (ν : Measure (AdeleRing (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    weylIntertwiningIntegral (𝓞 F) F ν φ g = ∫ x, φ (adelicWeyl (𝓞 F) F * unipotentGL2 x * g) ∂ν := by
  simp only [weylIntertwiningIntegral, adelicWeyl_inv]

variable {F}

private def bigCellFn (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : AdeleRing (𝓞 F) F → ℂ :=
  fun x => φ (adelicWeyl (𝓞 F) F * unipotentGL2 x * g)

private theorem bigCellFn_apply (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (x : AdeleRing (𝓞 F) F) :
    bigCellFn φ g x = φ (adelicWeyl (𝓞 F) F * unipotentGL2 x * g) :=
  rfl

private theorem pseudoEisenstein_unipotentGL2_mul {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (q : AdeleRing (𝓞 F) F)
    (g : AdelicGL2 (𝓞 F) F) :
    pseudoEisenstein F φ (unipotentGL2 q * g)
      = φ g + ∑' β : F, bigCellFn φ g (algebraMap F (AdeleRing (𝓞 F) F) β + q) := by
  rw [pseudoEisenstein_apply, hφ.unipotent_mul]
  congr 1
  refine tsum_congr fun β => ?_
  simp only [bigCellFn_apply, unipotentGL2_add, mul_assoc]

private def toPrincipal (β : F) : AdeleRing.principalSubgroup (𝓞 F) F :=
  ⟨algebraMap F (AdeleRing (𝓞 F) F) β, β, rfl⟩

private theorem coe_toPrincipal (β : F) : ((toPrincipal β : AdeleRing.principalSubgroup (𝓞 F) F) : AdeleRing (𝓞 F) F)
    = algebraMap F (AdeleRing (𝓞 F) F) β :=
  rfl

private theorem toPrincipal_bijective : Function.Bijective (toPrincipal (F := F)) := by
  refine ⟨fun a b h => AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h), ?_⟩
  rintro ⟨_, β, rfl⟩
  exact ⟨β, rfl⟩

private theorem countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 F) F) :=
  @Function.Surjective.countable _ _ (countable_numberField (F := F)) _ toPrincipal_bijective.2

attribute [local instance] countable_numberField countable_principalSubgroup

private theorem tsum_principal (h : AdeleRing (𝓞 F) F → ℂ) :
    ∑' β : F, h (algebraMap F (AdeleRing (𝓞 F) F) β)
      = ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F, h γ :=
  (Equiv.ofBijective _ toPrincipal_bijective).tsum_eq fun γ : AdeleRing.principalSubgroup (𝓞 F) F => h γ

private theorem tsum_principal_neg (k : AdeleRing.principalSubgroup (𝓞 F) F → ℂ) :
    ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F, k γ
      = ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F, k (-γ) :=
  ((Equiv.neg (AdeleRing.principalSubgroup (𝓞 F) F)).tsum_eq k).symm

private theorem pseudoEisenstein_unipotentGL2_mul' {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (q : AdeleRing (𝓞 F) F)
    (g : AdelicGL2 (𝓞 F) F) :
    pseudoEisenstein F φ (unipotentGL2 q * g)
      = φ g + ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F, bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q) := by
  rw [pseudoEisenstein_unipotentGL2_mul hφ, tsum_principal (fun y => bigCellFn φ g (y + q)),
    tsum_principal_neg (fun γ : AdeleRing.principalSubgroup (𝓞 F) F => bigCellFn φ g (γ + q))]
  simp only [AddSubgroup.coe_neg]

private theorem measurable_tsum_of_forall_hasFiniteSupport {ι α : Type*} [Countable ι] [MeasurableSpace α]
    (f : ι → α → ℂ) (hf : ∀ i, Measurable (f i))
    (hfin : ∀ a, (Function.support fun i => f i a).Finite) : Measurable fun a => ∑' i, f i a := by
  refine measurable_of_tendsto_metrizable' (f := fun s : Finset ι => fun a => ∑ i ∈ s, f i a)
    (Filter.atTop : Filter (Finset ι)) (fun s => Finset.measurable_sum s fun i _ => hf i) ?_
  rw [tendsto_pi_nhds]
  intro a
  have hs : Summable fun i => f i a := summable_of_hasFiniteSupport (hfin a)
  exact hs.hasSum

private theorem finite_support_principal_translates {φ : AdelicGL2 (𝓞 F) F → ℂ} (g : AdelicGL2 (𝓞 F) F)
    (hLF : ∀ g' : AdelicGL2 (𝓞 F) F, (Function.support fun β : F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g')).Finite)
    (q : AdeleRing (𝓞 F) F) :
    (Function.support fun γ : AdeleRing.principalSubgroup (𝓞 F) F =>
      bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q)).Finite := by
  refine ((hLF (unipotentGL2 q * g)).image fun β => -toPrincipal β).subset ?_
  intro γ hγ
  obtain ⟨β, hβ⟩ := toPrincipal_bijective.2 (-γ)
  refine ⟨β, ?_, by show -toPrincipal β = γ; rw [hβ, neg_neg]⟩
  have hβ' : -(γ : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) β := by
    rw [← coe_toPrincipal, hβ, AddSubgroup.coe_neg]
  simp only [Function.mem_support] at hγ ⊢
  rw [bigCellFn_apply, hβ', unipotentGL2_add, ← mul_assoc] at hγ
  rwa [← mul_assoc]

private theorem constantTerm_cond_pseudoEisenstein {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (g : AdelicGL2 (𝓞 F) F)
    (hLF : ∀ g' : AdelicGL2 (𝓞 F) F, (Function.support fun β : F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g')).Finite)
    (hfm : Measurable (bigCellFn φ g))
    (hint : Integrable (bigCellFn φ g) (adelicAddHaar (𝓞 F) F)) :
    constantTerm ((adelicAddHaar (𝓞 F) F)[|adelicBox F]) unipotentGL2 (pseudoEisenstein F φ) g
      = φ g + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  set μ := adelicAddHaar (𝓞 F) F with hμ
  haveI : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) μ :=
    inferInstanceAs (VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F)
      (adelicAddHaar (𝓞 F) F))
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F) μ :=
    isAddFundamentalDomain_adelicBox F μ
  have hfγ : ∀ γ : AdeleRing.principalSubgroup (𝓞 F) F,
      Measurable fun x => bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + x) :=
    fun γ => hfm.comp (measurable_const_add _)

  have hnorm : ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F,
      ∫⁻ x in adelicBox F, ‖bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + x)‖ₑ ∂μ ≠ ⊤ := by
    have h := hFD.lintegral_eq_tsum' fun x => ‖bigCellFn φ g x‖ₑ
    exact ne_of_eq_of_ne h.symm hint.2.ne
  haveI : IsFiniteMeasure (μ.restrict (adelicBox F)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact adelicAddHaar_adelicBox_lt_top F⟩

  have hS : Integrable (fun q => ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F,
      bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q)) (μ.restrict (adelicBox F)) := by
    refine ⟨(measurable_tsum_of_forall_hasFiniteSupport _ hfγ
      (finite_support_principal_translates g hLF)).aestronglyMeasurable, ?_⟩
    have hbound : ∀ q : AdeleRing (𝓞 F) F,
        ‖∑' γ : AdeleRing.principalSubgroup (𝓞 F) F, bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q)‖ₑ
          ≤ ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F,
              ‖bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q)‖ₑ := by
      intro q
      have hsn : Summable fun γ : AdeleRing.principalSubgroup (𝓞 F) F =>
          ‖bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q)‖₊ :=
        summable_of_hasFiniteSupport
          ((finite_support_principal_translates g hLF q).subset
            (Function.support_comp_subset nnnorm_zero _))
      simp only [enorm_eq_nnnorm]
      rw [← ENNReal.coe_tsum hsn]
      exact ENNReal.coe_le_coe.mpr (nnnorm_tsum_le hsn)
    show ∫⁻ q, ‖∑' γ : AdeleRing.principalSubgroup (𝓞 F) F,
        bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q)‖ₑ ∂(μ.restrict (adelicBox F)) < ⊤
    calc ∫⁻ q, ‖∑' γ : AdeleRing.principalSubgroup (𝓞 F) F,
            bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q)‖ₑ ∂(μ.restrict (adelicBox F))
        ≤ ∫⁻ q, ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F,
            ‖bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + q)‖ₑ ∂(μ.restrict (adelicBox F)) :=
          lintegral_mono hbound
      _ = ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F,
            ∫⁻ x in adelicBox F, ‖bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + x)‖ₑ ∂μ :=
          lintegral_tsum fun γ => (hfγ γ).enorm.aemeasurable
      _ < ⊤ := lt_top_iff_ne_top.mpr hnorm

  have hre : ∀ x : AdeleRing (𝓞 F) F,
      ∑' γ : AdeleRing.principalSubgroup (𝓞 F) F, bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + x)
        = ∑' β : F, bigCellFn φ g (x + algebraMap F (AdeleRing (𝓞 F) F) β) := by
    intro x
    rw [tsum_principal (fun y => bigCellFn φ g (x + y)),
      tsum_principal_neg (fun γ : AdeleRing.principalSubgroup (𝓞 F) F => bigCellFn φ g (x + γ))]
    refine tsum_congr fun γ => ?_
    rw [AddSubgroup.coe_neg, add_comm]

  unfold constantTerm constantTermIntegrand
  simp_rw [pseudoEisenstein_unipotentGL2_mul' hφ]
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_add (integrable_const _) hS, integral_const]
  have hunf : ∫ x in adelicBox F, (∑' γ : AdeleRing.principalSubgroup (𝓞 F) F,
      bigCellFn φ g (-(γ : AdeleRing (𝓞 F) F) + x)) ∂μ = ∫ x, bigCellFn φ g x ∂μ := by
    simp_rw [hre]
    exact NumberField.AdelicBox.setIntegral_adelicBox_tsum_add_algebraMap F (bigCellFn φ g) hint
  rw [hunf, weylIntertwiningIntegral_eq]
  have hvol : (((μ (adelicBox F)).toReal : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos F).ne'
      (adelicAddHaar_adelicBox_lt_top F).ne).ne'
  rw [measureReal_restrict_apply_univ, measureReal_def, ENNReal.toReal_inv, Complex.real_smul,
    Complex.real_smul, Complex.ofReal_inv]
  show ((μ (adelicBox F)).toReal : ℂ)⁻¹ * ((μ (adelicBox F)).toReal * φ g + ∫ x, bigCellFn φ g x ∂μ)
    = φ g + ((μ (adelicBox F)).toReal : ℂ)⁻¹ * ∫ x, bigCellFn φ g x ∂μ
  field_simp

end AutomorphicForm.PseudoEisensteinConstantTerm

end

end

section

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.TateGlobal NumberField.AdelicHeight

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "unipotentGL2 unipotentGL2_coe unipotentGL2_add constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply AdelicGL2 gl2Weyl_inv adelicWeyl weylIntertwiningIntegral weylIntertwiningIntegrand_integrable_of_re_gt_half isInducedSection_adelicHeight_cpow continuous_unipotentGL2 finite_support_pseudoEisenstein_summand"
namespace PseudoEisensteinConstantTerm
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

private theorem det_unipotentGL2_eq_one (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]

private theorem ideleNorm_det_bigCell (g : AdelicGL2 (𝓞 F) F) (x : AdeleRing (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (adelicWeyl (𝓞 F) F * unipotentGL2 x * g))
      = ideleNorm F (Matrix.GeneralLinearGroup.det (adelicWeyl (𝓞 F) F))
          * ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, map_mul, det_unipotentGL2_eq_one, mul_one, ideleNorm_mul]

private theorem measurable_bigCellFn {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (g : AdelicGL2 (𝓞 F) F) :
    Measurable (bigCellFn φ g) :=
  hφ.measurable.comp ((continuous_const.mul continuous_unipotentGL2).mul continuous_const).measurable

variable (F)

private def heightSection (h : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((adelicHeight F h : ℝ) : ℂ) ^ ((1 : ℂ) + 1 / 2)

private theorem continuous_heightSection : Continuous (heightSection F) :=
  (Complex.continuous_ofReal.comp (continuous_adelicHeight F)).cpow continuous_const fun h =>
    Complex.ofReal_mem_slitPlane.mpr (adelicHeight_pos h)

private theorem norm_heightSection (h : AdelicGL2 (𝓞 F) F) :
    ‖heightSection F h‖ = adelicHeight F h ^ (3 / 2 : ℝ) := by
  unfold heightSection
  have h32 : ((1 : ℂ) + 1 / 2) = ((3 / 2 : ℝ) : ℂ) := by push_cast; norm_num
  rw [h32, Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos h), Complex.ofReal_re]

private theorem integrable_heightSection_bigCell (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun x : AdeleRing (𝓞 F) F => heightSection F (adelicWeyl (𝓞 F) F * unipotentGL2 x * g))
      (adelicAddHaar (𝓞 F) F) := by
  have hflat := isInducedSection_adelicHeight_cpow F
  obtain ⟨hα, hone, hsec⟩ := hflat
  have h := weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 hone hone 1 (by norm_num)
    (heightSection F) (hsec hα 1) (continuous_heightSection F) g
  simpa only [adelicWeyl_inv F] using h

variable {F}

private theorem integrable_bigCellFn {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (bigCellFn φ g) (adelicAddHaar (𝓞 F) F) := by
  obtain ⟨a, b, ha, hband⟩ := hφ.height_band
  have hd : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det (adelicWeyl (𝓞 F) F))
      * ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    mul_pos (ideleNorm_pos _) (ideleNorm_pos _)
  obtain ⟨C, hC⟩ := hφ.bounded_on_slab _ _ hd
  have hapos : 0 < a ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
  set K : ℝ := max C 0 / a ^ (3 / 2 : ℝ) with hK
  have hK0 : 0 ≤ K := div_nonneg (le_max_right _ _) hapos.le
  refine ((integrable_heightSection_bigCell F g).norm.const_mul K).mono'
    (measurable_bigCellFn hφ g).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_heightSection]
  by_cases hz : bigCellFn φ g x = 0
  · rw [hz, norm_zero]
    exact mul_nonneg hK0 (Real.rpow_nonneg (adelicHeight_pos _).le _)
  · have hmem := hband _ hz
    have hCx : ‖bigCellFn φ g x‖ ≤ C :=
      hC _ ⟨(ideleNorm_det_bigCell g x).ge, (ideleNorm_det_bigCell g x).le⟩
    calc ‖bigCellFn φ g x‖ ≤ max C 0 := hCx.trans (le_max_left _ _)
      _ = K * a ^ (3 / 2 : ℝ) := by rw [hK, div_mul_cancel₀ _ hapos.ne']
      _ ≤ K * adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 x * g) ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hmem.1 (by norm_num)) hK0

end AutomorphicForm.PseudoEisensteinConstantTerm

end

end

section

set_option autoImplicit false

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral.AutomorphicForm"
open NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F]
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (_hφ : AutomorphicForm.IsSlabProfile F Z ξ φ)
    (g : AdelicGL2 (𝓞 F) F) :
    letI := adeleBorel (𝓞 F) F
    constantTerm (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
        unipotentGL2 (AutomorphicForm.pseudoEisenstein F φ) g
      = φ g + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  exact PseudoEisensteinConstantTerm.constantTerm_cond_pseudoEisenstein _hφ g
    (fun g' => finite_support_pseudoEisenstein_summand F Z ξ φ _hφ g')
    (PseudoEisensteinConstantTerm.measurable_bigCellFn _hφ g)
    (PseudoEisensteinConstantTerm.integrable_bigCellFn _hφ g)

end

end

end S_AutomorphicForm_constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral
end P2MW
export P2MW.S_AutomorphicForm_constantTerm_pseudoEisenstein_eq_add_weylIntertwiningIntegral (solution)
