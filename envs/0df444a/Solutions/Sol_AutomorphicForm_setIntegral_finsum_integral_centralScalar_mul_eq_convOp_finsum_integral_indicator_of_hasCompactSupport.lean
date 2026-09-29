-- Prove2me | solution 1 for AutomorphicForm.setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/829fe2e0-3091-5b49-b9b3-91c9d6a714dd

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
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
import Theorems.Thm_AutomorphicForm_finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Oper25

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

theorem secondCountableTopology_units : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem secondCountableTopology_gl : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

theorem isHaarMeasure_glHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  have : centralScalar (𝓞 K) K z ∈ Subgroup.center (AdelicGL2 (𝓞 K) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨z, rfl⟩
  exact ((Subgroup.mem_center_iff.mp this) g).symm

theorem globalPoints_scalar_eq_centralScalar (a : Kˣ) :
    globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  apply Units.ext
  ext i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) =
    (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem exists_globalPoints_out_inv_inv (q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) :
    ∃ a : Kˣ, (globalPoints (𝓞 K) K (q⁻¹).out)⁻¹ =
      globalPoints (𝓞 K) K q.out *
        centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  have h : (QuotientGroup.mk (q.out⁻¹) : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) = QuotientGroup.mk (q⁻¹).out := by
    rw [QuotientGroup.mk_inv, QuotientGroup.out_eq', QuotientGroup.out_eq']
  rw [QuotientGroup.eq] at h
  obtain ⟨b, hb⟩ := (Matrix.GeneralLinearGroup.center_eq_range_scalar (n := Fin 2) (R := K)).le h

  refine ⟨b⁻¹, ?_⟩
  rw [inv_inv] at hb
  have hrep : (q⁻¹).out = (q.out)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) b := by
    rw [hb, inv_mul_cancel_left]
  rw [hrep, ← map_inv (globalPoints (𝓞 K) K), mul_inv_rev, inv_inv, map_mul,
    ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)) b, globalPoints_scalar_eq_centralScalar, centralScalar_comm]

noncomputable def xiTop (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ where
  toFun z := ξ ⟨z, Subgroup.mem_top z⟩
  map_one' := by exact map_one ξ
  map_mul' a b := by rw [← map_mul]; rfl

theorem xiTop_apply (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    xiTop K ξ z = ξ ⟨z, Subgroup.mem_top z⟩ := rfl

theorem term_inv_eq
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (x u : AdelicGL2 (𝓞 K) K) (q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) :
    ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
        f (x⁻¹ * (globalPoints (𝓞 K) K (q⁻¹).out)⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)) ∂νZK =
      ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        f (x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K z * u)) ∂νZK := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : νZK.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular νZK
  obtain ⟨a, ha⟩ := exists_globalPoints_out_inv_inv K q
  set ι := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)) with hι

  have harg : ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      x⁻¹ * (globalPoints (𝓞 K) K (q⁻¹).out)⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u) =
        x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K (ι a * w⁻¹) * u) := by
    intro w
    rw [ha, map_mul, ← map_inv]
    group
  simp_rw [harg]

  have hxi : ∀ w : (AdeleRing (𝓞 K) K)ˣ, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) =
      ((xiTop K ξK w⁻¹ : ℂˣ) : ℂ) := by
    intro w; rw [map_inv, xiTop_apply]
  simp_rw [hxi]

  have step1 := integral_inv_eq_self
    (fun w : (AdeleRing (𝓞 K) K)ˣ => ((xiTop K ξK w : ℂˣ) : ℂ) *
      f (x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K (ι a * w) * u))) νZK
  rw [step1]

  have hprin : ((ξK ⟨(ι a)⁻¹, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = 1 := by
    rw [hξt _ ⟨a⁻¹, map_inv ι a⟩, Units.val_one]
  have step2 := integral_mul_left_eq_self (μ := νZK)
    (fun w : (AdeleRing (𝓞 K) K)ˣ => ((xiTop K ξK ((ι a)⁻¹ * w) : ℂˣ) : ℂ) *
      f (x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K w * u))) (ι a)
  simp only [inv_mul_cancel_left] at step2
  rw [step2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [map_mul, Units.val_mul, xiTop_apply]
  rw [hprin, one_mul]

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hcoe : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        (z : AdeleRing (𝓞 K) K) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    intro z
    show ((Units.map (Matrix.scalar (Fin 2)).toMonoidHom z : (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ˣ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = _
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (Units.continuous_val.smul continuous_const).congr fun z => (hcoe z).symm
  · refine ((Units.continuous_val.comp continuous_inv).smul
      (continuous_const (y := (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))))).congr fun z => ?_
    show _ = ((↑(centralScalar (𝓞 K) K z)⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))
    rw [← map_inv]
    exact (hcoe z⁻¹).symm

theorem integrable_prod_of_bdd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X × Y → ℂ) (hF : Measurable F) (A : Set X) (B : Set Y) (hA : μ A < ⊤) (hB : ν B < ⊤)
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ A ∧ p.2 ∈ B) (M : ℝ) (hM : ∀ p, ‖F p‖ ≤ M) :
    Integrable F (μ.prod ν) := by
  have hsub : Function.support F ⊆ A ×ˢ B := fun p hp => hsupp p hp
  rw [← integrableOn_iff_integrable_of_support_subset hsub]
  refine Measure.integrableOn_of_bounded (M := M) ?_ hF.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  refine ne_of_lt (lt_of_le_of_lt (Measure.prod_prod_le A B) ?_)
  exact ENNReal.mul_lt_top hA hB

variable [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
  (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
  (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
  (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
  (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
    z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
      ξK ⟨z, Subgroup.mem_top z⟩ = 1)
  (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
  (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
  (Ψ₀ : AdelicGL2 (𝓞 K) K → ℂ) (hΨ₀m : Measurable Ψ₀)
  (CΨ : Set (AdelicGL2 (𝓞 K) K)) (hCΨ : IsCompact CΨ) (hΨ₀C : ∀ y ∉ CΨ, Ψ₀ y = 0)
  (BΨ : ℝ) (hΨ₀b : ∀ y, ‖Ψ₀ y‖ ≤ BΨ)
  (x : AdelicGL2 (𝓞 K) K)

include hξc in
theorem continuous_xi_inv :
    Continuous fun w : (AdeleRing (𝓞 K) K)ˣ => (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) := by
  have : (fun w : (AdeleRing (𝓞 K) K)ˣ => (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ)) =
      fun w => (((ξK ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ))⁻¹ := by
    funext w; rw [Units.val_inv_eq_inv_val]
  rw [this]
  exact hξc.inv₀ fun w => Units.ne_zero _

include hξu in
theorem norm_xi_inv (w : (AdeleRing (𝓞 K) K)ˣ) : ‖(((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
  rw [Units.val_inv_eq_inv_val, norm_inv, hξu, inv_one]

include hξc hξu hf hfc hΨ₀m hCΨ hΨ₀C hΨ₀b in

theorem perClass (q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K))
    (S : Set (AdeleRing (𝓞 K) K)ˣ) (hS : IsCompact S)
    (hSw : ∀ w : (AdeleRing (𝓞 K) K)ˣ, (∃ g, f g ≠ 0 ∧
        Ψ₀ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g))) ≠ 0) → w ∈ S) :
    Integrable (fun g : AdelicGL2 (𝓞 K) K => (∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
        Ψ₀ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g))) ∂νZK) * f g)
      (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
    Integrable (fun u : AdelicGL2 (𝓞 K) K => Ψ₀ u * ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
        f (x⁻¹ * (globalPoints (𝓞 K) K q.out)⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)) ∂νZK)
      (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
    ∫ g, (∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
        Ψ₀ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g))) ∂νZK) * f g
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ u, Ψ₀ u * ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
        f (x⁻¹ * (globalPoints (𝓞 K) K q.out)⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)) ∂νZK
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set γ := globalPoints (𝓞 K) K q.out with hγ
  set Cf := tsupport f with hCf
  have hCfc : IsCompact Cf := hfc
  obtain ⟨Bf, hBf⟩ := hfc.exists_bound_of_continuous hf
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf 1)
  have hBΨ0 : 0 ≤ BΨ := (norm_nonneg _).trans (hΨ₀b 1)
  have hxi_m : Measurable fun w : (AdeleRing (𝓞 K) K)ˣ => (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) :=
    (continuous_xi_inv K ξK hξc).measurable

  set F : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ → ℂ := fun p =>
    (((ξK ⟨p.2, Subgroup.mem_top p.2⟩)⁻¹ : ℂˣ) : ℂ) * Ψ₀ (centralScalar (𝓞 K) K p.2 * (γ * (x * p.1))) * f p.1 with hF
  have hFm : Measurable F := by
    refine ((hxi_m.comp measurable_snd).mul (hΨ₀m.comp ?_)).mul (hf.measurable.comp measurable_fst)
    exact (((continuous_centralScalar K).comp continuous_snd).mul
      (continuous_const.mul (continuous_const.mul continuous_fst))).measurable
  have hFi : Integrable F (μ.prod νZK) := by
    refine integrable_prod_of_bdd μ νZK F hFm Cf S hCfc.measure_lt_top hS.measure_lt_top ?_ (1 * BΨ * Bf) ?_
    · rintro ⟨g, w⟩ hp
      have hfg : f g ≠ 0 := fun h => hp (by simp [hF, h])
      have hΨ : Ψ₀ (centralScalar (𝓞 K) K w * (γ * (x * g))) ≠ 0 := fun h => hp (by simp [hF, h])
      exact ⟨subset_tsupport f hfg, hSw w ⟨g, hfg, hΨ⟩⟩
    · rintro ⟨g, w⟩
      simp only [hF, norm_mul]
      rw [norm_xi_inv K ξK hξu]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hΨ₀b _) zero_le_one) (hBf g) (norm_nonneg _)
        (mul_nonneg zero_le_one hBΨ0)

  set G' : (AdeleRing (𝓞 K) K)ˣ × AdelicGL2 (𝓞 K) K → ℂ := fun p =>
    (((ξK ⟨p.1, Subgroup.mem_top p.1⟩)⁻¹ : ℂˣ) : ℂ) *
      f (x⁻¹ * γ⁻¹ * ((centralScalar (𝓞 K) K p.1)⁻¹ * p.2)) * Ψ₀ p.2 with hG'
  have hG'm : Measurable G' := by
    refine ((hxi_m.comp measurable_fst).mul (hf.measurable.comp ?_)).mul (hΨ₀m.comp measurable_snd)
    exact (continuous_const.mul (((continuous_centralScalar K).comp continuous_fst).inv.mul continuous_snd)).measurable
  have hG'i : Integrable G' (νZK.prod μ) := by
    refine integrable_prod_of_bdd νZK μ G' hG'm S CΨ hS.measure_lt_top hCΨ.measure_lt_top ?_ (1 * Bf * BΨ) ?_
    · rintro ⟨w, u⟩ hp
      have hfg : f (x⁻¹ * γ⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)) ≠ 0 := fun h => hp (by simp [hG', h])
      have hΨ : Ψ₀ u ≠ 0 := fun h => hp (by simp [hG', h])
      refine ⟨hSw w ⟨x⁻¹ * γ⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u), hfg, ?_⟩, ?_⟩
      · have : centralScalar (𝓞 K) K w * (γ * (x * (x⁻¹ * γ⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)))) = u := by group
        rw [this]; exact hΨ
      · by_contra hu; exact hΨ (hΨ₀C u hu)
    · rintro ⟨w, u⟩
      simp only [hG', norm_mul]
      rw [norm_xi_inv K ξK hξu]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hBf _) zero_le_one) (hΨ₀b u) (norm_nonneg _)
        (mul_nonneg zero_le_one hBf0)
  refine ⟨?_, ?_, ?_⟩
  ·
    have := hFi.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hF]
    rw [← integral_mul_const]
  · refine (hG'i.integral_prod_right).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hG']
    rw [integral_mul_const, mul_comm]
  ·
    calc ∫ g, (∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
            Ψ₀ (centralScalar (𝓞 K) K w * (γ * (x * g))) ∂νZK) * f g ∂μ
        = ∫ g, ∫ w, F (g, w) ∂νZK ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          simp only [hF]
          rw [← integral_mul_const]
      _ = ∫ w, ∫ g, F (g, w) ∂μ ∂νZK := integral_integral_swap hFi
      _ = ∫ w, ∫ u, G' (w, u) ∂μ ∂νZK := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          simp only [hF, hG']

          have hsub := integral_mul_left_eq_self (μ := μ)
            (fun u : AdelicGL2 (𝓞 K) K => (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              f (x⁻¹ * γ⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)) * Ψ₀ u)
            (centralScalar (𝓞 K) K w * γ * x)
          rw [← hsub]
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          dsimp only
          have e1 : x⁻¹ * γ⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * (centralScalar (𝓞 K) K w * γ * x * g)) = g := by group
          have e2 : centralScalar (𝓞 K) K w * γ * x * g = centralScalar (𝓞 K) K w * (γ * (x * g)) := by group
          rw [e1, e2]
          ring
      _ = ∫ u, ∫ w, G' (w, u) ∂νZK ∂μ := integral_integral_swap hG'i
      _ = ∫ u, Ψ₀ u * ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
            f (x⁻¹ * γ⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)) ∂νZK ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only [hG']
          rw [mul_comm (Ψ₀ u), ← integral_mul_const]

theorem countable_quot : Countable (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) := by
  haveI : Countable K := by
    haveI : Countable K := Countable.of_equiv _ (Module.Free.chooseBasis ℚ K).equivFun.toEquiv.symm
    infer_instance
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (GL (Fin 2) K) := Function.Injective.countable (f := (Units.val : GL (Fin 2) K → _)) Units.val_injective
  exact Function.Surjective.countable (QuotientGroup.mk_surjective)

include hξc hξt hξu hf hfc hΨ₀m hCΨ hΨ₀C hΨ₀b in
theorem core :
    ∫ y, (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K z * y)) ∂νZK) * Ψ₀ y
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g, (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              Ψ₀ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g))) ∂νZK) * f g
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Cf := tsupport f with hCf
  have hCfc : IsCompact Cf := hfc
  set Cy : Set (AdelicGL2 (𝓞 K) K) := (fun g => x * g) '' Cf with hCy
  have hCyc : IsCompact Cy := hCfc.image (continuous_const.mul continuous_id)

  have hQfin := AutomorphicForm.finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
    K CΨ {1} Cy hCΨ isCompact_singleton hCyc
  set Q : Finset (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) := hQfin.toFinset with hQ
  have hmemQ : ∀ (q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) (g : AdelicGL2 (𝓞 K) K) (w : (AdeleRing (𝓞 K) K)ˣ),
      g ∈ Cf → centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g)) ∈ CΨ → q ∈ Q := by
    intro q g w hg hmem
    rw [hQ, Set.Finite.mem_toFinset]
    refine ⟨1, rfl, x * g, ⟨g, hg, rfl⟩, w, ?_⟩
    rw [inv_one, one_mul, ← mul_assoc, ← centralScalar_comm, mul_assoc]
    exact hmem

  have hS : ∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), ∃ S : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact S ∧
      ∀ w : (AdeleRing (𝓞 K) K)ˣ, (∃ g, f g ≠ 0 ∧
        Ψ₀ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g))) ≠ 0) → w ∈ S := by
    intro q
    obtain ⟨S, hSc, hSw⟩ :=
      AutomorphicForm.exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact
        K CΨ {1} Cy hCΨ isCompact_singleton hCyc q.out
    refine ⟨S, hSc, fun w ⟨g, hfg, hΨ⟩ => hSw w ⟨1, rfl, x * g, ⟨g, subset_tsupport f hfg, rfl⟩, ?_⟩⟩
    rw [inv_one, one_mul, ← mul_assoc, ← centralScalar_comm, mul_assoc]
    by_contra h; exact hΨ (hΨ₀C _ h)
  choose S hSc hSw using hS
  have hPC := fun q => perClass K νZK ξK hξc hξu f hf hfc Ψ₀ hΨ₀m CΨ hCΨ hΨ₀C BΨ hΨ₀b x q (S q) (hSc q) (hSw q)

  set B : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) → AdelicGL2 (𝓞 K) K → ℂ := fun q g =>
    ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
      Ψ₀ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g))) ∂νZK with hB
  set T' : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) → AdelicGL2 (𝓞 K) K → ℂ := fun q u =>
    ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
      f (x⁻¹ * (globalPoints (𝓞 K) K q.out)⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)) ∂νZK with hT'
  set T : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) → AdelicGL2 (𝓞 K) K → ℂ := fun q u =>
    ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      f (x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K z * u)) ∂νZK with hT

  have hA : ∀ g, (∑ᶠ q, B q g) * f g = (∑ q ∈ Q, B q g) * f g := by
    intro g
    by_cases hfg : f g = 0
    · rw [hfg, mul_zero, mul_zero]
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro q hq
    rw [Function.mem_support] at hq

    by_contra hqQ
    apply hq
    simp only [hB]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
    have : Ψ₀ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g))) = 0 := by
      by_contra hne
      exact hqQ (Finset.mem_coe.2 (hmemQ q g w (subset_tsupport f hfg) (by by_contra h; exact hne (hΨ₀C _ h))))
    simp [this]

  have hBsupp : ∀ u, Ψ₀ u * ∑ᶠ q, T' q u = Ψ₀ u * ∑ q ∈ Q, T' q u := by
    intro u
    by_cases hu : Ψ₀ u = 0
    · rw [hu, zero_mul, zero_mul]
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro q hq
    rw [Function.mem_support] at hq
    by_contra hqQ
    apply hq
    simp only [hT']
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
    have : f (x⁻¹ * (globalPoints (𝓞 K) K q.out)⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)) = 0 := by
      by_contra hne
      apply hqQ (Finset.mem_coe.2 (hmemQ q _ w (subset_tsupport f hne) ?_))
      have : centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out *
          (x * (x⁻¹ * (globalPoints (𝓞 K) K q.out)⁻¹ * ((centralScalar (𝓞 K) K w)⁻¹ * u)))) = u := by group
      rw [this]
      by_contra h; exact hu (hΨ₀C u h)
    simp [this]

  have hsymm : ∀ u, ∑ᶠ q, T' q u = ∑ᶠ q, T q u := by
    intro u
    rw [← finsum_comp_equiv (Equiv.inv (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)))]
    refine finsum_congr fun q => ?_
    simp only [hT', hT, Equiv.inv_apply]
    exact term_inv_eq K νZK ξK hξt f x u q

  symm
  calc ∫ g, (∑ᶠ q, B q g) * f g ∂μ
      = ∫ g, ∑ q ∈ Q, B q g * f g ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        dsimp only
        rw [hA g, Finset.sum_mul]
    _ = ∑ q ∈ Q, ∫ g, B q g * f g ∂μ := integral_finsetSum Q fun q _ => (hPC q).1
    _ = ∑ q ∈ Q, ∫ u, Ψ₀ u * T' q u ∂μ := Finset.sum_congr rfl fun q _ => (hPC q).2.2
    _ = ∫ u, ∑ q ∈ Q, Ψ₀ u * T' q u ∂μ := (integral_finsetSum Q fun q _ => (hPC q).2.1).symm
    _ = ∫ u, (∑ᶠ q, T q u) * Ψ₀ u ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        rw [← Finset.mul_sum, ← hBsupp u, hsymm u, mul_comm]

omit [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] in
theorem nullMeasurableSet_of_restrict {X : Type*} [MeasurableSpace X] (m : Measure X) {s t : Set X}
    (ht : MeasurableSet t) (hst : s ⊆ t) (hs : NullMeasurableSet s (m.restrict t)) : NullMeasurableSet s m := by
  obtain ⟨s', hsub, hs'm, hs'ae⟩ := hs.exists_measurable_superset_ae_eq
  have h1 : (m.restrict t) (s' \ s) = 0 := (ae_eq_set.1 hs'ae).1
  rw [Measure.restrict_apply' ht] at h1
  have hae : s =ᵐ[m] (s' ∩ t : Set X) := by
    rw [ae_eq_set]
    constructor
    · have : s \ (s' ∩ t) = ∅ := Set.diff_eq_empty.2 fun y hy => ⟨hsub hy, hst hy⟩
      rw [this, measure_empty]
    · refine measure_mono_null ?_ h1
      intro y hy; exact ⟨⟨hy.1.1, hy.2⟩, hy.1.2⟩
  exact (hs'm.inter ht).nullMeasurableSet.congr hae.symm

omit [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] in
theorem nullMeasurableSet_canonicalTruncationDomain (α β : ℝ) :
    NullMeasurableSet (canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  by_cases h : ∃ d, IsTruncationDatum K α β d
  · have hspec := canonicalTruncationData_spec K h
    obtain ⟨-, -, -, hsub, hFD⟩ := hspec
    have hslab : MeasurableSet {g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
      NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
    exact nullMeasurableSet_of_restrict (adelicGLHaar (Fin 2) (𝓞 K) K) hslab hsub hFD.nullMeasurableSet
  · have : canonicalTruncationDomain K α β = ∅ := by
      show (canonicalTruncationData K α β).2.2 = ∅
      unfold canonicalTruncationData
      rw [dif_neg h]
    rw [this]
    exact MeasurableSet.empty.nullMeasurableSet

include hξc hξt hξu hf hfc in

theorem ae_ae_not_mem (N : Set (AdelicGL2 (𝓞 K) K)) (hNm : MeasurableSet N) (hN : adelicGLHaar (Fin 2) (𝓞 K) K N = 0)
    (q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), ∀ᵐ w ∂νZK,
      centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g)) ∉ N := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Sq : Set (AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ) :=
    {p | centralScalar (𝓞 K) K p.2 * (globalPoints (𝓞 K) K q.out * (x * p.1)) ∈ N} with hSq
  have hSqm : MeasurableSet Sq :=
    hNm.preimage (((continuous_centralScalar K).comp continuous_snd).mul
      (continuous_const.mul (continuous_const.mul continuous_fst))).measurable
  have hnull : (μ.prod νZK) Sq = 0 := by
    rw [Measure.prod_apply_symm hSqm]
    have : ∀ w : (AdeleRing (𝓞 K) K)ˣ, μ ((fun g => (g, w)) ⁻¹' Sq) = 0 := by
      intro w
      have : (fun g => (g, w)) ⁻¹' Sq =
          (fun g => (centralScalar (𝓞 K) K w * globalPoints (𝓞 K) K q.out * x) * g) ⁻¹' N := by
        ext g; simp only [hSq, Set.mem_preimage, Set.mem_setOf_eq, mul_assoc]
      rw [this, measure_preimage_mul, hN]
    simp [this]
  have := Measure.ae_ae_of_ae_prod (measure_eq_zero_iff_ae_notMem.1 hnull)
  exact this

open Classical in
include hξc hξt hξu hf hfc in
theorem final (α β : ℝ) (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (hΨm : Measurable Ψ)
    (hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B) :
    ∫ y in canonicalTruncationDomain K α β,
        (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * globalPoints (𝓞 K) K q.out *
                      (centralScalar (𝓞 K) K z * y)) ∂νZK) * Ψ y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      convOp K f (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (canonicalTruncationDomain K α β).indicator Ψ
                (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK) x := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := secondCountableTopology_gl K
  haveI := isHaarMeasure_glHaar K
  haveI := countable_quot K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ₀ := canonicalTruncationDomain K α β with hΦ₀
  obtain ⟨CΨ, hCΨ, hΨC⟩ := hΨc
  obtain ⟨BΨ, hΨB⟩ := hΨb

  obtain ⟨Φ₁, -, hΦ₁m, hae⟩ := (nullMeasurableSet_canonicalTruncationDomain K α β).exists_measurable_superset_ae_eq
  rw [← hΦ₀] at hae

  set Ψ₁ := Φ₁.indicator Ψ with hΨ₁
  have hΨ₁m : Measurable Ψ₁ := hΨm.indicator hΦ₁m
  have hΨ₁C : ∀ y ∉ CΨ, Ψ₁ y = 0 := fun y hy => by
    simp only [hΨ₁, Set.indicator_apply_eq_zero]; exact fun _ => hΨC y hy
  have hΨ₁B : ∀ y, ‖Ψ₁ y‖ ≤ BΨ := fun y => (norm_indicator_le_norm_self _ _).trans (hΨB y)
  have hcore := core K νZK ξK hξc hξt hξu f hf hfc Ψ₁ hΨ₁m CΨ hCΨ hΨ₁C BΨ hΨ₁B x

  have hL : ∫ y in Φ₀, (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
        ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          f (x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K z * y)) ∂νZK) * Ψ y ∂μ =
      ∫ y, (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
        ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          f (x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K z * y)) ∂νZK) * Ψ₁ y ∂μ := by
    rw [setIntegral_congr_set hae.symm, ← integral_indicator hΦ₁m]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hΨ₁]
    rw [Set.indicator_mul_right]

  have hnull : μ ((Φ₁ \ Φ₀) ∪ (Φ₀ \ Φ₁)) = 0 := by
    have h := ae_eq_set.1 hae
    exact measure_union_null h.1 h.2
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  have hind : ∀ y ∉ N, Φ₀.indicator Ψ y = Ψ₁ y := by
    intro y hy
    have h1' : y ∈ Φ₀ → y ∈ Φ₁ := fun h => by
      by_contra h'; exact hy (hNsub (Or.inr ⟨h, h'⟩))
    have h2' : y ∈ Φ₁ → y ∈ Φ₀ := fun h => by
      by_contra h'; exact hy (hNsub (Or.inl ⟨h, h'⟩))
    simp only [hΨ₁, Set.indicator_apply]
    by_cases h1 : y ∈ Φ₀
    · rw [if_pos h1, if_pos (h1' h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (h2' h))]
  have hR : convOp K f (fun g : AdelicGL2 (𝓞 K) K =>
        ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
            Φ₀.indicator Ψ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * g)) ∂νZK) x =
      ∫ g, (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
            Ψ₁ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g))) ∂νZK) * f g ∂μ := by
    rw [convOp_apply, show rightConv K _ f x = ∫ g, _ ∂μ from rightConv_apply K _ f x]
    have hgood : ∀ᵐ g ∂μ, ∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K), ∀ᵐ w ∂νZK,
        centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K q.out * (x * g)) ∉ N :=
      ae_all_iff.2 fun q => ae_ae_not_mem K νZK ξK hξc hξt hξu f hf hfc x N hNm hN0 q
    refine integral_congr_ae (hgood.mono fun g hg => ?_)
    dsimp only
    congr 1
    refine finsum_congr fun q => ?_
    refine integral_congr_ae ((hg q).mono fun w hw => ?_)
    dsimp only
    rw [hind _ hw]
  rw [hR, hΦ₀] at *
  rw [hL]
  exact hcore

end Oper25

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
    (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (_hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B)
    (x : AdelicGL2 (𝓞 K) K) :
    ∫ y in AutomorphicForm.canonicalTruncationDomain K α β,
        (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK) * Ψ y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      convOp K f (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) x :=
  Oper25.final K νZK ξK hξc hξt hξu f _hf _hfc x α β Ψ _hΨm _hΨc _hΨb

end S_AutomorphicForm_setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport (solution)
