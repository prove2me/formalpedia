-- Prove2me | solution 1 for AutomorphicForm.exists_forall_isSlabProfile_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_le_mul_eLpNorm_sub_diagOne_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/09476a8d-d90c-580c-90b4-8e08b044891c

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_HaarQuotient
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_isSlabProfile_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_le_mul_eLpNorm_sub_diagOne_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

section

open MeasureTheory

namespace InvariantDescent

variable {G : Type*} [Group G] {H : Subgroup G}

private def descend {β : Type*} (f : G → β) (hf : ∀ x ∈ H, ∀ g, f (x * g) = f g) :
    MulAction.orbitRel.Quotient H G → β :=
  Quotient.lift f (fun a b hab => by
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hx]
    exact hf x x.2 b)

private theorem apply_out_eq_descend {β : Type*} (f : G → β) (hf : ∀ x ∈ H, ∀ g, f (x * g) = f g)
    (q : MulAction.orbitRel.Quotient H G) : f q.out = descend f hf q := by
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.mk_out (s := MulAction.orbitRel H G) g))
    show f (Quotient.mk (MulAction.orbitRel H G) g).out = f g
    rw [← hx]
    exact hf x x.2 g

variable [MeasurableSpace G]

private theorem measurable_descend {β : Type*} [MeasurableSpace β] (f : G → β)
    (hf : ∀ x ∈ H, ∀ g, f (x * g) = f g) (hfm : Measurable f) : Measurable (descend f hf) :=
  measurable_from_quotient.mpr hfm

private theorem map_descend_eq {m : Measure (MulAction.orbitRel.Quotient H G)} {ρ : Measure G}
    (hdis : ∀ f : G → ENNReal, Measurable f → (∀ x ∈ H, ∀ g, f (x * g) = f g) →
      ∫⁻ q, f q.out ∂m = ∫⁻ g, f g ∂ρ)
    {β : Type*} [MeasurableSpace β] (F : G → β) (hFm : Measurable F)
    (hFinv : ∀ x ∈ H, ∀ g, F (x * g) = F g) :
    m.map (descend F hFinv) = ρ.map F := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_descend F hFinv hFm) hs, Measure.map_apply hFm hs,
    ← lintegral_indicator_one ((measurable_descend F hFinv hFm) hs),
    ← lintegral_indicator_one (hFm hs)]
  have hind : ∀ x ∈ H, ∀ g, (F ⁻¹' s).indicator (1 : G → ENNReal) (x * g) = (F ⁻¹' s).indicator 1 g := by
    intro x hx g
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply, hFinv x hx g]
  rw [← hdis _ (measurable_one.indicator (hFm hs)) hind]
  refine lintegral_congr (fun q => ?_)
  simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply, apply_out_eq_descend F hFinv q]

private theorem integral_apply_out_eq {m : Measure (MulAction.orbitRel.Quotient H G)} {ρ : Measure G}
    (hdis : ∀ f : G → ENNReal, Measurable f → (∀ x ∈ H, ∀ g, f (x * g) = f g) →
      ∫⁻ q, f q.out ∂m = ∫⁻ g, f g ∂ρ)
    (F : G → ℂ) (hFm : Measurable F) (hFinv : ∀ x ∈ H, ∀ g, F (x * g) = F g) :
    ∫ q, F q.out ∂m = ∫ g, F g ∂ρ := by
  have hmap := map_descend_eq hdis F hFm hFinv
  have h1 : ∫ z, (id z : ℂ) ∂(m.map (descend F hFinv)) = ∫ q, F q.out ∂m := by
    rw [integral_map (measurable_descend F hFinv hFm).aemeasurable aestronglyMeasurable_id]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => (apply_out_eq_descend F hFinv q).symm)
  have h2 : ∫ z, (id z : ℂ) ∂(ρ.map F) = ∫ g, F g ∂ρ := by
    rw [integral_map hFm.aemeasurable aestronglyMeasurable_id]
    rfl
  rw [← h1, ← h2, hmap]

private theorem integrable_apply_out_iff {m : Measure (MulAction.orbitRel.Quotient H G)} {ρ : Measure G}
    (hdis : ∀ f : G → ENNReal, Measurable f → (∀ x ∈ H, ∀ g, f (x * g) = f g) →
      ∫⁻ q, f q.out ∂m = ∫⁻ g, f g ∂ρ)
    (F : G → ℂ) (hFm : Measurable F) (hFinv : ∀ x ∈ H, ∀ g, F (x * g) = F g) :
    Integrable (fun q => F q.out) m ↔ Integrable F ρ := by
  have hmap := map_descend_eq hdis F hFm hFinv
  have h1 : Integrable (fun q => F q.out) m ↔ Integrable (descend F hFinv) m :=
    integrable_congr (Filter.Eventually.of_forall fun q => apply_out_eq_descend F hFinv q)
  have h2 : Integrable (descend F hFinv) m ↔ Integrable (id : ℂ → ℂ) (m.map (descend F hFinv)) :=
    (integrable_map_measure aestronglyMeasurable_id (measurable_descend F hFinv hFm).aemeasurable).symm
  have h3 : Integrable F ρ ↔ Integrable (id : ℂ → ℂ) (ρ.map F) :=
    (integrable_map_measure aestronglyMeasurable_id hFm.aemeasurable).symm
  rw [h1, h2, h3, hmap]

private theorem measurable_apply_out {β : Type*} [MeasurableSpace β] (F : G → β) (hFm : Measurable F)
    (hFinv : ∀ x ∈ H, ∀ g, F (x * g) = F g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => F q.out := by
  have h : (fun q : MulAction.orbitRel.Quotient H G => F q.out) = descend F hFinv :=
    funext fun q => apply_out_eq_descend F hFinv q
  rw [h]
  exact measurable_descend F hFinv hFm

end InvariantDescent

end
section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace IteratedCoordinates

variable {X Y Z G : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace G]

private def coordMeasure (μ₁ : Measure X) (μ₂ : Measure Y) (μ₃ : Measure Z) (w : Y → ℝ≥0∞)
    (π : X × Y × Z → G) : Measure G :=
  (μ₁.prod ((μ₂.withDensity w).prod μ₃)).map π

variable (μ₁ : Measure X) (μ₂ : Measure Y) (μ₃ : Measure Z) [SFinite μ₁] [SFinite μ₂] [SFinite μ₃]

omit [SFinite μ₁] in

private theorem lintegral_coordMeasure {w : Y → ℝ≥0∞} (hw : Measurable w) {π : X × Y × Z → G}
    (hπ : Measurable π) {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂(coordMeasure μ₁ μ₂ μ₃ w π) = ∫⁻ x, ∫⁻ y, ∫⁻ z, f (π (x, y, z)) * w y ∂μ₃ ∂μ₂ ∂μ₁ := by
  unfold coordMeasure
  rw [lintegral_map hf hπ]
  have h1 : ∫⁻ p, f (π p) ∂(μ₁.prod ((μ₂.withDensity w).prod μ₃))
      = ∫⁻ x, ∫⁻ p, f (π (x, p)) ∂((μ₂.withDensity w).prod μ₃) ∂μ₁ :=
    lintegral_prod (fun p => f (π p)) (hf.comp hπ).aemeasurable
  rw [h1]
  refine lintegral_congr (fun x => ?_)
  have hx : Measurable fun p : Y × Z => f (π (x, p)) := (hf.comp hπ).comp measurable_prodMk_left
  have h2 : ∫⁻ p, f (π (x, p)) ∂((μ₂.withDensity w).prod μ₃)
      = ∫⁻ y, ∫⁻ z, f (π (x, y, z)) ∂μ₃ ∂(μ₂.withDensity w) :=
    lintegral_prod (fun p : Y × Z => f (π (x, p))) hx.aemeasurable
  have h3 : ∫⁻ y, ∫⁻ z, f (π (x, y, z)) ∂μ₃ ∂(μ₂.withDensity w)
      = ∫⁻ y, (w * fun y => ∫⁻ z, f (π (x, y, z)) ∂μ₃) y ∂μ₂ :=
    lintegral_withDensity_eq_lintegral_mul μ₂ hw hx.lintegral_prod_right'
  rw [h2, h3]
  refine lintegral_congr (fun y => ?_)
  have hxy : Measurable fun z : Z => f (π (x, y, z)) := hx.comp measurable_prodMk_left
  show w y * ∫⁻ z, f (π (x, y, z)) ∂μ₃ = ∫⁻ z, f (π (x, y, z)) * w y ∂μ₃
  rw [lintegral_mul_const _ hxy, mul_comm]

private theorem integral_coordMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : Y → ℝ≥0∞} (hw : Measurable w) (hwfin : ∀ y, w y < ∞) {π : X × Y × Z → G}
    (hπ : Measurable π) {F : G → E} (hFm : AEStronglyMeasurable F (coordMeasure μ₁ μ₂ μ₃ w π))
    (hFi : Integrable F (coordMeasure μ₁ μ₂ μ₃ w π)) :
    ∫ g, F g ∂(coordMeasure μ₁ μ₂ μ₃ w π)
      = ∫ x, ∫ y, (w y).toReal • ∫ z, F (π (x, y, z)) ∂μ₃ ∂μ₂ ∂μ₁ := by
  have hFi' : Integrable (fun p : X × Y × Z => F (π p)) (μ₁.prod ((μ₂.withDensity w).prod μ₃)) :=
    (integrable_map_measure hFm hπ.aemeasurable).mp hFi
  unfold coordMeasure
  rw [integral_map hπ.aemeasurable hFm, integral_prod _ hFi']
  refine integral_congr_ae ((hFi'.prod_right_ae).mono fun x hx => ?_)
  dsimp only at hx ⊢
  rw [integral_prod _ hx,
    integral_withDensity_eq_integral_toReal_smul hw (Filter.Eventually.of_forall hwfin) _]

omit [SFinite μ₁] [SFinite μ₂] [SFinite μ₃] in

private theorem integrable_coordMeasure_of_norm_le {E : Type*} [NormedAddCommGroup E]
    {w : Y → ℝ≥0∞} {π : X × Y × Z → G} (hπ : Measurable π) {F : G → E}
    (hFm : AEStronglyMeasurable F (coordMeasure μ₁ μ₂ μ₃ w π)) {B : X × Y × Z → ℝ}
    (hB : Integrable B (μ₁.prod ((μ₂.withDensity w).prod μ₃))) (hle : ∀ p, ‖F (π p)‖ ≤ B p) :
    Integrable F (coordMeasure μ₁ μ₂ μ₃ w π) :=
  (integrable_map_measure hFm hπ.aemeasurable).mpr
    (hB.mono' (hFm.comp_aemeasurable hπ.aemeasurable) (Filter.Eventually.of_forall hle))

omit [SFinite μ₁] [SFinite μ₂] [SFinite μ₃] in

private theorem aestronglyMeasurable_coordMeasure {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [SecondCountableTopology E] [OpensMeasurableSpace E]
    {w : Y → ℝ≥0∞} {π : X × Y × Z → G} {F : G → E} (hF : Measurable F) :
    AEStronglyMeasurable F (coordMeasure μ₁ μ₂ μ₃ w π) :=
  hF.aestronglyMeasurable

end IteratedCoordinates

end

end
section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace IwasawaBochner

variable (K : Type) [Field K] [NumberField K]

private abbrev iwasawaCoord (p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K) :
    AdelicGL2 (𝓞 K) K :=
  centralScalar (𝓞 K) K p.1 * diagOne p.2.1 * (p.2.2 : AdelicGL2 (𝓞 K) K)

private abbrev torusWeight (t : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ :=
  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)

private def iwasawaMeasure (D D' : Set (AdeleRing (𝓞 K) K)ˣ) : Measure (AdelicGL2 (𝓞 K) K) :=
  IteratedCoordinates.coordMeasure ((NumberField.Idele.idelicHaar K).restrict D)
    ((NumberField.Idele.idelicHaar K).restrict D') (maximalCompactHaar K) (torusWeight K)
    (iwasawaCoord K)

private def HasIwasawaDisintegration (cQ : ℝ≥0∞) (D D' : Set (AdeleRing (𝓞 K) K)ˣ) : Prop :=
  ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
    (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
    ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
      cQ * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
            f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)

variable {K}

private theorem measurable_torusWeight (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K)) :
    Measurable (torusWeight K) :=
  ENNReal.measurable_ofReal.comp hnorm.inv

variable {D D' : Set (AdeleRing (𝓞 K) K)ˣ}

private theorem lintegral_iwasawaMeasure [SFinite (NumberField.Idele.idelicHaar K)]
    (hπ : Measurable (iwasawaCoord K)) (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K))
    {f : AdelicGL2 (𝓞 K) K → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂(iwasawaMeasure K D D') =
      ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
          f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) :=
  IteratedCoordinates.lintegral_coordMeasure ((NumberField.Idele.idelicHaar K).restrict D)
    ((NumberField.Idele.idelicHaar K).restrict D') (maximalCompactHaar K)
    (measurable_torusWeight hnorm) hπ hf

private theorem integrable_iwasawaMeasure_of_norm_le (hπ : Measurable (iwasawaCoord K))
    {Fc : AdelicGL2 (𝓞 K) K → ℂ} (hFm : Measurable Fc)
    {B : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K → ℝ}
    (hB : Integrable B (((NumberField.Idele.idelicHaar K).restrict D).prod
      ((((NumberField.Idele.idelicHaar K).restrict D').withDensity (torusWeight K)).prod
        (maximalCompactHaar K))))
    (hle : ∀ p, ‖Fc (iwasawaCoord K p)‖ ≤ B p) :
    Integrable Fc (iwasawaMeasure K D D') :=
  IteratedCoordinates.integrable_coordMeasure_of_norm_le _ _ _ hπ hFm.aestronglyMeasurable hB hle

variable {cQ : ℝ≥0∞}

private theorem lintegral_out_eq_lintegral_smul_iwasawaMeasure [SFinite (NumberField.Idele.idelicHaar K)]
    (hdis : HasIwasawaDisintegration K cQ D D') (hπ : Measurable (iwasawaCoord K))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K)) (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hf : Measurable f)
    (hfinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
      ∫⁻ g, f g ∂(cQ • iwasawaMeasure K D D') := by
  have h1 : ∫⁻ g, f g ∂(cQ • iwasawaMeasure K D D') = cQ * ∫⁻ g, f g ∂(iwasawaMeasure K D D') :=
    lintegral_smul_measure cQ f
  rw [h1, lintegral_iwasawaMeasure hπ hnorm hf, hdis f hf hfinv]

private theorem integral_out_eq_smul_integral_iwasawa [SFinite (NumberField.Idele.idelicHaar K)]
    (hdis : HasIwasawaDisintegration K cQ D D') (hπ : Measurable (iwasawaCoord K))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K)) (Fc : AdelicGL2 (𝓞 K) K → ℂ)
    (hFm : Measurable Fc)
    (hFinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, Fc (x * g) = Fc g)
    (hFi : Integrable Fc (iwasawaMeasure K D D')) :
    ∫ q, Fc q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
      cQ.toReal • ∫ z in D, ∫ t in D',
        (ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)).toReal •
          ∫ k, Fc (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)
        ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  rw [InvariantDescent.integral_apply_out_eq
      (lintegral_out_eq_lintegral_smul_iwasawaMeasure hdis hπ hnorm) Fc hFm hFinv,
    integral_smul_measure]
  congr 1
  exact IteratedCoordinates.integral_coordMeasure ((NumberField.Idele.idelicHaar K).restrict D)
    ((NumberField.Idele.idelicHaar K).restrict D') (maximalCompactHaar K)
    (measurable_torusWeight hnorm) (fun _ => ENNReal.ofReal_lt_top) hπ hFm.aestronglyMeasurable
    hFi

private theorem integrable_apply_out [SFinite (NumberField.Idele.idelicHaar K)]
    (hdis : HasIwasawaDisintegration K cQ D D') (hπ : Measurable (iwasawaCoord K))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm K)) (hcQ : cQ ≠ ∞)
    (Fc : AdelicGL2 (𝓞 K) K → ℂ) (hFm : Measurable Fc)
    (hFinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, Fc (x * g) = Fc g)
    (hFi : Integrable Fc (iwasawaMeasure K D D')) :
    Integrable (fun q => Fc q.out) (rationalTorusUnipotentQuotientMeasure K) :=
  (InvariantDescent.integrable_apply_out_iff
      (lintegral_out_eq_lintegral_smul_iwasawaMeasure hdis hπ hnorm) Fc hFm hFinv).mpr
    (hFi.smul_measure hcQ)

end IwasawaBochner

end

end
section

open MeasureTheory NumberField NumberField.TateGlobal
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace NormWindowVolume

private def window (d₁ d₂ y : ℝ) : Set ℝ := {r : ℝ | r ^ 2 * y ∈ Set.Icc d₁ d₂}

private theorem measurableSet_window (d₁ d₂ y : ℝ) : MeasurableSet (window d₁ d₂ y) :=
  (by fun_prop : Measurable fun r : ℝ => r ^ 2 * y) measurableSet_Icc

private theorem window_inter_Ioi {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hy : 0 < y) :
    window d₁ d₂ y ∩ Set.Ioi 0 = Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y)) := by
  ext r
  simp only [window, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hr⟩
    have hd₂y : 0 ≤ d₂ / y := (div_pos (hd₁.trans_le (h₁.trans h₂)) hy).le
    refine ⟨?_, ?_⟩
    · conv_rhs => rw [← Real.sqrt_sq hr.le]
      rw [Real.sqrt_le_sqrt_iff (sq_nonneg r), div_le_iff₀ hy]
      exact h₁
    · conv_lhs => rw [← Real.sqrt_sq hr.le]
      rw [Real.sqrt_le_sqrt_iff hd₂y, le_div_iff₀ hy]
      exact h₂
  · rintro ⟨h₁, h₂⟩
    have hr : 0 < r := (Real.sqrt_pos.mpr (div_pos hd₁ hy)).trans_le h₁
    have hd₂y : 0 ≤ d₂ / y := (Real.sqrt_pos.mp (hr.trans_le h₂)).le
    rw [← Real.sqrt_sq hr.le, Real.sqrt_le_sqrt_iff (sq_nonneg r), div_le_iff₀ hy] at h₁
    rw [← Real.sqrt_sq hr.le, Real.sqrt_le_sqrt_iff hd₂y, le_div_iff₀ hy] at h₂
    exact ⟨⟨h₁, h₂⟩, hr⟩

private theorem lintegral_window_inv {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hy : 0 < y) :
    ∫⁻ r in Set.Ioi (0 : ℝ), (window d₁ d₂ y).indicator (fun _ => (1 : ℝ≥0∞)) r * ENNReal.ofReal r⁻¹
      = ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
  have hd₂ : 0 < d₂ := hd₁.trans_le hd
  have ha : 0 < Real.sqrt (d₁ / y) := Real.sqrt_pos.mpr (div_pos hd₁ hy)
  have hab : Real.sqrt (d₁ / y) ≤ Real.sqrt (d₂ / y) := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hd hy.le)
  have hb : 0 < Real.sqrt (d₂ / y) := ha.trans_le hab
  have hfun : ∀ r : ℝ, (window d₁ d₂ y).indicator (fun _ => (1 : ℝ≥0∞)) r * ENNReal.ofReal r⁻¹
      = (window d₁ d₂ y).indicator (fun r => ENNReal.ofReal r⁻¹) r := by
    intro r
    by_cases hr : r ∈ window d₁ d₂ y <;> simp [hr]
  simp_rw [hfun]
  rw [lintegral_indicator (measurableSet_window d₁ d₂ y), Measure.restrict_restrict (measurableSet_window d₁ d₂ y),
    window_inter_Ioi hd₁ hy]
  have hint : IntegrableOn (fun r : ℝ => r⁻¹) (Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y))) :=
    (continuousOn_inv₀.mono fun r hr => (ha.trans_le (Set.mem_Icc.mp hr).1).ne').integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => inv_nonneg.mpr (ha.trans_le hr.1).le)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb,
    Real.log_div hb.ne' ha.ne', Real.log_sqrt (div_pos hd₂ hy).le, Real.log_sqrt (div_pos hd₁ hy).le,
    Real.log_div hd₂.ne' hy.ne', Real.log_div hd₁.ne' hy.ne', Real.log_div hd₂.ne' hd₁.ne']
  ring

variable {F : Type} [Field F] [NumberField F]

private theorem lintegral_indicator_window {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hy : 0 < y) :
    ∫⁻ z in D, (window d₁ d₂ y).indicator (fun _ => (1 : ℝ≥0∞)) (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F)
      = V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
  rw [hV ((window d₁ d₂ y).indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator (measurableSet_window d₁ d₂ y)),
    lintegral_window_inv hd₁ hd hy]

private theorem measure_window {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hy : 0 < y) :
    NumberField.Idele.idelicHaar F ({z | ideleNorm F z ^ 2 * y ∈ Set.Icc d₁ d₂} ∩ D)
      = V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
  have hpre : MeasurableSet {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * y ∈ Set.Icc d₁ d₂} :=
    (continuous_ideleNorm F).measurable (measurableSet_window d₁ d₂ y)
  rw [← Measure.restrict_apply hpre, ← lintegral_indicator_one hpre, ← lintegral_indicator_window hV hd₁ hd hy]
  rfl

private theorem setIntegral_indicator_window {D : Set (AdeleRing (𝓞 F) F)ˣ} {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    {d₁ d₂ y : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hy : 0 < y) :
    ∫ z in D, (window d₁ d₂ y).indicator (fun _ => (1 : ℂ)) (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F)
      = ((V.toReal * (Real.log (d₂ / d₁) / 2) : ℝ) : ℂ) := by
  have hpre : MeasurableSet {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * y ∈ Set.Icc d₁ d₂} :=
    (continuous_ideleNorm F).measurable (measurableSet_window d₁ d₂ y)
  have hlog : 0 ≤ Real.log (d₂ / d₁) / 2 :=
    div_nonneg (Real.log_nonneg ((one_le_div hd₁).mpr hd)) (by norm_num)
  have hfun : (fun z => (window d₁ d₂ y).indicator (fun _ => (1 : ℂ)) (ideleNorm F z))
      = {z : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F z ^ 2 * y ∈ Set.Icc d₁ d₂}.indicator (fun _ => (1 : ℂ)) := rfl
  rw [hfun, integral_indicator hpre, setIntegral_const, measureReal_def, Measure.restrict_apply hpre,
    measure_window hV hd₁ hd hy, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlog, Complex.real_smul, mul_one]

end NormWindowVolume

end

end
section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace SlabToTorus

variable {F : Type} [Field F] [NumberField F]

private theorem indicator_apply_coord_eq {S : Set (AdelicGL2 (𝓞 F) F)} {d₁ d₂ : ℝ}
    {Y : (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ}
    (hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k))
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, t, k)) =
      (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k)).indicator
        (fun _ => Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F)))) z := by
  classical
  simp only [Set.indicator_apply, Set.mem_preimage, IwasawaBochner.iwasawaCoord]
  by_cases hz : NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k)
  · rw [if_pos ((hSco z t k).2 hz), if_pos hz]
    exact hcen z t k
  · rw [if_neg (fun h => hz ((hSco z t k).1 h)), if_neg hz]

private theorem measurable_indicator_mul_conj {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    {Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ} (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂) :
    Measurable (S.indicator fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) :=
  (hΦ₁m.mul (Complex.continuous_conj.measurable.comp hΦ₂m)).indicator hS

private theorem indicator_mul_conj_apply_mul {S : Set (AdelicGL2 (𝓞 F) F)}
    (hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (hΦ₁inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₁ (x * g) = Φ₁ g)
    (hΦ₂inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₂ (x * g) = Φ₂ g) :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (x * g) =
        S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) g := by
  classical
  intro x hx g
  simp only [Set.indicator_apply]
  by_cases hg : g ∈ S
  · rw [if_pos ((hSinv x hx g).2 hg), if_pos hg, hΦ₁inv x hx g, hΦ₂inv x hx g]
  · rw [if_neg (fun h => hg ((hSinv x hx g).1 h)), if_neg hg]

private theorem integrable_indicator_mul_conj_comp_iwasawaCoord
    [SFinite (NumberField.Idele.idelicHaar F)]
    {V : ℝ≥0∞} {D : Set (AdeleRing (𝓞 F) F)ˣ} {d₁ d₂ : ℝ}
    (hπ : Measurable (IwasawaBochner.iwasawaCoord F))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm F))
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    {Y : (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ} (hY : ∀ t k, 0 < Y t k)
    (hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k))
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (hint : Integrable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        Φ₁ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
        (maximalCompactHaar F))) :
    Integrable
      (fun p => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F p))
      (((NumberField.Idele.idelicHaar F).restrict D).prod
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
          (maximalCompactHaar F))) := by
  classical
  have hlog : 0 ≤ Real.log (d₂ / d₁) / 2 := div_nonneg (Real.log_nonneg ((one_le_div hd₁).2 hd)) zero_le_two
  have hpt := indicator_apply_coord_eq hSco Φ₁ Φ₂ hcen
  have hwin : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      (NumberField.Idele.idelicHaar F).restrict D
          (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k)) =
        V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
    intro t k
    rw [Measure.restrict_apply (hnorm (NormWindowVolume.measurableSet_window d₁ d₂ _))]
    exact NormWindowVolume.measure_window hV hd₁ hd (hY t k)
  have hwinT : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      (NumberField.Idele.idelicHaar F).restrict D
          (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k)) ≠ ∞ := by
    intro t k
    rw [hwin t k]
    exact ENNReal.mul_ne_top hVT ENNReal.ofReal_ne_top
  have hGm := measurable_indicator_mul_conj hS hΦ₁m hΦ₂m
  refine (integrable_prod_iff'
    (f := fun p => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F p))
    (hGm.comp hπ).aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine Filter.Eventually.of_forall fun y => ?_
    obtain ⟨t, k⟩ := y
    show Integrable (fun z => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g))
      (IwasawaBochner.iwasawaCoord F (z, t, k))) ((NumberField.Idele.idelicHaar F).restrict D)
    have hfun : (fun z => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g))
        (IwasawaBochner.iwasawaCoord F (z, t, k))) =
        (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k)).indicator
          fun _ => Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))) :=
      funext fun z => hpt z t k
    have hIO : IntegrableOn
        (fun _ => Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
        (NumberField.TateGlobal.ideleNorm F ⁻¹' NormWindowVolume.window d₁ d₂ (Y t k))
        ((NumberField.Idele.idelicHaar F).restrict D) :=
      integrableOn_const (hwinT t k)
    rw [hfun]
    exact hIO.integrable_indicator (hnorm (NormWindowVolume.measurableSet_window d₁ d₂ _))
  · show Integrable (fun y : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      ∫ z, ‖S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, y))‖
        ∂((NumberField.Idele.idelicHaar F).restrict D))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
        (maximalCompactHaar F))
    have hfun : (fun y : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        ∫ z, ‖S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, y))‖
          ∂((NumberField.Idele.idelicHaar F).restrict D)) =
        fun y => (V.toReal * (Real.log (d₂ / d₁) / 2)) *
          ‖Φ₁ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F)) *
            starRingEnd ℂ (Φ₂ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F)))‖ := by
      funext y
      obtain ⟨t, k⟩ := y
      simp_rw [hpt _ t k, norm_indicator_eq_indicator_norm]
      rw [integral_indicator_const _ (hnorm (NormWindowVolume.measurableSet_window d₁ d₂ _)),
        measureReal_def, hwin t k, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlog, smul_eq_mul]
    rw [hfun]
    exact hint.norm.const_mul _

private theorem setIntegral_mul_conj_apply_out_eq_mul_setIntegral
    [SFinite (NumberField.Idele.idelicHaar F)]
    {cQ V : ℝ≥0∞} {D : Set (AdeleRing (𝓞 F) F)ˣ} {d₁ d₂ : ℝ}
    (hdis : IwasawaBochner.HasIwasawaDisintegration F cQ D D)
    (hπ : Measurable (IwasawaBochner.iwasawaCoord F))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm F))
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    (hT : MeasurableSet {q : RationalTorusUnipotentQuotient F | q.out ∈ S})
    (hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {Y : (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ} (hY : ∀ t k, 0 < Y t k)
    (hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k))
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂)
    (hΦ₁inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₁ (x * g) = Φ₁ g)
    (hΦ₂inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₂ (x * g) = Φ₂ g)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (hint : Integrable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        Φ₁ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
        (maximalCompactHaar F))) :
    ∫ q in {q : RationalTorusUnipotentQuotient F | q.out ∈ S},
        Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out) ∂(rationalTorusUnipotentQuotientMeasure F) =
      ((cQ.toReal * (V.toReal * (Real.log (d₂ / d₁) / 2)) : ℝ) : ℂ) *
        ∫ t in D, (NumberField.TateGlobal.ideleNorm F t)⁻¹ •
          ∫ k, Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F)))
            ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  classical
  have hpt := indicator_apply_coord_eq hSco Φ₁ Φ₂ hcen
  have hGm := measurable_indicator_mul_conj hS hΦ₁m hΦ₂m
  have hGinv := indicator_mul_conj_apply_mul hSinv hΦ₁inv hΦ₂inv
  have hGπi := integrable_indicator_mul_conj_comp_iwasawaCoord hπ hnorm hV hVT hd₁ hd hS hY hSco Φ₁ Φ₂ hΦ₁m
    hΦ₂m hcen hint

  have hρ := IwasawaBochner.lintegral_out_eq_lintegral_smul_iwasawaMeasure hdis hπ hnorm
  have hptT : ∀ q : RationalTorusUnipotentQuotient F,
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S}.indicator
          (fun q => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out)) q =
        S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) q.out := by
    intro q
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← integral_indicator hT]
  simp_rw [hptT]
  rw [InvariantDescent.integral_apply_out_eq hρ _ hGm hGinv, integral_smul_measure]
  have hmap : ∫ g, S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) g
        ∂(IwasawaBochner.iwasawaMeasure F D D) =
      ∫ p, S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F p)
        ∂(((NumberField.Idele.idelicHaar F).restrict D).prod
          ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
            (maximalCompactHaar F))) := by
    unfold IwasawaBochner.iwasawaMeasure IteratedCoordinates.coordMeasure
    exact integral_map hπ.aemeasurable hGm.aestronglyMeasurable
  rw [hmap, integral_prod_symm _ hGπi]

  have hinner : ∀ y : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F,
      ∫ z, S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, y))
          ∂((NumberField.Idele.idelicHaar F).restrict D) =
        ((V.toReal * (Real.log (d₂ / d₁) / 2) : ℝ) : ℂ) *
          (Φ₁ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F)) *
            starRingEnd ℂ (Φ₂ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F)))) := by
    rintro ⟨t, k⟩
    have hpt' : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
        S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) (IwasawaBochner.iwasawaCoord F (z, t, k)) =
          (NormWindowVolume.window d₁ d₂ (Y t k)).indicator (fun _ => (1 : ℂ))
              (NumberField.TateGlobal.ideleNorm F z) *
            (Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
              starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F)))) := by
      intro z
      rw [hpt z t k]
      simp only [Set.indicator_apply, Set.mem_preimage]
      split_ifs <;> simp
    simp_rw [hpt']
    rw [integral_mul_const, NormWindowVolume.setIntegral_indicator_window hV hd₁ hd (hY t k)]
  simp_rw [hinner]
  rw [integral_const_mul, integral_prod _ hint,
    integral_withDensity_eq_integral_toReal_smul₀ (IwasawaBochner.measurable_torusWeight hnorm).aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hw : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      (IwasawaBochner.torusWeight F t).toReal = (NumberField.TateGlobal.ideleNorm F t)⁻¹ := fun t =>
    ENNReal.toReal_ofReal (inv_nonneg.2 (NumberField.TateGlobal.ideleNorm_pos (F := F) t).le)
  simp_rw [hw]
  rw [Complex.real_smul, ← mul_assoc]
  congr 1
  exact (Complex.ofReal_mul _ _).symm

private theorem integrableOn_mul_conj_apply_out
    [SFinite (NumberField.Idele.idelicHaar F)]
    {cQ V : ℝ≥0∞} {D : Set (AdeleRing (𝓞 F) F)ˣ} {d₁ d₂ : ℝ}
    (hdis : IwasawaBochner.HasIwasawaDisintegration F cQ D D) (hcQ : cQ ≠ ∞)
    (hπ : Measurable (IwasawaBochner.iwasawaCoord F))
    (hnorm : Measurable (NumberField.TateGlobal.ideleNorm F))
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hVT : V ≠ ∞) (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    (hT : MeasurableSet {q : RationalTorusUnipotentQuotient F | q.out ∈ S})
    (hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {Y : (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ} (hY : ∀ t k, 0 < Y t k)
    (hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        NumberField.TateGlobal.ideleNorm F z ∈ NormWindowVolume.window d₁ d₂ (Y t k))
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂)
    (hΦ₁inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₁ (x * g) = Φ₁ g)
    (hΦ₂inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₂ (x * g) = Φ₂ g)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (hint : Integrable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        Φ₁ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (IwasawaBochner.torusWeight F)).prod
        (maximalCompactHaar F))) :
    IntegrableOn (fun q : RationalTorusUnipotentQuotient F => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out))
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S} (rationalTorusUnipotentQuotientMeasure F) := by
  classical
  have hGm := measurable_indicator_mul_conj hS hΦ₁m hΦ₂m
  have hGinv := indicator_mul_conj_apply_mul hSinv hΦ₁inv hΦ₂inv
  have hGπi := integrable_indicator_mul_conj_comp_iwasawaCoord hπ hnorm hV hVT hd₁ hd hS hY hSco Φ₁ Φ₂ hΦ₁m
    hΦ₂m hcen hint
  have hGi : Integrable (S.indicator fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g))
      (IwasawaBochner.iwasawaMeasure F D D) := by
    unfold IwasawaBochner.iwasawaMeasure IteratedCoordinates.coordMeasure
    exact (integrable_map_measure hGm.aestronglyMeasurable hπ.aemeasurable).2 hGπi
  have hout := IwasawaBochner.integrable_apply_out hdis hπ hnorm hcQ _ hGm hGinv hGi
  have hptT : ∀ q : RationalTorusUnipotentQuotient F,
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S}.indicator
          (fun q : RationalTorusUnipotentQuotient F => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out)) q =
        S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) q.out := by
    intro q
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← integrable_indicator_iff hT]
  rw [show ({q : RationalTorusUnipotentQuotient F | q.out ∈ S}.indicator
      fun q : RationalTorusUnipotentQuotient F => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out)) =
      fun q => S.indicator (fun g => Φ₁ g * starRingEnd ℂ (Φ₂ g)) q.out from funext hptT]
  exact hout

end SlabToTorus

end

end
section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

open AutomorphicForm
open scoped ENNReal

namespace CuspidalOrthogonality

section Invariance

variable (F : Type) [Field F] [NumberField F]

private def leftInvariantSubgroup (c : AdelicGL2 (𝓞 F) F → ℂ) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {h | ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g}
  one_mem' := by
    intro g
    rw [one_mul]
  mul_mem' := by
    intro a b ha hb
    have ha' : ∀ g : AdelicGL2 (𝓞 F) F, c (a * g) = c g := ha
    have hb' : ∀ g : AdelicGL2 (𝓞 F) F, c (b * g) = c g := hb
    intro g
    rw [mul_assoc, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : ∀ g : AdelicGL2 (𝓞 F) F, c (a * g) = c g := ha
    intro g
    have h := ha' (a⁻¹ * g)
    rw [mul_inv_cancel_left] at h
    exact h.symm

private theorem mem_leftInvariantSubgroup {c : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} :
    h ∈ leftInvariantSubgroup F c ↔ ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g :=
  Iff.rfl

omit [NumberField F] in

private theorem scalar_mem_borelSubgroup (a : Fˣ) :
    Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a ∈ borelSubgroup F := by
  show ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  have hval : ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (a : F) := rfl
  rw [hval, Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

omit [NumberField F] in

private theorem diagOne_mem_borelSubgroup (a : Fˣ) : diagOne a ∈ borelSubgroup F := by
  show ((diagOne a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem forall_mem_rationalTorusUnipotent_mul_eq (c : AdelicGL2 (𝓞 F) F → ℂ)
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), c (unipotentGL2 x * g) = c g)
    (hB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, c (globalPoints (𝓞 F) F γ * g) = c g) :
    ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g := by
  have hle : rationalTorusUnipotent F ≤ leftInvariantSubgroup F c := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨a, rfl⟩ g
      exact hB _ (scalar_mem_borelSubgroup F a) g
    · rintro _ ⟨a, rfl⟩ g
      exact hB _ (diagOne_mem_borelSubgroup F a) g
    · rintro _ ⟨x, rfl⟩ g
      exact hN x.toAdd g
  intro h hh g
  have hmem : h ∈ leftInvariantSubgroup F c := hle hh
  exact (mem_leftInvariantSubgroup F).mp hmem g

end Invariance

end CuspidalOrthogonality

end

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace EisensteinTorusFacts

section Determinant

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem coe_diagOne (t : (AdeleRing R K)ˣ) :
    ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = Matrix.diagonal ![(t : AdeleRing R K), 1] := rfl

private theorem
det_diagOne (t : (AdeleRing R K)ˣ) : Matrix.GeneralLinearGroup.det (diagOne t : AdelicGL2 R K) = t := by
  apply Units.ext
  show Matrix.det ((diagOne t : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = (t : AdeleRing R K)
  rw [coe_diagOne, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_centralScalar (z : (AdeleRing R K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar R K z) = z ^ 2 := by
  rw [show centralScalar R K = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

end Determinant

variable {F : Type} [Field F] [NumberField F]

private theorem ideleNorm_det_iwasawa (z t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) :
    NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * diagOne t * k)) =
      NumberField.TateGlobal.ideleNorm F z ^ 2 *
        (NumberField.TateGlobal.ideleNorm F t *
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k)) := by
  rw [map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul,
    det_centralScalar, det_diagOne, pow_two, NumberField.TateGlobal.ideleNorm_mul]
  ring

private theorem iwasawa_mem_slab_iff (d₁ d₂ : ℝ) (z t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * diagOne t * k ∈
        {g : AdelicGL2 (𝓞 F) F |
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} ↔
      NumberField.TateGlobal.ideleNorm F z ^ 2 *
          (NumberField.TateGlobal.ideleNorm F t *
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k)) ∈ Set.Icc d₁ d₂ := by
  rw [Set.mem_setOf_eq, ideleNorm_det_iwasawa]

private theorem ideleNorm_mul_ideleNorm_det_pos (t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) :
    0 < NumberField.TateGlobal.ideleNorm F t *
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det k) :=
  mul_pos (NumberField.TateGlobal.ideleNorm_pos (F := F) t) (NumberField.TateGlobal.ideleNorm_pos (F := F) _)

private theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
  rw [one_mul] at h
  have h' : NumberField.TateGlobal.ideleNorm F 1 * 1 =
      NumberField.TateGlobal.ideleNorm F 1 * NumberField.TateGlobal.ideleNorm F 1 := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := F) 1).ne' h').symm

private theorem det_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
  ext
  simp [unipotentGL2, Matrix.det_fin_two_of]

private theorem ideleNorm_det_mul_eq_of_mem :
    ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (x * g)) =
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  have h := CuspidalOrthogonality.forall_mem_rationalTorusUnipotent_mul_eq F
    (fun g : AdelicGL2 (𝓞 F) F =>
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ))
    (fun x g => by
      simp only [map_mul, det_unipotentGL2, one_mul])
    (fun γ _ g => by
      simp only [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_globalPoints, one_mul])
  intro x hx g
  have h' := h x hx g
  exact_mod_cast h'

private theorem measurableSet_setOf_ideleNorm_det_out_mem_Icc (d₁ d₂ : ℝ)
    (hS : MeasurableSet {g : AdelicGL2 (𝓞 F) F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hdesc : ∀ (P : AdelicGL2 (𝓞 F) F → Prop), Measurable P →
      (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, P (x * g) = P g) →
        Measurable fun q : RationalTorusUnipotentQuotient F => P q.out) :
    MeasurableSet {q : RationalTorusUnipotentQuotient F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂} :=
  measurableSet_setOf.2 (hdesc _ (measurableSet_setOf.1 hS)
    (fun x hx g => by rw [ideleNorm_det_mul_eq_of_mem x hx g]))

end EisensteinTorusFacts

end

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open scoped Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.Idele.isHaarMeasure_idelicHaar
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

noncomputable section

namespace IwasawaQuotientDisintegration

variable (F : Type) [Field F] [NumberField F]

private theorem secondCountableTopology_units_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_units_adeleRing F
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
  infer_instance

private theorem sigmaFinite_adelicGLHaar : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  infer_instance

private theorem continuous_diagOne : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => (diagOne t : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Units.continuous_coe_inv
    · exact continuous_const

private theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F) := by
  have hdiag : ∀ x : AdeleRing (𝓞 F) F, Matrix.scalar (Fin 2) x = Matrix.diagonal fun _ => x := fun x =>
    Matrix.scalar_apply x
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
    simp only [hdiag]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.scalar (Fin 2) ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    simp only [hdiag]
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

private theorem measurable_centralScalar_mul_diagOne_mul :
    Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      centralScalar (𝓞 F) F p.1 * diagOne p.2.1 * (p.2.2 : AdelicGL2 (𝓞 F) F) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have h1 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      centralScalar (𝓞 F) F p.1 := (continuous_centralScalar F).measurable.comp measurable_fst
  have h2 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      (diagOne p.2.1 : AdelicGL2 (𝓞 F) F) :=
    (continuous_diagOne F).measurable.comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      (p.2.2 : AdelicGL2 (𝓞 F) F) :=
    (measurable_subtype_val_adelicMaximalCompact F).comp (measurable_snd.comp measurable_snd)
  exact (h1.mul h2).mul h3

end IwasawaQuotientDisintegration

end

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace TorusDisintPW

private theorem _root_.TorusDisintPW.main (F : Type) [Field F] [NumberField F]
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
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞) (hVT : V ≠ ∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hΦ₁m : Measurable Φ₁) (hΦ₂m : Measurable Φ₂)
    (hΦ₁inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₁ (x * g) = Φ₁ g)
    (hΦ₂inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₂ (x * g) = Φ₂ g)
    (hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
    (hint : Integrable
      (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        Φ₁ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
          (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((ideleNorm F t)⁻¹))).prod
        (maximalCompactHaar F))) :
    IntegrableOn (fun q : RationalTorusUnipotentQuotient F => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out))
        {q : RationalTorusUnipotentQuotient F |
          ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂}
        (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q in {q : RationalTorusUnipotentQuotient F |
        ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂},
        Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out) ∂(rationalTorusUnipotentQuotientMeasure F) =
      ((c.toReal * (V.toReal * (Real.log (d₂ / d₁) / 2)) : ℝ) : ℂ) *
        ∫ t in D, (ideleNorm F t)⁻¹ •
          ∫ k, Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F)))
            ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SigmaFinite (NumberField.Idele.idelicHaar F) := IwasawaQuotientDisintegration.sigmaFinite_idelicHaar F
  have hdis : IwasawaBochner.HasIwasawaDisintegration F c D D := hc D D hDm hDm hDF hDF
  have hπ : Measurable (IwasawaBochner.iwasawaCoord F) :=
    IwasawaQuotientDisintegration.measurable_centralScalar_mul_diagOne_mul F
  have hnorm : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  have hS : MeasurableSet {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} :=
    NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂
  set S : Set (AdelicGL2 (𝓞 F) F) :=
    {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} with hSdef
  have hTS : {q : RationalTorusUnipotentQuotient F |
      ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂} =
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S} := rfl
  rw [hTS]
  have hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S := fun x hx g => by
    rw [hSdef, Set.mem_setOf_eq, Set.mem_setOf_eq, EisensteinTorusFacts.ideleNorm_det_mul_eq_of_mem x hx g]
  have hT : MeasurableSet {q : RationalTorusUnipotentQuotient F | q.out ∈ S} :=
    EisensteinTorusFacts.measurableSet_setOf_ideleNorm_det_out_mem_Icc d₁ d₂ hS
      (fun P hP hPinv => InvariantDescent.measurable_apply_out P hP hPinv)
  have hY : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      0 < ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) := fun t k =>
    EisensteinTorusFacts.ideleNorm_mul_ideleNorm_det_pos t _
  have hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        ideleNorm F z ∈ NormWindowVolume.window d₁ d₂
          (ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F))) :=
    fun z t k => EisensteinTorusFacts.iwasawa_mem_slab_iff d₁ d₂ z t _
  exact ⟨SlabToTorus.integrableOn_mul_conj_apply_out hdis hc_top hπ hnorm hV hVT hd₁ hd hS hT hSinv hY hSco Φ₁ Φ₂
      hΦ₁m hΦ₂m hΦ₁inv hΦ₂inv hcen hint,
    SlabToTorus.setIntegral_mul_conj_apply_out_eq_mul_setIntegral hdis hπ hnorm hV hVT hd₁ hd hS hT hSinv hY hSco
      Φ₁ Φ₂ hΦ₁m hΦ₂m hΦ₁inv hΦ₂inv hcen hint⟩

p2m_export "TorusDisintPW" "main"
end TorusDisintPW

end

end

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal AutomorphicForm

open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace Ws31
namespace SlabCoordL2

variable (F : Type) [Field F] [NumberField F]

abbrev pins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

variable {F}

theorem sub_facts {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} {ξ : (pins F Φ₀).Z →* ℂˣ}
    (hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1) {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsSlabProfile F (pins F Φ₀).Z ξ φ) (hψ : IsSlabProfile F (pins F Φ₀).Z ξ ψ) :
    Measurable (fun g => φ g - ψ g) ∧
    (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, φ (x * g) - ψ (x * g) = φ g - ψ g) ∧
    (∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      ‖φ (centralScalar (𝓞 F) F z * g) - ψ (centralScalar (𝓞 F) F z * g)‖ₑ = ‖φ g - ψ g‖ₑ) := by
  refine ⟨hφ.measurable.sub hψ.measurable, ?_, ?_⟩
  · exact CuspidalOrthogonality.forall_mem_rationalTorusUnipotent_mul_eq F (fun g => φ g - ψ g)
      (fun x g => by simp only [hφ.unipotent_mul x g, hψ.unipotent_mul x g])
      (fun γ hγ g => by simp only [hφ.borel_mul γ hγ g, hψ.borel_mul γ hγ g])
  · intro z g
    have hz : z ∈ (pins F Φ₀).Z := Subgroup.mem_top z
    have h1 : φ (centralScalar (𝓞 F) F z * g) = ((ξ ⟨z, hz⟩ : ℂˣ) : ℂ) * φ g := hφ.central_transform ⟨z, hz⟩ g
    have h2 : ψ (centralScalar (𝓞 F) F z * g) = ((ξ ⟨z, hz⟩ : ℂˣ) : ℂ) * ψ g := hψ.central_transform ⟨z, hz⟩ g
    rw [h1, h2, ← mul_sub, enorm_mul, ← ofReal_norm ((ξ ⟨z, hz⟩ : ℂˣ) : ℂ), hξu, ENNReal.ofReal_one, one_mul]

set_option maxHeartbeats 3200000 in

theorem lintegral_restrict_enorm_rpow_apply_out_eq
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
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ) (hΦm : Measurable Φ)
    (hΦinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ (x * g) = Φ g)
    (hΦcen : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), ‖Φ (centralScalar (𝓞 F) F z * g)‖ₑ = ‖Φ g‖ₑ)
    (r : ℝ) :
    ∫⁻ q, ‖Φ q.out‖ₑ ^ r ∂((rationalTorusUnipotentQuotientMeasure F).restrict
        {q | ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂}) =
      c * (V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2)) *
        ∫⁻ p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F, ‖Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))‖ₑ ^ r
          ∂((((NumberField.Idele.idelicHaar F).restrict D).withDensity
              (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((ideleNorm F t)⁻¹))).prod (maximalCompactHaar F)) := by
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SigmaFinite (NumberField.Idele.idelicHaar F) := IwasawaQuotientDisintegration.sigmaFinite_idelicHaar F

  have hπ : Measurable (IwasawaBochner.iwasawaCoord F) :=
    IwasawaQuotientDisintegration.measurable_centralScalar_mul_diagOne_mul F
  have hnorm : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  have hS : MeasurableSet {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} :=
    NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂
  set S : Set (AdelicGL2 (𝓞 F) F) :=
    {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} with hSdef
  have hTS : {q : RationalTorusUnipotentQuotient F |
      ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂} =
      {q : RationalTorusUnipotentQuotient F | q.out ∈ S} := rfl
  rw [hTS]
  have hSinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S := fun x hx g => by
    rw [hSdef, Set.mem_setOf_eq, Set.mem_setOf_eq, EisensteinTorusFacts.ideleNorm_det_mul_eq_of_mem x hx g]
  have hT : MeasurableSet {q : RationalTorusUnipotentQuotient F | q.out ∈ S} :=
    EisensteinTorusFacts.measurableSet_setOf_ideleNorm_det_out_mem_Icc d₁ d₂ hS
      (fun P hP hPinv => InvariantDescent.measurable_apply_out P hP hPinv)
  have hY : ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      0 < ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) := fun t k =>
    EisensteinTorusFacts.ideleNorm_mul_ideleNorm_det_pos t _
  have hSco : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ S ↔
        ideleNorm F z ∈ NormWindowVolume.window d₁ d₂
          (ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F))) :=
    fun z t k => EisensteinTorusFacts.iwasawa_mem_slab_iff d₁ d₂ z t _

  have hGm : Measurable fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const).measurable.comp hΦm.enorm
  have hSGm : Measurable (S.indicator fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) := hGm.indicator hS
  have hw : Measurable fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((ideleNorm F t)⁻¹) :=
    ENNReal.measurable_ofReal.comp hnorm.inv
  have hdiag : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F) :=
    ((IwasawaQuotientDisintegration.continuous_diagOne F).measurable.comp measurable_fst).mul
      ((measurable_subtype_val_adelicMaximalCompact F).comp measurable_snd)
  have hGdiag : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      ‖Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))‖ₑ ^ r := hGm.comp hdiag

  have hSGinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) (x * g) =
        S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) g := by
    intro x hx g
    simp only [Set.indicator_apply]
    by_cases hg : g ∈ S
    · rw [if_pos ((hSinv x hx g).2 hg), if_pos hg, hΦinv x hx g]
    · rw [if_neg (fun h => hg ((hSinv x hx g).1 h)), if_neg hg]

  have hpt : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) (IwasawaBochner.iwasawaCoord F (z, t, k)) =
        (NormWindowVolume.window d₁ d₂
            (ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)))).indicator
          (fun _ => (1 : ℝ≥0∞)) (ideleNorm F z) * ‖Φ (diagOne t * (k : AdelicGL2 (𝓞 F) F))‖ₑ ^ r := by
    intro z t k
    simp only [Set.indicator_apply, IwasawaBochner.iwasawaCoord]
    by_cases hz : ideleNorm F z ∈ NormWindowVolume.window d₁ d₂
        (ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)))
    · rw [if_pos ((hSco z t k).2 hz), if_pos hz, one_mul, mul_assoc, hΦcen]
    · rw [if_neg (fun h => hz ((hSco z t k).1 h)), if_neg hz, zero_mul]

  have step1 : ∫⁻ q, ‖Φ q.out‖ₑ ^ r ∂((rationalTorusUnipotentQuotientMeasure F).restrict
        {q : RationalTorusUnipotentQuotient F | q.out ∈ S}) =
      ∫⁻ q, S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) q.out
        ∂(rationalTorusUnipotentQuotientMeasure F) := by
    rw [← lintegral_indicator hT]
    refine lintegral_congr fun q => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [step1, hc D D hDm hDm hDF hDF _ hSGm hSGinv, mul_assoc]
  congr 1

  have hHm : Measurable fun q : (AdeleRing (𝓞 F) F)ˣ × ((AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) =>
      S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) (IwasawaBochner.iwasawaCoord F q) *
        ENNReal.ofReal ((ideleNorm F q.2.1)⁻¹) :=
    (hSGm.comp hπ).mul (hw.comp (measurable_fst.comp measurable_snd))
  have step2 : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ∫⁻ t in D, ∫⁻ k, S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r)
            (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) * ENNReal.ofReal ((ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) =
        ∫⁻ p, S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) (IwasawaBochner.iwasawaCoord F (z, p)) *
            ENNReal.ofReal ((ideleNorm F p.1)⁻¹)
          ∂(((NumberField.Idele.idelicHaar F).restrict D).prod (maximalCompactHaar F)) := fun z =>
    (lintegral_prod (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
        S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) (IwasawaBochner.iwasawaCoord F (z, p)) *
          ENNReal.ofReal ((ideleNorm F p.1)⁻¹))
      (hHm.comp measurable_prodMk_left).aemeasurable).symm
  simp_rw [step2]
  have hHm' : Measurable (Function.uncurry fun (z : (AdeleRing (𝓞 F) F)ˣ)
      (p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) =>
        S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) (IwasawaBochner.iwasawaCoord F (z, p)) *
          ENNReal.ofReal ((ideleNorm F p.1)⁻¹)) := hHm
  rw [lintegral_lintegral_swap (μ := (NumberField.Idele.idelicHaar F).restrict D)
    (ν := ((NumberField.Idele.idelicHaar F).restrict D).prod (maximalCompactHaar F))
    (f := fun (z : (AdeleRing (𝓞 F) F)ˣ) (p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) =>
      S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) (IwasawaBochner.iwasawaCoord F (z, p)) *
        ENNReal.ofReal ((ideleNorm F p.1)⁻¹)) hHm'.aemeasurable]

  have step3 : ∀ p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F,
      ∫⁻ z in D, S.indicator (fun g : AdelicGL2 (𝓞 F) F => ‖Φ g‖ₑ ^ r) (IwasawaBochner.iwasawaCoord F (z, p)) *
          ENNReal.ofReal ((ideleNorm F p.1)⁻¹) ∂(NumberField.Idele.idelicHaar F) =
        V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2) *
          (‖Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))‖ₑ ^ r * ENNReal.ofReal ((ideleNorm F p.1)⁻¹)) := by
    rintro ⟨t, k⟩
    have hmi : Measurable fun z : (AdeleRing (𝓞 F) F)ˣ =>
        (NormWindowVolume.window d₁ d₂
            (ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)))).indicator
          (fun _ => (1 : ℝ≥0∞)) (ideleNorm F z) :=
      (measurable_const.indicator (NormWindowVolume.measurableSet_window d₁ d₂ _)).comp hnorm
    simp_rw [hpt]
    simp_rw [mul_assoc]
    rw [lintegral_mul_const _ hmi, NormWindowVolume.lintegral_indicator_window hV hd₁ hd (hY t k), mul_assoc]
  simp_rw [step3]
  have hm : Measurable fun y : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      ‖Φ (diagOne y.1 * (y.2 : AdelicGL2 (𝓞 F) F))‖ₑ ^ r * ENNReal.ofReal ((ideleNorm F y.1)⁻¹) :=
    hGdiag.mul (hw.comp measurable_fst)
  rw [lintegral_const_mul _ hm]
  congr 1

  have hw1 : Measurable fun z : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      ENNReal.ofReal ((ideleNorm F z.1)⁻¹) := hw.comp measurable_fst
  rw [prod_withDensity_left hw, lintegral_withDensity_eq_lintegral_mul _ hw1 hGdiag]
  refine lintegral_congr fun p => ?_
  rw [Pi.mul_apply]
  exact mul_comm _ _

theorem main
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
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞) (hVT : V ≠ ∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ₀).Z →* ℂˣ) (hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1) :
    ∃ κ : ℝ≥0∞, κ ≠ ∞ ∧
    ∀ (φ ψ : AdelicGL2 (𝓞 F) F → ℂ),
      IsSlabProfile F (pins F Φ₀).Z ξ φ → IsSlabProfile F (pins F Φ₀).Z ξ ψ →
      eLpNorm (fun q : RationalTorusUnipotentQuotient F => φ q.out - ψ q.out) 2
          ((rationalTorusUnipotentQuotientMeasure F).restrict
            {q | ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂}) ≤
        κ * eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
            φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) - ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))) 2
          ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
              (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((ideleNorm F t)⁻¹))).prod (maximalCompactHaar F)) := by
  have he : (0 : ℝ) ≤ 1 / (2 : ℝ≥0∞).toReal := by positivity
  refine ⟨(c * (V * ENNReal.ofReal (Real.log (d₂ / d₁) / 2))) ^ (1 / (2 : ℝ≥0∞).toReal),
    ENNReal.rpow_ne_top_of_nonneg he
      (ENNReal.mul_ne_top hc_top (ENNReal.mul_ne_top hVT ENNReal.ofReal_ne_top)), ?_⟩
  intro φ ψ hφ hψ
  obtain ⟨hΦm, hΦinv, hΦcen⟩ := sub_facts hξu hφ hψ
  have two_ne_zero' : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  refine le_of_eq ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero' ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm two_ne_zero' ENNReal.ofNat_ne_top,
    lintegral_restrict_enorm_rpow_apply_out_eq c hc D hDm hDF V hV d₁ d₂ hd₁ hd.le (fun g => φ g - ψ g)
      hΦm hΦinv hΦcen (2 : ℝ≥0∞).toReal,
    ENNReal.mul_rpow_of_nonneg _ _ he]

end Ws31.SlabCoordL2

end

end

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c : ℝ≥0∞) (_hc_top : c ≠ ∞)
    (_hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
          c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
    (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
    (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ) (_hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1) :
    ∃ κ : ℝ≥0∞, κ ≠ ∞ ∧
    ∀ (φ ψ : AdelicGL2 (𝓞 F) F → ℂ),
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ →
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ →
      eLpNorm (fun q : AutomorphicForm.RationalTorusUnipotentQuotient F => φ q.out - ψ q.out) 2
          ((AutomorphicForm.rationalTorusUnipotentQuotientMeasure F).restrict
            {q | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂}) ≤
        κ * eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
            φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
              ψ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))) 2
          ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
              (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
            (maximalCompactHaar F)) := by
  obtain ⟨κ, hκ, h⟩ := Ws31.SlabCoordL2.main c _hc_top _hc D _hDm _hDF V _hVT _hV d₁ d₂ _hd₁ _hd Φ ξ _hξu
  exact ⟨κ, hκ, fun φ ψ hφ hψ => h φ ψ hφ hψ⟩

end S_AutomorphicForm_exists_forall_isSlabProfile_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_le_mul_eLpNorm_sub_diagOne_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_isSlabProfile_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_le_mul_eLpNorm_sub_diagOne_mul (solution)
