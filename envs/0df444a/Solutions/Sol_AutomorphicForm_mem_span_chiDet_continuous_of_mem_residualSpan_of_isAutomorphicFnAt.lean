-- Prove2me | solution 1 for AutomorphicForm.mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/89b71bd3-3015-5388-be51-de07ef763a08

import Mathlib
import Definitions.Def_AutomorphicForm_AdelicLsXi
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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
import Theorems.Thm_MeasureTheory_aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory Measure MeasureTheory.Measure Set Filter Topology"
open scoped Pointwise

namespace AutoCont

theorem continuous_of_measurable {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [OpensMeasurableSpace H]
    [SecondCountableTopology H]
    (f : G →* H) (hf : Measurable f) : Continuous f := by
  classical
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one]
  intro U hU

  obtain ⟨V, hV, hVU⟩ := exists_nhds_split_inv hU
  let W : Set H := interior V
  have hWo : IsOpen W := isOpen_interior
  have h1W : (1 : H) ∈ W := mem_interior_iff_mem_nhds.2 hV
  have hWU : ∀ v ∈ W, ∀ w ∈ W, v / w ∈ U := fun v hv w hw => hVU v (interior_subset hv) w (interior_subset hw)

  have hcov : ∀ h : H, h ∈ (fun x => x * h) '' W := fun h => ⟨1, h1W, one_mul h⟩
  obtain ⟨D, hDc, hDU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun h : H => (fun x => x * h) '' W)
    (fun h => (Homeomorph.mulRight h).isOpenMap _ hWo)
  have hcovD : ∀ y : H, ∃ h ∈ D, y ∈ (fun x => x * h) '' W := by
    intro y
    have : y ∈ ⋃ h ∈ D, (fun x => x * h) '' W := by
      rw [hDU]; exact mem_iUnion.2 ⟨y, hcov y⟩
    simpa only [mem_iUnion, exists_prop] using this

  let μ : Measure G := haar
  let K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  let E : H → Set G := fun h => interior (K : Set G) ∩ f ⁻¹' ((fun x => x * h) '' W)
  have hEm : ∀ h, MeasurableSet (E h) := fun h =>
    isOpen_interior.measurableSet.inter (hf ((Homeomorph.mulRight h).isOpenMap _ hWo).measurableSet)
  have hUE : interior (K : Set G) ⊆ ⋃ h ∈ D, E h := by
    intro x hx
    obtain ⟨h, hD, hh⟩ := hcovD (f x)
    exact mem_iUnion₂.2 ⟨h, hD, hx, hh⟩
  obtain ⟨h₀, hD₀, hpos⟩ : ∃ h ∈ D, 0 < μ (E h) := by
    by_contra hno
    push Not at hno
    have hnull : μ (⋃ h ∈ D, E h) = 0 :=
      (measure_biUnion_null_iff hDc).2 fun h hh => nonpos_iff_eq_zero.1 (hno h hh)
    have hKpos : 0 < μ (interior (K : Set G)) := isOpen_interior.measure_pos μ K.interior_nonempty
    exact (lt_irrefl 0) (hKpos.trans_le ((measure_mono hUE).trans hnull.le))
  have hfin : μ (E h₀) ≠ ⊤ :=
    ((measure_mono (inter_subset_left.trans interior_subset)).trans_lt K.isCompact.measure_lt_top).ne

  have hnhds : E h₀ / E h₀ ∈ 𝓝 (1 : G) := div_mem_nhds_one_of_haar_pos_ne_top μ _ (hEm h₀) hpos hfin
  refine Filter.mem_map.2 (Filter.mem_of_superset hnhds ?_)
  rintro z ⟨a, ha, b, hb, rfl⟩
  obtain ⟨wa, hwa, hfa⟩ := ha.2
  obtain ⟨wb, hwb, hfb⟩ := hb.2
  show f (a / b) ∈ U
  rw [map_div, ← hfa, ← hfb, mul_div_mul_right_eq_div]
  exact hWU wa hwa wb hwb

theorem continuous_of_ae_eq_measurable {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [OpensMeasurableSpace H]
    [SecondCountableTopology H]
    (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop]
    (f : G →* H) (F : G → H) (hF : Measurable F) (hae : ∀ᵐ x ∂μ, f x = F x) : Continuous f := by
  classical
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨V, hV, hVU⟩ := exists_nhds_split_inv hU
  let W : Set H := interior V
  have hWo : IsOpen W := isOpen_interior
  have h1W : (1 : H) ∈ W := mem_interior_iff_mem_nhds.2 hV
  have hWU : ∀ v ∈ W, ∀ w ∈ W, v / w ∈ U := fun v hv w hw => hVU v (interior_subset hv) w (interior_subset hw)
  have hcov : ∀ h : H, h ∈ (fun x => x * h) '' W := fun h => ⟨1, h1W, one_mul h⟩
  obtain ⟨D, hDc, hDU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun h : H => (fun x => x * h) '' W)
    (fun h => (Homeomorph.mulRight h).isOpenMap _ hWo)
  have hcovD : ∀ y : H, ∃ h ∈ D, y ∈ (fun x => x * h) '' W := by
    intro y
    have : y ∈ ⋃ h ∈ D, (fun x => x * h) '' W := by
      rw [hDU]; exact mem_iUnion.2 ⟨y, hcov y⟩
    simpa only [mem_iUnion, exists_prop] using this

  obtain ⟨S, hSm, hSμ, hSsub⟩ : ∃ S : Set G, MeasurableSet S ∧ μ Sᶜ = 0 ∧ ∀ x ∈ S, f x = F x := by
    have h0 : μ {x | f x = F x}ᶜ = 0 := by
      rw [ae_iff] at hae; simpa [compl_setOf] using hae
    refine ⟨(toMeasurable μ {x | f x = F x}ᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact h0
    · intro x hx
      by_contra hne
      exact hx (subset_toMeasurable _ _ hne)
  let K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  let E : H → Set G := fun h => (interior (K : Set G) ∩ S) ∩ F ⁻¹' ((fun x => x * h) '' W)
  have hEm : ∀ h, MeasurableSet (E h) := fun h =>
    (isOpen_interior.measurableSet.inter hSm).inter (hF ((Homeomorph.mulRight h).isOpenMap _ hWo).measurableSet)
  have hUE : interior (K : Set G) ∩ S ⊆ ⋃ h ∈ D, E h := by
    intro x hx
    obtain ⟨h, hD, hh⟩ := hcovD (F x)
    exact mem_iUnion₂.2 ⟨h, hD, hx, hh⟩
  have hKSpos : 0 < μ (interior (K : Set G) ∩ S) := by
    have h1 : μ (interior (K : Set G)) ≤ μ (interior (K : Set G) ∩ S) + μ Sᶜ := by
      calc μ (interior (K : Set G)) ≤ μ ((interior (K : Set G) ∩ S) ∪ Sᶜ) :=
            measure_mono (fun x hx => by by_cases hs : x ∈ S <;> simp [hx, hs])
        _ ≤ μ (interior (K : Set G) ∩ S) + μ Sᶜ := measure_union_le _ _
    rw [hSμ, add_zero] at h1
    exact (isOpen_interior.measure_pos μ K.interior_nonempty).trans_le h1
  obtain ⟨h₀, hD₀, hpos⟩ : ∃ h ∈ D, 0 < μ (E h) := by
    by_contra hno
    push Not at hno
    have hnull : μ (⋃ h ∈ D, E h) = 0 :=
      (measure_biUnion_null_iff hDc).2 fun h hh => nonpos_iff_eq_zero.1 (hno h hh)
    exact (lt_irrefl 0) (hKSpos.trans_le ((measure_mono hUE).trans hnull.le))
  have hfin : μ (E h₀) ≠ ⊤ :=
    ((measure_mono ((inter_subset_left.trans inter_subset_left).trans interior_subset)).trans_lt
      K.isCompact.measure_lt_top).ne
  have hnhds : E h₀ / E h₀ ∈ 𝓝 (1 : G) := div_mem_nhds_one_of_haar_pos_ne_top μ _ (hEm h₀) hpos hfin
  refine Filter.mem_map.2 (Filter.mem_of_superset hnhds ?_)
  rintro z ⟨a, ha, b, hb, rfl⟩
  obtain ⟨wa, hwa, hfa⟩ := ha.2
  obtain ⟨wb, hwb, hfb⟩ := hb.2
  show f (a / b) ∈ U
  rw [map_div, hSsub a ha.1.2, hSsub b hb.1.2, ← hfa, ← hfb, mul_div_mul_right_eq_div]
  exact hWU wa hwa wb hwb

theorem continuous_of_eqOn_measurable {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [T2Space G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [OpensMeasurableSpace H]
    [SecondCountableTopology H]
    (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop]
    (f : G →* H) (F : G → H) (hF : Measurable F) (S : Set G) (hS : MeasurableSet S) (hSpos : 0 < μ S) (hSfin : μ S ≠ ⊤)
    (hfS : ∀ x ∈ S, f x = F x) : Continuous f := by
  classical
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨V, hV, hVU⟩ := exists_nhds_split_inv hU
  let W : Set H := interior V
  have hWo : IsOpen W := isOpen_interior
  have h1W : (1 : H) ∈ W := mem_interior_iff_mem_nhds.2 hV
  have hWU : ∀ v ∈ W, ∀ w ∈ W, v / w ∈ U := fun v hv w hw => hVU v (interior_subset hv) w (interior_subset hw)
  have hcov : ∀ h : H, h ∈ (fun x => x * h) '' W := fun h => ⟨1, h1W, one_mul h⟩
  obtain ⟨D, hDc, hDU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun h : H => (fun x => x * h) '' W)
    (fun h => (Homeomorph.mulRight h).isOpenMap _ hWo)
  have hcovD : ∀ y : H, ∃ h ∈ D, y ∈ (fun x => x * h) '' W := by
    intro y
    have : y ∈ ⋃ h ∈ D, (fun x => x * h) '' W := by
      rw [hDU]; exact mem_iUnion.2 ⟨y, hcov y⟩
    simpa only [mem_iUnion, exists_prop] using this

  obtain ⟨C, hCS, hC, hCpos⟩ := hS.exists_lt_isCompact_of_ne_top hSfin hSpos
  let E : H → Set G := fun h => (C ∩ S) ∩ F ⁻¹' ((fun x => x * h) '' W)
  have hEm : ∀ h, MeasurableSet (E h) := fun h =>
    (hC.measurableSet.inter hS).inter (hF ((Homeomorph.mulRight h).isOpenMap _ hWo).measurableSet)
  have hUE : C ∩ S ⊆ ⋃ h ∈ D, E h := by
    intro x hx
    obtain ⟨h, hD, hh⟩ := hcovD (F x)
    exact mem_iUnion₂.2 ⟨h, hD, hx, hh⟩
  have hCSpos : 0 < μ (C ∩ S) := by rwa [inter_eq_left.2 hCS]
  obtain ⟨h₀, hD₀, hpos⟩ : ∃ h ∈ D, 0 < μ (E h) := by
    by_contra hno
    push Not at hno
    have hnull : μ (⋃ h ∈ D, E h) = 0 :=
      (measure_biUnion_null_iff hDc).2 fun h hh => nonpos_iff_eq_zero.1 (hno h hh)
    exact (lt_irrefl 0) (hCSpos.trans_le ((measure_mono hUE).trans hnull.le))
  have hfin : μ (E h₀) ≠ ⊤ :=
    ((measure_mono (inter_subset_left.trans inter_subset_left)).trans_lt hC.measure_lt_top).ne
  have hnhds : E h₀ / E h₀ ∈ 𝓝 (1 : G) := div_mem_nhds_one_of_haar_pos_ne_top μ _ (hEm h₀) hpos hfin
  refine Filter.mem_map.2 (Filter.mem_of_superset hnhds ?_)
  rintro z ⟨a, ha, b, hb, rfl⟩
  obtain ⟨wa, hwa, hfa⟩ := ha.2
  obtain ⟨wb, hwb, hfb⟩ := hb.2
  show f (a / b) ∈ U
  rw [map_div, hfS a ha.1.2, hfS b hb.1.2, ← hfa, ← hfb, mul_div_mul_right_eq_div]
  exact hWU wa hwa wb hwb

end AutoCont

set_option autoImplicit false

noncomputable section

open Matrix NumberField

namespace WsF
namespace AC

section Sec

variable {A : Type*} [CommRing A]

def dsec (a : Aˣ) : GL (Fin 2) A where
  val := Matrix.diagonal ![(a : A), 1]
  inv := Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

theorem val_dsec (a : Aˣ) : ((dsec a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![(a : A), 1] := rfl

theorem val_inv_dsec (a : Aˣ) :
    (((dsec a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1] := rfl

theorem det_dsec (a : Aˣ) : Matrix.GeneralLinearGroup.det (dsec a) = a := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_dsec, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem continuous_dsec [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (dsec : Aˣ → GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun a : Aˣ => ((dsec a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
    simp only [val_dsec]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using Units.continuous_val
    · simpa using continuous_const
  · show Continuous fun a : Aˣ => (((dsec a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
    simp only [val_inv_dsec]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using Units.continuous_coe_inv
    · simpa using continuous_const

end Sec

theorem continuous_of_continuous_comp_det {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (χ : (AdeleRing R K)ˣ →* ℂˣ)
    (h : Continuous fun g : AutomorphicForm.AdelicGL2 R K => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) :
    Continuous fun a : (AdeleRing R K)ˣ => ((χ a : ℂˣ) : ℂ) := by
  have he : (fun a : (AdeleRing R K)ˣ => ((χ a : ℂˣ) : ℂ)) =
      (fun g : AutomorphicForm.AdelicGL2 R K => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) ∘
        (dsec : (AdeleRing R K)ˣ → GL (Fin 2) (AdeleRing R K)) := by
    funext a
    simp only [Function.comp_apply, det_dsec]
  rw [he]
  exact h.comp continuous_dsec

theorem exists_globalPoints_det_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (u : Kˣ) :
    ∃ γ : GL (Fin 2) K, Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints R K γ) =
      Units.map (↑(algebraMap K (AdeleRing R K)) : K →* AdeleRing R K) u := by
  refine ⟨dsec u, ?_⟩
  rw [AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map_det, det_dsec]

end WsF.AC

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutoContMain
open AutomorphicForm

noncomputable def psiOf {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (χ : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL2 R K →* ℂ :=
  (Units.coeHom ℂ).comp (χ.comp Matrix.GeneralLinearGroup.det)

theorem coe_psiOf {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (χ : (AdeleRing R K)ˣ →* ℂˣ) : ⇑(psiOf χ) = chiDet R K χ := rfl

end AutoContMain

open AutoContMain AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (r : AdelicGL2 (𝓞 K) K → ℂ)
    (_hr : r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK)
    (_hra : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r) :
    r ∈ Submodule.span ℂ ((fun χ => chiDet (𝓞 K) K χ) '' {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}) := by
  classical

  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI hHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI hReg : (adelicGLHaar (Fin 2) (𝓞 K) K).Regular := by unfold adelicGLHaar; infer_instance
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  have hr := _hr
  unfold residualSpan at hr
  rw [Submodule.mem_span_set] at hr
  obtain ⟨cf, hcf, hsum⟩ := hr
  have hgen : ∀ φ ∈ cf.support, ∃ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧ φ = chiDet (𝓞 K) K χ := fun φ hφ => hcf hφ
  choose χof hχsq hχeq using hgen

  let n : ℕ := cf.support.card
  let e : Fin n ≃ ↥cf.support := cf.support.equivFin.symm
  let χi : Fin n → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun i => χof (e i : AdelicGL2 (𝓞 K) K → ℂ) (e i).2
  let c : Fin n → ℂ := fun i => cf (e i)
  let ψ : Fin n → (AdelicGL2 (𝓞 K) K →* ℂ) := fun i => psiOf (χi i)
  have hψφ : ∀ i, ⇑(ψ i) = ((e i : ↥cf.support) : AdelicGL2 (𝓞 K) K → ℂ) := fun i => by
    rw [show ⇑(ψ i) = chiDet (𝓞 K) K (χi i) from rfl]; exact (hχeq _ (e i).2).symm
  have hc : ∀ i, c i ≠ 0 := fun i => Finsupp.mem_support_iff.1 (e i).2
  have hψinj : Function.Injective ψ := by
    intro i j hij
    have : ((e i : ↥cf.support) : AdelicGL2 (𝓞 K) K → ℂ) = (e j : ↥cf.support) := by rw [← hψφ i, ← hψφ j, hij]
    exact e.injective (Subtype.ext this)

  have hr_sum : r = ∑ i : Fin n, c i • (⇑(ψ i) : AdelicGL2 (𝓞 K) K → ℂ) := by
    rw [← hsum]
    show (∑ φ ∈ cf.support, cf φ • φ) = _
    rw [← Finset.sum_coe_sort cf.support, ← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψφ]
  have hr_fun : r = fun g => ∑ i : Fin n, c i * ψ i g := by
    rw [hr_sum]; funext g; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hLs := ((lsXiMemberAt_iff (𝓞 K) K _ _ ξK _ r).1 _hra).1
  have hli : LinearIndependent ℂ (fun i : Fin n => (⇑(ψ i) : AdelicGL2 (𝓞 K) K → ℂ)) :=
    (linearIndependent_monoidHom (AdelicGL2 (𝓞 K) K) ℂ).comp ψ hψinj
  have hKtriv : ∀ i, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χi i z = 1 := by
    intro i z hz
    obtain ⟨u, rfl⟩ := hz
    obtain ⟨γ, hγ⟩ := WsF.AC.exists_globalPoints_det_eq (R := 𝓞 K) (K := K) u

    have hinv : ∀ g, r (globalPoints (𝓞 K) K γ * g) = r g := fun g => hLs.left_invariant γ g
    have hrel : ∑ i : Fin n, (c i * ψ i (globalPoints (𝓞 K) K γ) - c i) • (⇑(ψ i) : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
      funext g
      have := hinv g
      rw [hr_fun] at this
      simp only [map_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa [mul_assoc] using this
    have hcoef := (Fintype.linearIndependent_iff.1 hli) _ hrel i
    have h1 : ψ i (globalPoints (𝓞 K) K γ) = 1 := by
      have : c i * (ψ i (globalPoints (𝓞 K) K γ) - 1) = 0 := by rw [mul_sub, mul_one]; exact hcoef
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hc i))

    have : ((χi i (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ)) : ℂˣ) : ℂ) = 1 := h1
    rw [hγ] at this
    exact Units.val_eq_one.1 this

  obtain ⟨-, -, -, hslab, hFD⟩ := canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hae : AEStronglyMeasurable r μ :=
    aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ (canonicalTruncationDomain K α β)
      hslab hFD ξK r _hra
  have hae' : AEStronglyMeasurable (fun g => ∑ i : Fin n, c i * ψ i g) μ := by rwa [hr_fun] at hae
  have hcont : ∀ i, Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => ((χi i a : ℂˣ) : ℂ) := by
    intro i
    have hψae : AEStronglyMeasurable (⇑(ψ i)) μ :=
      MeasureTheory.aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom μ ψ hψinj c hc hae' i
    obtain ⟨Fm, hFm, hFae⟩ := hψae

    letI : MeasurableSpace ℂˣ := borel ℂˣ
    haveI : BorelSpace ℂˣ := ⟨rfl⟩
    haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
    let f : AdelicGL2 (𝓞 K) K →* ℂˣ := (χi i).comp Matrix.GeneralLinearGroup.det
    let F : AdelicGL2 (𝓞 K) K → ℂˣ := fun g => if h : Fm g ≠ 0 then Units.mk0 (Fm g) h else 1
    have hFval : (fun g => ((F g : ℂˣ) : ℂ)) = fun g => if Fm g ≠ 0 then Fm g else 1 := by
      funext g; by_cases h : Fm g ≠ 0 <;> simp [F, h]
    have hFmeas : Measurable F := by
      refine ((Units.isOpenEmbedding_val (R := ℂ)).measurableEmbedding.measurable_comp_iff).1 ?_
      show Measurable fun g => ((F g : ℂˣ) : ℂ)
      rw [hFval]
      exact Measurable.ite (hFm.measurable (measurableSet_singleton 0)).compl hFm.measurable measurable_const
    have hfF : ∀ᵐ g ∂μ, f g = F g := by
      filter_upwards [hFae] with g hg
      have hne : Fm g ≠ 0 := by
        rw [← hg]; exact (χi i (Matrix.GeneralLinearGroup.det g)).ne_zero
      apply Units.ext
      show ((χi i (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = ((F g : ℂˣ) : ℂ)
      rw [congrFun hFval g, if_pos hne, ← hg]
      rfl
    have hfc : Continuous f := AutoCont.continuous_of_ae_eq_measurable μ f F hFmeas hfF
    exact WsF.AC.continuous_of_continuous_comp_det (R := 𝓞 K) (K := K) (χi i) (Units.continuous_val.comp hfc)

  rw [hr_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨χi i, ⟨?_, hKtriv i, hcont i⟩, ?_⟩)
  · exact hχsq _ (e i).2
  · exact (hψφ i ▸ (hχeq _ (e i).2).symm : chiDet (𝓞 K) K (χi i) = ⇑(ψ i))

end
end S_AutomorphicForm_mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
end P2MW
export P2MW.S_AutomorphicForm_mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt (solution)
