-- Prove2me | solution 1 for AutomorphicForm.integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0497a4b0-18db-5784-8639-452ef34dbeb1

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_exists_forall_mem_canonicalTruncationDomain_pseudoEisenstein_eq_zero_of_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws31
namespace FiniteUnfoldCont

variable (F : Type) [Field F] [NumberField F]

abbrev slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

abbrev pins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

abbrev Γ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range

theorem globalPoints_mul_mem_slab_iff (a b : ℝ)
    (γ : Γ F) (g : AdelicGL2 (𝓞 F) F) : (γ : AdelicGL2 (𝓞 F) F) * g ∈ slab F a b ↔ g ∈ slab F a b := by
  obtain ⟨x, hx⟩ := γ.2
  have hdet : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ← hx, AutomorphicForm.ideleNorm_det_globalPoints x, one_mul]
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g)) ∈ Set.Icc a b ↔
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b
  rw [hdet]

theorem smulInvariantMeasure_slabHaar (a b : ℝ) (hslab : MeasurableSet (slab F a b)) :
    SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b)) := by
  have _ := hslab
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  have hpre : (fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' slab F a b = slab F a b := by
    ext g
    exact globalPoints_mul_mem_slab_iff F a b γ g
  have hmeas : MeasurableSet ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s) :=
    measurable_const_mul (γ : AdelicGL2 (𝓞 F) F) hs
  calc (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b) ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s)
      = adelicGLHaar (Fin 2) (𝓞 F) F ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s ∩ slab F a b) :=
        Measure.restrict_apply hmeas
    _ = adelicGLHaar (Fin 2) (𝓞 F) F ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' (s ∩ slab F a b)) := by
        rw [Set.preimage_inter, hpre]
    _ = adelicGLHaar (Fin 2) (𝓞 F) F (s ∩ slab F a b) :=
        measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (γ : AdelicGL2 (𝓞 F) F) _
    _ = (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b) s := (Measure.restrict_apply hs).symm

theorem countable_of_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

theorem countable_range_globalPoints : Countable (Γ F) := by
  haveI : Countable F := countable_of_numberField F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have hinj : Function.Injective
      (Units.val : (Matrix (Fin 2) (Fin 2) F)ˣ → Matrix (Fin 2) (Fin 2) F) := fun _ _ h => Units.ext h
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := hinj.countable
  exact Set.countable_coe_iff.2 (by rw [MonoidHom.coe_range]; exact Set.countable_range _)

variable {F}

def normChar {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} (ξ : Z →* ℂˣ) : Z →* ℂˣ where
  toFun z := Units.mk0 ((‖((ξ z : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    (by exact_mod_cast (norm_ne_zero_iff.2 (ξ z).ne_zero))
  map_one' := by ext; simp
  map_mul' z w := by ext; simp

@[scoped simp]
theorem normChar_apply_coe {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} (ξ : Z →* ℂˣ) (z : Z) :
    ((normChar ξ z : ℂˣ) : ℂ) = ((‖((ξ z : ℂˣ) : ℂ)‖ : ℝ) : ℂ) := rfl

private abbrev _root_.Ws31.FiniteUnfoldCont.normFn (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := fun g => ((‖φ g‖ : ℝ) : ℂ)

p2m_export "Ws31.FiniteUnfoldCont" "normFn"
namespace IsSlabProfile

private theorem _root_.Ws31.FiniteUnfoldCont.IsSlabProfile.normFn {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsSlabProfile F Z ξ φ) : IsSlabProfile F Z (normChar ξ) (Ws31.FiniteUnfoldCont.normFn φ) where
  measurable := Complex.measurable_ofReal.comp hφ.measurable.norm
  unipotent_mul x g := by simp [Ws31.FiniteUnfoldCont.normFn, hφ.unipotent_mul x g]
  borel_mul γ hγ g := by simp [Ws31.FiniteUnfoldCont.normFn, hφ.borel_mul γ hγ g]
  central_transform z g := by
    simp only [Ws31.FiniteUnfoldCont.normFn, hφ.central_transform z g, norm_mul, normChar_apply_coe,
      Complex.ofReal_mul]
  bounded_on_slab d₁ d₂ hd₁ := by
    obtain ⟨C, hC⟩ := hφ.bounded_on_slab d₁ d₂ hd₁
    exact ⟨C, fun g hg => by simpa [Ws31.FiniteUnfoldCont.normFn] using hC g hg⟩
  height_band := by
    obtain ⟨a, b, ha, hab⟩ := hφ.height_band
    exact ⟨a, b, ha, fun g hg => hab g (by simpa [Ws31.FiniteUnfoldCont.normFn] using hg)⟩

end IsSlabProfile
p2m_export "Ws31.FiniteUnfoldCont" "IsSlabProfile.normFn"
variable (F)

theorem integrable_main
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : IsLsXiFunction (𝓞 F) F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ f)
    (_hfc : Continuous f)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ) :
    Integrable (fun g : AdelicGL2 (𝓞 F) F =>
        AutomorphicForm.pseudoEisenstein F (fun x => ((‖φ x‖ : ℝ) : ℂ)) g * f g)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := by
  classical
  haveI : Countable F := countable_of_numberField F
  haveI : Countable (Γ F) := countable_range_globalPoints F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have hslab : MeasurableSet (slab F d₁ d₂) :=
    NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂
  haveI : SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) :=
    smulInvariantMeasure_slabHaar F d₁ d₂ hslab

  have hθabs : IsAutomorphicFnAt F (pins F Φ) (normChar ξ) (pseudoEisenstein F (normFn φ)) :=
    AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ (normChar ξ) (normFn φ)
      (IsSlabProfile.normFn _hφ)
  have hL := (lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z (normChar ξ) (pins F Φ).D
    (pseudoEisenstein F (normFn φ))).mp hθabs
  have hθinv : ∀ (γ : Γ F) (g : AdelicGL2 (𝓞 F) F),
      pseudoEisenstein F (normFn φ) ((γ : AdelicGL2 (𝓞 F) F) * g) = pseudoEisenstein F (normFn φ) g := by
    intro γ g
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    have h := hL.1.left_invariant γ₀ g
    rwa [hγ₀] at h
  have hθ2 : MemLp (pseudoEisenstein F (normFn φ)) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hL.2
  have hfinv : ∀ (γ : Γ F) (g : AdelicGL2 (𝓞 F) F), f ((γ : AdelicGL2 (𝓞 F) F) * g) = f g := by
    intro γ g
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    have h := _hf.left_invariant γ₀ g
    rwa [hγ₀] at h

  have hvol : adelicGLHaar (Fin 2) (𝓞 F) F Φ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      F d₁ d₂ _hd₁ _hd Φ _hΦ
    rwa [Set.inter_eq_left.mpr _hΦs] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := isFiniteMeasure_restrict.2 hvol.ne
  have hθint : Integrable (pseudoEisenstein F (normFn φ)) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
    hθ2.integrable one_le_two

  have hmeas : AEStronglyMeasurable (fun g : AdelicGL2 (𝓞 F) F => pseudoEisenstein F (normFn φ) g * f g)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
    hθint.aestronglyMeasurable.mul _hfc.aestronglyMeasurable

  obtain ⟨-, -, -, hDs, hD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F d₁ d₂ _hd₁ _hd
  obtain ⟨H, hH⟩ :=
    AutomorphicForm.exists_forall_mem_canonicalTruncationDomain_pseudoEisenstein_eq_zero_of_lt_adelicHeight
      F d₁ d₂ _hd₁ _hd (normChar ξ) (normFn φ) (IsSlabProfile.normFn _hφ)
  obtain ⟨C, hC, hDC⟩ :=
    AutomorphicForm.exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset F d₁ d₂ _hd₁ _hd H
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn _hfc.continuousOn

  have hpt : ∀ g ∈ canonicalTruncationDomain F d₁ d₂,
      ‖pseudoEisenstein F (normFn φ) g * f g‖ₑ ≤ ENNReal.ofReal M * ‖pseudoEisenstein F (normFn φ) g‖ₑ := by
    intro g hg
    by_cases hz : pseudoEisenstein F (normFn φ) g = 0
    · simp [hz]
    · have hle : NumberField.AdelicHeight.adelicHeight F g ≤ H := not_lt.1 fun hlt => hz (hH g hg hlt)
      have hgC : g ∈ C := hDC ⟨hg, hle⟩
      rw [enorm_mul, mul_comm, ← ofReal_norm (f g)]
      gcongr
      exact hM g hgC
  refine ⟨hmeas, hasFiniteIntegral_iff_enorm.2 ?_⟩
  calc ∫⁻ g, ‖pseudoEisenstein F (normFn φ) g * f g‖ₑ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)
      = ∫⁻ g in Φ, ‖pseudoEisenstein F (normFn φ) g * f g‖ₑ
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) := by
        rw [Measure.restrict_restrict_of_subset _hΦs]
    _ = ∫⁻ g in canonicalTruncationDomain F d₁ d₂, ‖pseudoEisenstein F (normFn φ) g * f g‖ₑ
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) :=
        _hΦ.setLIntegral_eq hD (fun g => ‖pseudoEisenstein F (normFn φ) g * f g‖ₑ) fun γ g => by
          simp only [Subgroup.smul_def, smul_eq_mul, hθinv, hfinv]
    _ ≤ ∫⁻ g in canonicalTruncationDomain F d₁ d₂, ENNReal.ofReal M * ‖pseudoEisenstein F (normFn φ) g‖ₑ
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem₀ hD.nullMeasurableSet] with g hg
        exact hpt g hg
    _ = ENNReal.ofReal M * ∫⁻ g in canonicalTruncationDomain F d₁ d₂, ‖pseudoEisenstein F (normFn φ) g‖ₑ
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M * ∫⁻ g in Φ, ‖pseudoEisenstein F (normFn φ) g‖ₑ
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) := by
        rw [hD.setLIntegral_eq _hΦ (fun g => ‖pseudoEisenstein F (normFn φ) g‖ₑ) fun γ g => by
          simp only [Subgroup.smul_def, smul_eq_mul, hθinv]]
    _ = ENNReal.ofReal M * ∫⁻ g, ‖pseudoEisenstein F (normFn φ) g‖ₑ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := by
        rw [Measure.restrict_restrict_of_subset _hΦs]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hasFiniteIntegral_iff_enorm.1 hθint.hasFiniteIntegral)

end Ws31.FiniteUnfoldCont
p2m_reactivate "P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31 P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31.FiniteUnfoldCont"
p2m_reactivate "P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31 P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31.FiniteUnfoldCont"

section

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

open AutomorphicForm in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : AutomorphicForm.IsLsXiFunction (𝓞 F) F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ f)
    (_hfc : Continuous f)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ) :
    Integrable (fun g : AdelicGL2 (𝓞 F) F =>
        AutomorphicForm.pseudoEisenstein F (fun x => ((‖φ x‖ : ℝ) : ℂ)) g * f g)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
  Ws31.FiniteUnfoldCont.integrable_main F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ f _hf _hfc φ _hφ

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31 P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31.FiniteUnfoldCont"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31 P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.Ws31.FiniteUnfoldCont"

end S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous (solution)
