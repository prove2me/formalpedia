-- Prove2me | solution 1 for AutomorphicForm.exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/cb934b49-8ae2-50bf-abb0-e2cc0900b674

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
import Definitions.Def_NumberField_NormPowChar
import Mathlib
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_exists_residualProjection_mem_span_chiDet_principalLevel_archCutSubmodule_and_ae_eq_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_ae_constantTerm_eq_zero_of_mem_residualSpan_slab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ENNReal

noncomputable section

namespace Ws31
namespace L2Kit

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

theorem memLp_conj {f : X → ℂ} {p : ℝ≥0∞} (hf : MemLp f p ν) : MemLp (fun x => conj (f x)) p ν := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf.1, ?_⟩
  have : eLpNorm (fun x => conj (f x)) p ν = eLpNorm f p ν :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => RCLike.norm_conj _)
  rw [this]; exact hf.2

theorem integrable_mul_conj {f g : X → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x => f x * conj (g x)) ν := by
  have h := MemLp.integrable_mul hf (memLp_conj ν hg)
  exact h

theorem integrable_mul' {f g : X → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x => f x * g x) ν :=
  MemLp.integrable_mul hf hg

theorem norm_integral_mul_conj_le (f g : X → ℂ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ‖∫ x, f x * conj (g x) ∂ν‖ ≤ (eLpNorm f 2 ν).toReal * (eLpNorm g 2 ν).toReal := by
  have h1 : ∫ x, f x * conj (g x) ∂ν = inner ℂ (hg.toLp g) (hf.toLp f) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply, mul_comm]
  rw [h1]
  calc ‖inner ℂ (hg.toLp g) (hf.toLp f)‖ ≤ ‖hg.toLp g‖ * ‖hf.toLp f‖ := norm_inner_le_norm _ _
    _ = (eLpNorm f 2 ν).toReal * (eLpNorm g 2 ν).toReal := by rw [Lp.norm_toLp, Lp.norm_toLp, mul_comm]

theorem integral_sub_mul_conj {f g h : X → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (hh : MemLp h 2 ν) :
    ∫ x, (f x - g x) * conj (h x) ∂ν = ∫ x, f x * conj (h x) ∂ν - ∫ x, g x * conj (h x) ∂ν := by
  rw [← integral_sub (integrable_mul_conj ν hf hh) (integrable_mul_conj ν hg hh)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [sub_mul]

theorem integral_add_mul_conj {f g h : X → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (hh : MemLp h 2 ν) :
    ∫ x, (f x + g x) * conj (h x) ∂ν = ∫ x, f x * conj (h x) ∂ν + ∫ x, g x * conj (h x) ∂ν := by
  rw [← integral_add (integrable_mul_conj ν hf hh) (integrable_mul_conj ν hg hh)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_mul]

theorem integral_mul_conj_comm (f g : X → ℂ) :
    ∫ x, g x * conj (f x) ∂ν = conj (∫ x, f x * conj (g x) ∂ν) := by
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem eLpNorm_sub_le_add_of_le {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g h : X → E} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hh : AEStronglyMeasurable h ν) {a b : ℝ≥0∞}
    (h1 : eLpNorm (f - g) p ν ≤ a) (h2 : eLpNorm (g - h) p ν ≤ b) :
    eLpNorm (f - h) p ν ≤ a + b := by
  have : f - h = (f - g) + (g - h) := by abel
  rw [this]
  exact (eLpNorm_add_le (hf.sub hg) (hg.sub hh) hp).trans (add_le_add h1 h2)

theorem integral_mul_conj_congr_ae_left {f f' g : X → ℂ} (h : f =ᵐ[ν] f') :
    ∫ x, f x * conj (g x) ∂ν = ∫ x, f' x * conj (g x) ∂ν :=
  integral_congr_ae (h.mono fun x hx => by simp only [hx])

end Ws31.L2Kit

namespace Ws31
namespace ThreeWay

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

abbrev P0 (α β : ℝ) : CarrierPins K :=
  productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
    (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

abbrev P1 (α β : ℝ) : CarrierPins K :=
  productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
    (fun M => levelOne (𝓞 K) K M) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

theorem isAutomorphicFnAt_P0_iff (α β : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) :
    IsAutomorphicFnAt K (P0 K α β) ξ f ↔ IsAutomorphicFnAt K (P1 K α β) ξ f := Iff.rfl

theorem continuous_xi (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) :
    Continuous ξK := by
  have hval : Continuous fun z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) => ((ξK z : ℂˣ) : ℂ) := by
    have : (fun z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) => ((ξK z : ℂˣ) : ℂ)) =
        (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∘ Subtype.val := by
      funext z; rfl
    rw [this]; exact hξc.comp continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have : (fun z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) => (((ξK z)⁻¹ : ℂˣ) : ℂ)) =
      fun z => (((ξK z : ℂˣ) : ℂ))⁻¹ := by
    funext z; exact Units.val_inv_eq_inv_val _
  rw [this]
  exact hval.inv₀ fun z => Units.ne_zero _

theorem isAutomorphicFnAt_sub (α β : ℝ) (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (u w : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsAutomorphicFnAt K (P0 K α β) ξK u)
    (hw : IsAutomorphicFnAt K (P0 K α β) ξK w) :
    IsAutomorphicFnAt K (P0 K α β) ξK (u - w) := by
  have huL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
  have hwL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hw
  refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, huL.2.sub hwL.2⟩
  · simp only [Pi.sub_apply, huL.1.left_invariant γ g, hwL.1.left_invariant γ g]
  · simp only [Pi.sub_apply, huL.1.central_transform z g, hwL.1.central_transform z g, mul_sub]

end Ws31.ThreeWay

open AutomorphicForm Ws31.ThreeWay in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hψ : AutomorphicForm.IsSlabProfile K
      (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)).Z ξK ψ)
    (_hθN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, AutomorphicForm.pseudoEisenstein K ψ (g * u') = AutomorphicForm.pseudoEisenstein K ψ g)
    (_hθt : AutomorphicForm.pseudoEisenstein K ψ ∈ archCutSubmodule K tysK)
    (pψ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK pψ)
    (_hpψc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)).Z ξK,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK r ∧ eLpNorm (pψ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
    (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK h →
      h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)).Z ξK →
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) :
    letI := adeleBorel (𝓞 K) K
    ∃ (uc ur ue : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc) (_huc0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc g = 0))
      (_hur : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur)
      (_hurc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue)
      (_hueo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum : AutomorphicForm.pseudoEisenstein K ψ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc + ur + ue),
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ue (g * u') = ue g) ∧
    ue ∈ archCutSubmodule K tysK ∧
    ue =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))]
      (fun g => AutomorphicForm.pseudoEisenstein K ψ g - pψ g) := by

  obtain ⟨-, -, -, hΦs, hΦfd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ

  have hθ : IsAutomorphicFnAt K (P0 K α β) ξK (AutomorphicForm.pseudoEisenstein K ψ) :=
    AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ _ hΦs hΦfd ξK ψ _hψ

  obtain ⟨p, hp, ⟨hpc, hpo⟩, hpspan, -, -, hpN, hpt, hpuniq⟩ :=
    AutomorphicForm.exists_residualProjection_mem_span_chiDet_principalLevel_archCutSubmodule_and_ae_eq_of_isAutomorphicFnAt
      K α β hα hαβ ξK hξc hξt hξu N hN tysK (AutomorphicForm.pseudoEisenstein K ψ) hθ _hθN _hθt
  have hae : pψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] p :=
    hpuniq pψ _hpψ ⟨_hpψc, _hpψo⟩

  have hpres : p ∈ AutomorphicForm.residualSpan (𝓞 K) K (P0 K α β).Z ξK := by
    refine Submodule.span_mono ?_ hpspan
    rintro φ ⟨χ, ⟨hχ, -, -⟩, rfl⟩
    exact ⟨χ, hχ, rfl⟩

  have hθ2 : MemLp (AutomorphicForm.pseudoEisenstein K ψ) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hθ).2
  have hp2 : MemLp p 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hp).2
  have hξcont : Continuous ξK := continuous_xi K ξK hξc
  refine ⟨fun _ => 0, p, AutomorphicForm.pseudoEisenstein K ψ - p, isAutomorphicFnAt_zero K (P0 K α β) ξK, ?_, hp, hpc,
    isAutomorphicFnAt_sub K α β ξK _ _ hθ hp, ?_, ?_, ?_, (archCutSubmodule K tysK).sub_mem _hθt hpt, ?_⟩
  ·
    letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
    exact Filter.Eventually.of_forall fun g => constantTerm_zero _ _ g
  ·
    intro h hh hcase
    have hh2 : MemLp h 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
      ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 hh).2
    rcases hcase with hcusp | hres
    · have h1 : ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
        (AutomorphicForm.ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
          K α β hα hαβ _ hΦs hΦfd ξK hξcont h hh).mp hcusp ψ _hψ
      have h2 : ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          h g * conj (p g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
        AutomorphicForm.setIntegral_mul_conj_eq_zero_of_ae_constantTerm_eq_zero_of_mem_residualSpan_slab
          K α β hα hαβ _ hΦs hΦfd ξK h hh hcusp p hp hpres
      have h3 : ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          p g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
        rw [Ws31.L2Kit.integral_mul_conj_comm, h2, map_zero]
      show ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          (AutomorphicForm.pseudoEisenstein K ψ - p) g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0
      simp only [Pi.sub_apply]
      rw [Ws31.L2Kit.integral_sub_mul_conj _ hθ2 hp2 hh2, h1, h3, sub_zero]
    · simpa only [Pi.sub_apply] using hpo h hh hres
  ·
    exact Filter.Eventually.of_forall fun g => by simp
  ·
    intro g u' hu'
    simp only [Pi.sub_apply, _hθN g u' hu', hpN g u' hu']
  ·
    filter_upwards [hae] with g hg
    simp only [Pi.sub_apply, hg]

end
end S_AutomorphicForm_exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_threeWay_principalLevel_archCutSubmodule_ae_eq_pseudoEisenstein_sub_residualProjection_slab (solution)
