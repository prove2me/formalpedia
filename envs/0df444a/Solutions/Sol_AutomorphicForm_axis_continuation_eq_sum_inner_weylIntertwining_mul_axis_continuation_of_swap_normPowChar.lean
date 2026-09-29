-- Prove2me | solution 1 for AutomorphicForm.axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/37b185a2-acd4-53a2-a48c-aae836803a29

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

import Theorems.Thm_AutomorphicForm_inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar
import Theorems.Thm_AutomorphicForm_forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero
import Theorems.Thm_AutomorphicForm_analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
import Theorems.Thm_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isArchKFinite_of_forall_exists_finiteDimensional_forall_mem
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Mathlib
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
noncomputable section

namespace Ws48
namespace Axis
open Filter

theorem limUnder_nhdsNE_eq_of_meromorphicOn_of_analyticOnNhd {f h : ℂ → ℂ} {O U : Set ℂ}
    (hf : MeromorphicOn f O) (hh : AnalyticOnNhd ℂ h O) (hO : IsPreconnected O)
    (hUo : IsOpen U) (hUO : U ⊆ O) (hUne : U.Nonempty) (heq : ∀ z ∈ U, f z = h z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O) :
    Filter.limUnder (𝓝[≠] z₀) f = h z₀ := by
  have hd : MeromorphicOn (f - h) O := fun x hx => (hf x hx).sub (hh x hx).meromorphicAt
  obtain ⟨z₁, hz₁⟩ := hUne
  have htop₁ : meromorphicOrderAt (f - h) z₁ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have : ∀ᶠ z in 𝓝 z₁, (f - h) z = 0 := by
      filter_upwards [hUo.mem_nhds hz₁] with z hz
      simp [heq z hz]
    exact this.filter_mono nhdsWithin_le_nhds
  have htop₀ : meromorphicOrderAt (f - h) z₀ = ⊤ := by
    by_contra hne
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected hO hz₀ (hUO hz₁) hne) htop₁
  rw [meromorphicOrderAt_eq_top_iff] at htop₀
  have hev : h =ᶠ[𝓝[≠] z₀] f := by
    filter_upwards [htop₀] with z hz
    have : f z - h z = 0 := hz
    exact (sub_eq_zero.1 this).symm
  have hcont : ContinuousAt h z₀ := (hh z₀ hz₀).continuousAt
  have ht : Filter.Tendsto f (𝓝[≠] z₀) (𝓝 (h z₀)) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
  exact ht.limUnder_eq

theorem integral_mul_conj_of_orthonormal {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    (e : Fin n → X → ℂ) (hint : ∀ i j, Integrable (fun x => e i x * conj (e j x)) μ)
    (hon : ∀ i j, ∫ x, e i x * conj (e j x) ∂μ = if i = j then 1 else 0)
    (c : Fin n → ℂ) (w : X → ℂ) (hw : ∀ x, w x = ∑ j, c j * e j x) :
    (∀ j, ∫ x, w x * conj (e j x) ∂μ = c j) ∧
    ∫ x, w x * conj (w x) ∂μ = ∑ j, (∫ x, w x * conj (e j x) ∂μ) * conj (∫ x, w x * conj (e j x) ∂μ) := by
  have hwj : ∀ j, (fun x => w x * conj (e j x)) = fun x => ∑ i, c i * (e i x * conj (e j x)) := by
    intro j; funext x
    rw [hw x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hintj : ∀ j, Integrable (fun x => w x * conj (e j x)) μ := by
    intro j; rw [hwj j]
    exact integrable_finsetSum _ fun i _ => (hint i j).const_mul (c i)
  have hcoef : ∀ j, ∫ x, w x * conj (e j x) ∂μ = c j := by
    intro j
    rw [hwj j, integral_finsetSum _ (fun i _ => (hint i j).const_mul (c i))]
    simp_rw [integral_const_mul, hon]
    simp
  refine ⟨hcoef, ?_⟩
  have hww : (fun x => w x * conj (w x)) = fun x => ∑ j, conj (c j) * (w x * conj (e j x)) := by
    funext x
    have : conj (w x) = ∑ j, conj (c j) * conj (e j x) := by
      rw [hw x, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul]
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hww, integral_finsetSum _ (fun j _ => (hintj j).const_mul (conj (c j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hcoef j, mul_comm]

section Eta
open AutomorphicForm NumberField.TateGlobal
variable (K : Type) [Field K] [NumberField K]

theorem cpowChar_mul_cpowChar (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (a b : ℂ) :
    cpowChar α hα a * cpowChar α hα b = cpowChar α hα (a + b) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val, cpowChar_apply_val,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]

theorem cpowChar_inv (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (a : ℂ) :
    (cpowChar α hα a)⁻¹ = cpowChar α hα (-a) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, cpowChar_apply_val, cpowChar_apply_val, Complex.cpow_neg]

theorem normPowChar_eq_cpowChar (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ))) (τ : ℝ) :
    normPowChar K τ = cpowChar (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (Complex.I * τ) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [coe_normPowChar_apply, cpowChar_apply_val]
  rfl

theorem etaFst_mul_normPowChar (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)))
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ) (s : ℂ) :
    etaFst (μ * normPowChar K τ) (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα s =
    etaFst μ (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [etaFst_apply, MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply, cpowChar_apply_val]
  have hx : ((((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hα x).ne'
  have hI : ((ideleNorm K x : ℝ) : ℂ) = (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ) := rfl
  rw [hI, mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2; ring

theorem etaSnd_mul_normPowChar_inv (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ) (s : ℂ) :
    etaSnd (ν * (normPowChar K τ)⁻¹) (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα s =
    etaSnd ν (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [etaSnd_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    coe_normPowChar_apply, cpowChar_apply_val]
  have hx : ((((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hα x).ne'
  have hI : ((ideleNorm K x : ℝ) : ℂ) = (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ) := rfl
  rw [hI, ← Complex.cpow_neg, mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2; ring

end Eta

section Ind
open AutomorphicForm
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem IsInducedSection.add' {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ} {φ ψ : AdelicGL2 R K → ℂ}
    (hφ : IsInducedSection R K χ₁ χ₂ φ) (hψ : IsInducedSection R K χ₁ χ₂ ψ) :
    IsInducedSection R K χ₁ χ₂ (fun g => φ g + ψ g) := by
  intro b hb g
  show φ (b * g) + ψ (b * g) = _ * (φ g + ψ g)
  rw [hφ b hb g, hψ b hb g]
  ring

theorem IsInducedSection.const_mul' {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ} {φ : AdelicGL2 R K → ℂ}
    (hφ : IsInducedSection R K χ₁ χ₂ φ) (c : ℂ) :
    IsInducedSection R K χ₁ χ₂ (fun g => c * φ g) := by
  intro b hb g
  show c * φ (b * g) = _ * (c * φ g)
  rw [hφ b hb g]
  ring

end Ind

end Ws48.Axis

end

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (e ē : ιE) (σ : ℝ)
      (_hsw : μ ē = ν e * NumberField.TateGlobal.normPowChar K σ ∧
        ν ē = μ e * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (j : Fin (nE e)) (t : ℝ) (g : AdelicGL2 (𝓞 K) K),
    EE e j ((t : ℂ) * Complex.I) g =
      ∑ j' : Fin (nE ē),
        (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
              NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
            conj (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE e ē σ _hsw j t g
  letI := adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 K) K

  have hNbot : N ≠ ⊥ := by
    intro hN0
    have hall : ∀ w : HeightOneSpectrum (𝓞 K), w ∈ SK := fun w => hN w (by
      rw [hN0, ← Ideal.zero_eq_bot]; exact dvd_zero _)
    have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
    have key : ∀ p : {p : ℕ // p.Prime}, ∃ w : HeightOneSpectrum (𝓞 K),
        w.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : ℤ)} := by
      intro p
      have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.2.ne_zero
      haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime hp0).2 (Nat.prime_iff_prime_int.1 p.2)
      obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {((p : ℕ) : ℤ)})
        (⊥ : Ideal (𝓞 K)) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
      have hQ0 : Q ≠ ⊥ := by
        intro h
        rw [h, Ideal.comap_bot_of_injective _ hinj] at hQc
        exact hp0 (Ideal.span_singleton_eq_bot.1 hQc.symm)
      exact ⟨⟨Q, hQ, hQ0⟩, hQc⟩
    choose f hf using key
    have hfinj : Function.Injective f := by
      intro p q hpq
      have h := hf p
      rw [hpq, hf q, Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
      exact Subtype.ext (by simpa using h.symm)
    haveI : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOf_prime.to_subtype
    exact (Set.infinite_of_injective_forall_mem hfinj (fun p => (Finset.mem_coe.2 (hall (f p)))))
      (Finset.finite_toSet SK)

  have hadm := AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
      K hαm (μ e) (ν e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e) N (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j)
      (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφElev e j) (OE e j) (EE e j) (NE e j) (_hEE e j) t
  obtain ⟨hUind, hUcont, hUlev, hUKu⟩ := hadm
  have hUty : (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) ∈ archCutSubmodule K tysK := by
    have h := AutomorphicForm.axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
      K tysK hαm (μ e) (ν e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e) (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j)
      (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφEty e j) (OE e j) (EE e j) (NE e j) (_hEE e j) t
    exact Submodule.smul_mem _ ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ h
  have es2 : ((-(t + σ) : ℝ) : ℂ) * Complex.I = (-((((t + σ : ℝ) : ℂ)) * Complex.I)) := by push_cast; ring
  have es3 : (-((((t + σ : ℝ) : ℂ)) * Complex.I)) + (σ : ℂ) * Complex.I = -((t : ℂ) * Complex.I) := by push_cast; ring
  have hUind' : IsInducedSection (𝓞 K) K (etaFst (μ ē) αm hαm (((-(t + σ) : ℝ) : ℂ) * Complex.I))
      (etaSnd (ν ē) αm hαm (((-(t + σ) : ℝ) : ℂ) * Complex.I)) (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) := by
    rw [es2, _hsw.1, _hsw.2, Ws48.Axis.etaFst_mul_normPowChar K hαm, Ws48.Axis.etaSnd_mul_normPowChar_inv K hαm, es3]
    exact hUind
  have hUK : IsArchKFinite K (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) :=
    AutomorphicForm.isArchKFinite_of_forall_exists_finiteDimensional_forall_mem K _ hUKu
  have hspan := _hφEspan ē (-(t + σ)) _ hUind' hUcont hUK (fun g u hu => by rw [hUlev g u hu]) hUty
  rw [es2] at hspan
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hspan

  have hUk : ∀ k : adelicMaximalCompact K, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) = ∑ j', c j' * φE ē j' 0 (k : AdelicGL2 (𝓞 K) K) := by
    intro k
    have := congrFun hc (k : AdelicGL2 (𝓞 K) K)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j' _ => by rw [_hφEflat ē j' _ k]
  have hφc : ∀ (j' : Fin (nE ē)) (s : ℂ), Continuous fun k : adelicMaximalCompact K => φE ē j' s (k : AdelicGL2 (𝓞 K) K) := fun j' s =>
    ((_hφEjc ē j').comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val
  have hint0 : ∀ i j', Integrable (fun k : adelicMaximalCompact K => φE ē i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE ē j' 0 (k : AdelicGL2 (𝓞 K) K)))
      (maximalCompactHaar K) := fun i j' =>
    ((hφc i 0).mul (Complex.continuous_conj.comp (hφc j' 0))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hcoef, -⟩ := Ws48.Axis.integral_mul_conj_of_orthonormal (maximalCompactHaar K)
    (fun j' (k : adelicMaximalCompact K) => φE ē j' 0 (k : AdelicGL2 (𝓞 K) K)) hint0 (_hφEon ē) c _ hUk
  have hcoef' : ∀ j', (∫ k, (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
      conj (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = c j' := by
    intro j'
    rw [← hcoef j']
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [_hφEflat ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) k]

  have hC1 := AutomorphicForm.inv_vol_sum_inner_axis_continuation_weylIntertwiningIntegral_mul_eq_self_of_swap_normPowChar
      K N hNbot tysK hαm (μ e) (ν e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e)
      (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφElev e j) (_hφEty e j)
      (OE e j) (EE e j) (NE e j) (_hEE e j) σ (μ ē) (ν ē) _hsw (_hμ ē) (_hν ē) (_hμic ē) (_hνic ē) (_hμc ē) (_hνc ē)
      (nE ē) (φE ē) (_hφE ē) (_hφEK ē) (_hφEf ē) (_hφEjc ē) (_hφEhol ē) (_hφEKu ē) (_hφEflat ē) (_hφElev ē) (_hφEty ē)
      (_hφEon ē) (_hφEspan ē) (OE ē) (EE ē) (NE ē) (_hEE ē) t
  simp only [hcoef'] at hC1

  have hCTe := AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family K hαm (μ e) (ν e)
      (_hμ e) (_hν e) (_hμic e) (_hνic e) (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j)
      (OE e j) (EE e j) (NE e j) (_hEE e j).1 (_hEE e j).2.1 (_hEE e j).2.2.2.1 (_hEE e j).2.2.2.2.1 (_hEE e j).2.2.2.2.2.1
      (_hEE e j).2.2.2.2.2.2.1 (_hEE e j).2.2.2.2.2.2.2.1 (_hEE e j).2.2.2.2.2.2.2.2.1 (_hEE e j).2.2.2.2.2.2.2.2.2
  have hCTē := fun j' => AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family K hαm (μ ē) (ν ē)
      (_hμ ē) (_hν ē) (_hμic ē) (_hνic ē) (φE ē j') (_hφE ē j') (_hφEK ē j') (_hφEf ē j') (_hφEjc ē j') (_hφEhol ē j') (_hφEKu ē j')
      (OE ē j') (EE ē j') (NE ē j') (_hEE ē j').1 (_hEE ē j').2.1 (_hEE ē j').2.2.2.1 (_hEE ē j').2.2.2.2.1 (_hEE ē j').2.2.2.2.2.1
      (_hEE ē j').2.2.2.2.2.2.1 (_hEE ē j').2.2.2.2.2.2.2.1 (_hEE ē j').2.2.2.2.2.2.2.2.1 (_hEE ē j').2.2.2.2.2.2.2.2.2
  have hmem_e : ((t : ℂ) * Complex.I) ∈ OE e j := (_hEE e j).2.2.1 (by simp)
  have hmem_ē : ∀ j', (-((((t + σ : ℝ) : ℂ)) * Complex.I)) ∈ OE ē j' := fun j' => (_hEE ē j').2.2.1 (by simp)

  obtain ⟨Cbox, hCboxc, hCboxsub⟩ := exists_isCompact_adelicBox_subset K
  have hν₀ : ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K) =
      ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • (adelicAddHaar (𝓞 K) K).restrict (adelicBox K) := rfl

  have hEcont : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s : ℂ), s ∈ OE e₀ j₀ → Continuous fun x : AdelicGL2 (𝓞 K) K => EE e₀ j₀ s x := by
    intro e₀ j₀ s hs
    exact ((_hEE e₀ j₀).2.2.2.2.2.2.1).comp_continuous (Continuous.prodMk continuous_const continuous_id)
      (fun x => ⟨hs, Set.mem_univ _⟩)
  have hInt : ∀ (F : AdelicGL2 (𝓞 K) K → ℂ), Continuous F → ∀ x : AdelicGL2 (𝓞 K) K,
      Integrable (fun q : AdeleRing (𝓞 K) K => F (AutomorphicForm.unipotentGL2 q * x))
        (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) := by
    intro F hF x
    have hc : Continuous fun q : AdeleRing (𝓞 K) K => F (AutomorphicForm.unipotentGL2 q * x) :=
      hF.comp ((AutomorphicForm.CuspidalSpectrum.continuous_unipotentGL2_adele K).mul continuous_const)
    rw [hν₀]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (adelicAddHaar_adelicBox_pos K).ne')
    exact ((hc.continuousOn.integrableOn_compact hCboxc).mono_set hCboxsub).integrable
  have hCT : ∀ x : AdelicGL2 (𝓞 K) K,
      AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun u => AutomorphicForm.unipotentGL2 u)
          (fun x : AdelicGL2 (𝓞 K) K => (EE e j ((t : ℂ) * Complex.I) x - ∑ j' : Fin (nE ē), c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x)) x = 0 := by
    intro x
    have h1 := hCTe.2.2 ((t : ℂ) * Complex.I) hmem_e x
    have h2 := fun j' => (hCTē j').2.2 (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (hmem_ē j') x
    simp only [AutomorphicForm.constantTerm, AutomorphicForm.constantTermIntegrand] at h1 h2 ⊢
    have hIe := hInt _ (hEcont e j ((t : ℂ) * Complex.I) hmem_e) x
    have hIē := fun j' => hInt _ (hEcont ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (hmem_ē j')) x
    rw [integral_sub hIe (integrable_finsetSum _ fun j' _ => (hIē j').const_mul (c j')),
      integral_finsetSum _ (fun j' _ => (hIē j').const_mul (c j'))]
    simp_rw [integral_const_mul]
    rw [h1]
    simp_rw [h2]
    have hU := congrFun hc x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hU
    have hC1x := hC1 x
    rw [Finset.mul_sum] at hC1x

    have : ∑ j' : Fin (nE ē), c j' * (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x) =
        (∑ j' : Fin (nE ē), c j' * φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x) + ∑ j' : Fin (nE ē), ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * (c j' * NE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j' _ => by ring
    rw [this, hU, hC1x]
    ring
  have hD := AutomorphicForm.forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero
    K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
    ι b cls hb hbn hbo hbs hbc ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol
    _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE e ē σ _hsw j t c hCT g
  simp only [hcoef']
  exact sub_eq_zero.1 hD

end S_AutomorphicForm_axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
end P2MW
export P2MW.S_AutomorphicForm_axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar (solution)
