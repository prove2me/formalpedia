-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_sub_residualProj_sub_mul_sum_integral_sum_inner_mul_axis_continuation_eq_zero_of_matched_paleyWiener_of_cuspBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3886243d-5416-581d-8c42-4d29245f4185

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
import Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_exists_forall_mem_canonicalTruncationDomain_pseudoEisenstein_eq_zero_of_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
import Theorems.Thm_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
import Theorems.Thm_AutomorphicForm_isArchKFinite_of_forall_exists_finiteDimensional_forall_mem
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_sub_residualProj_sub_mul_sum_integral_sum_inner_mul_axis_continuation_eq_zero_of_matched_paleyWiener_of_cuspBasis
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology ContDiff ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

set_option autoImplicit false

open MeasureTheory Filter NumberField
open scoped ComplexConjugate NNReal Topology

noncomputable section

namespace Ws48
namespace Axis

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

namespace Ws48
namespace WPW
open AutomorphicForm NumberField

theorem ne_bot_of_forall_dvd_mem (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK) : N ≠ ⊥ := by
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

theorem exists_meromorphicNF_weylIntertwining (K : Type) [Field K] [NumberField K]
    (hαm : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)))
    {ιP : Type} (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
    (hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
    (hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
    (hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
    (hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
    (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
    (hψf : ∀ e s, letI := adeleBorel (𝓞 K) K; IsInducedSection (𝓞 K) K
      (etaFst (μP e) (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hαm s)
      (etaSnd (νP e) (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hαm s) (ψf e s))
    (hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
    (hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
    (hψK : ∀ e s, IsArchKFinite K (ψf e s)) (hψsm : ∀ e s, IsKfSmooth K (ψf e s))
    (hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) :
    letI := adeleBorel (𝓞 K) K
    ∃ Mc : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ, ∀ (e : ιP) (g : AdelicGL2 (𝓞 K) K),
      MeromorphicNFOn (fun s : ℂ => Mc e s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re → Mc e s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf e s) g := by
  letI := adeleBorel (𝓞 K) K
  have H := fun (e : ιP) (g : AdelicGL2 (𝓞 K) K) =>
    AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family K hαm (μP e) (νP e)
      (hμ e) (hν e) (hμic e) (hνic e) (ψf e) (hψf e) (hψK e) (hψsm e) (hψjc e) (hψhol e) g
  choose M' hM' using H
  have C := fun (e : ιP) =>
    AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
      K hαm (μP e) (νP e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (ψf e) (hψf e) (hψK e) (hψsm e)
      (hψjc e) (hψhol e) (hψKu e)
  choose O Ec Nc hC using C
  refine ⟨fun e s g => toMeromorphicNFOn (M' e g) Set.univ s, fun e g => ⟨meromorphicNFOn_toMeromorphicNFOn _ _, ?_⟩⟩
  intro s hs
  obtain ⟨hOo, -, -, hOhalf, -, hNan, -, -, -, hNeq⟩ := hC e
  have hsO : s ∈ O e := hOhalf hs
  have hev : (fun z : ℂ => Nc e z g) =ᶠ[𝓝 s] M' e g := by
    have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [hNeq z hz g, (hM' e g).2 z hz]
  have han : AnalyticAt ℂ (M' e g) s := ((hNan g) s hsO).congr hev
  show toMeromorphicNFOn (M' e g) Set.univ s = _
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (hM' e g).1 (Set.mem_univ s),
    toMeromorphicNFAt_eq_self.2 han.meromorphicNFAt]
  exact (hM' e g).2 s hs

theorem decay_zero {G : Type} (C : Set G) (n : ℕ) (σ₀ : ℝ) :
    ∃ m : ℝ → ℝ, MeasureTheory.Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
      ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖(fun (_ : ℂ) (_ : G) => (0 : ℂ)) ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t :=
  ⟨fun _ => 0, MeasureTheory.integrable_zero _ _ _, ⟨0, fun _ => le_rfl⟩, fun σ' _ t g _ => by simp⟩

end Ws48.WPW

namespace Ws48
namespace WPW

theorem integral_mul_conj_eq_zero_of_forall_mem_of_closure {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f p : X → ℂ) (hf : MemLp f 2 μ) (hp : MemLp p 2 μ) (S : Set (X → ℂ))
    (hS : ∀ q ∈ S, MemLp q 2 μ ∧ ∫ x, f x * conj (q x) ∂μ = 0)
    (hcl : ∀ ε > (0:ℝ), ∃ q ∈ S, eLpNorm (p - q) 2 μ < ENNReal.ofReal ε) :
    ∫ x, f x * conj (p x) ∂μ = 0 := by
  set A : ℝ := (∫ x, ‖f x‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  have hpair : ∀ g : X → ℂ, MemLp g 2 μ →
      ‖∫ x, f x * conj (g x) ∂μ‖ ≤ A * (∫ x, ‖g x‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) := by
    intro g hg
    have h1 : ‖∫ x, f x * conj (g x) ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by beta_reduce; rw [norm_mul, RCLike.norm_conj])
    refine h1.trans ?_
    have hfn : MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) μ := by simpa using hf.norm
    have hgn : MemLp (fun x => ‖g x‖) (ENNReal.ofReal 2) μ := by simpa using hg.norm
    exact integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => norm_nonneg _) (Filter.Eventually.of_forall fun x => norm_nonneg _) hfn hgn
  have hB : ∀ g : X → ℂ, MemLp g 2 μ → (∫ x, ‖g x‖ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) = (eLpNorm g 2 μ).toReal := by
    intro g hg
    rw [MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hg,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)]
    norm_num
  have key : ∀ ε > (0:ℝ), ‖∫ x, f x * conj (p x) ∂μ‖ ≤ A * ε := by
    intro ε hε
    obtain ⟨q, hqS, hq⟩ := hcl ε hε
    obtain ⟨hqm, hq0⟩ := hS q hqS
    have hpq : MemLp (p - q) 2 μ := hp.sub hqm
    have hi1 : Integrable (fun x => f x * conj ((p - q) x)) μ := hf.integrable_mul hpq.star
    have hi2 : Integrable (fun x => f x * conj (q x)) μ := hf.integrable_mul hqm.star
    have hsplit : (∫ x, f x * conj (p x) ∂μ) = (∫ x, f x * conj ((p - q) x) ∂μ) + ∫ x, f x * conj (q x) ∂μ := by
      rw [← integral_add hi1 hi2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply, map_sub]; ring
    rw [hsplit, hq0, add_zero]
    refine (hpair _ hpq).trans ?_
    rw [hB _ hpq]
    refine mul_le_mul_of_nonneg_left ?_ hA0
    exact ENNReal.toReal_le_of_le_ofReal hε.le hq.le
  by_contra hne
  have hpos : 0 < ‖∫ x, f x * conj (p x) ∂μ‖ := norm_pos_iff.2 hne
  by_cases hA' : A = 0
  · have h1 := key 1 one_pos
    rw [hA', zero_mul] at h1
    linarith
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA')
    have h1 := key (‖∫ x, f x * conj (p x) ∂μ‖ / (2 * A)) (by positivity)
    have h2 : A * (‖∫ x, f x * conj (p x) ∂μ‖ / (2 * A)) = ‖∫ x, f x * conj (p x) ∂μ‖ / 2 := by
      field_simp
    rw [h2] at h1
    linarith

end Ws48.WPW

open AutomorphicForm in
theorem Ws48.WPW.bracket_eq
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (n : ℕ)
      (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φE j s))
      (_hφEK : ∀ j s, IsArchKFinite K (φE j s))
      (_hφEf : ∀ j s, IsKfSmooth K (φE j s))
      (_hφEjc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE j p.1 p.2))
      (_hφEhol : ∀ j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE j s g))
      (_hφEKu : ∀ j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE j s (g * u) = φE j s g)
      (_hφEty : ∀ j (s : ℂ), φE j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ i j, ∫ k, φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin n => φE j ((t : ℂ) * Complex.I)))
      (OE : Fin n → Set ℂ) (EE NE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (j : Fin n),
      IsOpen (OE j) ∧ IsPreconnected (OE j) ∧ {s : ℂ | s.re = 0} ⊆ (OE j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE j s g) (OE j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE j s g) (OE j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE j s g = φE j s g + ∑' ξ : K, φE j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE j s) g))
      (τ : ℝ) (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hem : μ' = μ * NumberField.TateGlobal.normPowChar K τ ∧ ν' = ν * (NumberField.TateGlobal.normPowChar K τ)⁻¹)
      (_hμ' : IsUnitaryChar (𝓞 K) K μ') (_hν' : IsUnitaryChar (𝓞 K) K ν')
      (_hμ'ic : IsIdeleClassChar (𝓞 K) K μ') (_hν'ic : IsIdeleClassChar (𝓞 K) K ν')
      (_hμ'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ))
      (_hν'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ))
      (ψ₁ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₁ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s) (ψ₁ s))
      (_hψ₁jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψ₁ p.1 p.2))
      (_hψ₁hol : ∀ g, Differentiable ℂ (fun s => ψ₁ s g))
      (_hψ₁K : ∀ s, IsArchKFinite K (ψ₁ s)) (_hψ₁sm : ∀ s, IsKfSmooth K (ψ₁ s))
      (_hψ₁Ku : ∀ (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψ₁ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψ₁lev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψ₁ s (g * u) = ψ₁ s g)
      (_hψ₁ty : ∀ (s : ℂ), ψ₁ s ∈ archCutSubmodule K tysK)
      (μ₂ ν₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hrev : μ₂ = ν' ∧ ν₂ = μ')
      (ψ₂ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₂ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ₂ αm hαm s) (etaSnd ν₂ αm hαm s) (ψ₂ s))
      (_hψ₂jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψ₂ p.1 p.2))
      (_hψ₂hol : ∀ g, Differentiable ℂ (fun s => ψ₂ s g))
      (_hψ₂K : ∀ s, IsArchKFinite K (ψ₂ s)) (_hψ₂sm : ∀ s, IsKfSmooth K (ψ₂ s))
      (_hψ₂Ku : ∀ (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψ₂ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψ₂lev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψ₂ s (g * u) = ψ₂ s g)
      (_hψ₂ty : ∀ (s : ℂ), ψ₂ s ∈ archCutSubmodule K tysK)
      (Mc₂ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hMc₂ : ∀ g : AdelicGL2 (𝓞 K) K, MeromorphicNFOn (fun s : ℂ => Mc₂ s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re → Mc₂ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψ₂ s) g)
      (a : AdelicGL2 (𝓞 K) K → ℂ) (_ha : Continuous a)
      (t : ℝ),
    (∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
      ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
        ∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I))) (fun s : ℂ => Mc₂ s (k : AdelicGL2 (𝓞 K) K)))
          ∂(maximalCompactHaar K) =
      ∑ j : Fin n,
        (∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
        conj ((∫ k, ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
                  conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
              ∫ k, ψ₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
                  conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
                    NE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
  intro αm hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc n φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan OE EE NE _hEE τ μ' ν' _hem _hμ' _hν' _hμ'ic _hν'ic _hμ'c _hν'c ψ₁ _hψ₁ _hψ₁jc _hψ₁hol _hψ₁K _hψ₁sm _hψ₁Ku _hψ₁lev _hψ₁ty μ₂ ν₂ _hrev ψ₂ _hψ₂ _hψ₂jc _hψ₂hol _hψ₂K _hψ₂sm _hψ₂Ku _hψ₂lev _hψ₂ty Mc₂ _hMc₂ a _ha t
  letI := adeleBorel (𝓞 K) K
  obtain ⟨hμ₂, hν₂⟩ := _hrev
  have _hψ₂' : ∀ s, IsInducedSection (𝓞 K) K (etaFst ν' αm hαm s) (etaSnd μ' αm hαm s) (ψ₂ s) := by
    rw [← hμ₂, ← hν₂]; exact _hψ₂
  clear _hψ₂
  obtain ⟨hμ', hν'⟩ := _hem

  obtain ⟨O₂, E₂, N₂, hC₂⟩ :=
    AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
      K hαm ν' μ' _hν' _hμ' _hν'ic _hμ'ic _hν'c _hμ'c ψ₂ _hψ₂' _hψ₂K _hψ₂sm _hψ₂jc _hψ₂hol _hψ₂Ku
  have hO₂pc := hC₂.2.1
  have hO₂ax := hC₂.2.2.1
  have hO₂half := hC₂.2.2.2.1
  have hN₂an := hC₂.2.2.2.2.2.1
  have hN₂eq := hC₂.2.2.2.2.2.2.2.2.2

  have hlim : ∀ g : AdelicGL2 (𝓞 K) K, Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I))) (fun s : ℂ => Mc₂ s g) =
      N₂ (-((t : ℂ) * Complex.I)) g := by
    intro g
    refine Ws48.Axis.limUnder_nhdsNE_eq_of_meromorphicOn_of_analyticOnNhd (O := O₂) (U := {s : ℂ | 1 / 2 < s.re})
      (((_hMc₂ g).1.meromorphicOn).mono_set (Set.subset_univ _)) (hN₂an g) hO₂pc
      (isOpen_lt continuous_const Complex.continuous_re) hO₂half ⟨1, by norm_num⟩
      (fun z hz => by rw [(_hMc₂ g).2 z hz, hN₂eq z hz g]) (hO₂ax (by simp))

  have hLint2 : (∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I))) (fun s : ℂ => Mc₂ s (k : AdelicGL2 (𝓞 K) K)))
        ∂(maximalCompactHaar K)) = ∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hlim]
  rw [hLint2]

  have e_neg : (((-t : ℝ) : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by push_cast; ring
  have e_negneg : -((((-t : ℝ) : ℂ)) * Complex.I) = (t : ℂ) * Complex.I := by push_cast; ring
  have hadm := AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
      K hαm ν' μ' _hν' _hμ' _hν'ic _hμ'ic _hν'c _hμ'c N ψ₂ _hψ₂' _hψ₂K _hψ₂sm _hψ₂jc _hψ₂hol _hψ₂Ku _hψ₂lev
      O₂ E₂ N₂ hC₂ (-t)
  rw [e_negneg, e_neg] at hadm
  obtain ⟨hW₂ind, hW₂cont, hW₂lev, hW₂Ku⟩ := hadm
  have hW₂ty : (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) ∈ archCutSubmodule K tysK := by
    have h := AutomorphicForm.axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
      K tysK hαm ν' μ' _hν' _hμ' _hν'ic _hμ'ic _hν'c _hμ'c ψ₂ _hψ₂' _hψ₂K _hψ₂sm _hψ₂jc _hψ₂hol _hψ₂Ku _hψ₂ty
      O₂ E₂ N₂ hC₂ (-t)
    rw [e_neg] at h
    exact Submodule.smul_mem _ ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ h

  have es' : (t : ℂ) * Complex.I + (τ : ℂ) * Complex.I = (((t + τ : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  have hWind : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((((t + τ : ℝ) : ℂ)) * Complex.I))
      (etaSnd ν αm hαm ((((t + τ : ℝ) : ℂ)) * Complex.I))
      (fun g : AdelicGL2 (𝓞 K) K => ψ₁ ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) := by
    have h1 : etaFst μ' αm hαm ((t : ℂ) * Complex.I) = etaFst μ αm hαm ((((t + τ : ℝ) : ℂ)) * Complex.I) := by
      rw [hμ', Ws48.Axis.etaFst_mul_normPowChar K hαm, es']
    have h2 : etaSnd ν' αm hαm ((t : ℂ) * Complex.I) = etaSnd ν αm hαm ((((t + τ : ℝ) : ℂ)) * Complex.I) := by
      rw [hν', Ws48.Axis.etaSnd_mul_normPowChar_inv K hαm, es']
    rw [← h1, ← h2]
    exact Ws48.Axis.IsInducedSection.add' (_hψ₁ _) hW₂ind
  have hψ₁c : Continuous (ψ₁ ((t : ℂ) * Complex.I)) :=
    _hψ₁jc.comp (Continuous.prodMk continuous_const continuous_id)
  have hWcont : Continuous (fun g : AdelicGL2 (𝓞 K) K => ψ₁ ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) :=
    hψ₁c.add hW₂cont
  have hWK : IsArchKFinite K (fun g : AdelicGL2 (𝓞 K) K => ψ₁ ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) := by
    refine AutomorphicForm.isArchKFinite_of_forall_exists_finiteDimensional_forall_mem K _ fun w => ?_
    obtain ⟨W₁, hW₁fd, hW₁⟩ := _hψ₁Ku w
    obtain ⟨W₂', hW₂fd, hW₂'⟩ := hW₂Ku w
    haveI := hW₁fd; haveI := hW₂fd
    refine ⟨W₁ ⊔ W₂', inferInstance, fun g => ?_⟩
    have : (fun k : ↥(archRowIsometrySubgroup K w) =>
        ψ₁ ((t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K)) + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (g * (k : AdelicGL2 (𝓞 K) K))) =
      (fun k : ↥(archRowIsometrySubgroup K w) => ψ₁ ((t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K))) +
      (fun k : ↥(archRowIsometrySubgroup K w) => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (g * (k : AdelicGL2 (𝓞 K) K))) := rfl
    rw [this]
    exact Submodule.add_mem_sup (hW₁ _ g) (hW₂' g)
  have hWlev : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      (fun g : AdelicGL2 (𝓞 K) K => ψ₁ ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) (g * u) =
      (fun g : AdelicGL2 (𝓞 K) K => ψ₁ ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) g := by
    intro g u hu
    show ψ₁ _ (g * u) + _ * N₂ _ (g * u) = ψ₁ _ g + _ * N₂ _ g
    rw [_hψ₁lev _ g u hu, hW₂lev g u hu]
  have hWty : (fun g : AdelicGL2 (𝓞 K) K => ψ₁ ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) ∈
      archCutSubmodule K tysK := Submodule.add_mem _ (_hψ₁ty _) hW₂ty

  have hspan := _hφEspan (t + τ) _ hWind hWcont hWK hWlev hWty
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hspan
  have hWk : ∀ k : adelicMaximalCompact K,
      ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) =
        ∑ j, c j * φE j 0 (k : AdelicGL2 (𝓞 K) K) := by
    intro k
    have := congrFun hc (k : AdelicGL2 (𝓞 K) K)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [_hφEflat j _ k]

  have hφc : ∀ (j : Fin n) (s : ℂ), Continuous fun k : adelicMaximalCompact K => φE j s (k : AdelicGL2 (𝓞 K) K) := fun j s =>
    ((_hφEjc j).comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val
  have hint0 : ∀ i j, Integrable (fun k : adelicMaximalCompact K => φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)))
      (maximalCompactHaar K) := fun i j =>
    ((hφc i 0).mul (Complex.continuous_conj.comp (hφc j 0))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hcoef, hpars⟩ := Ws48.Axis.integral_mul_conj_of_orthonormal (maximalCompactHaar K)
    (fun j (k : adelicMaximalCompact K) => φE j 0 (k : AdelicGL2 (𝓞 K) K)) hint0 _hφEon c _ hWk

  have hd : ∀ j : Fin n, c j = (∫ k, ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) + (∫ k, ψ₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
    intro j

    have hψ₂c : Continuous (ψ₂ (-((t : ℂ) * Complex.I))) :=
      _hψ₂jc.comp (Continuous.prodMk continuous_const continuous_id)
    have hK₁ : Integrable (fun k : adelicMaximalCompact K => ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
      ((hψ₁c.comp continuous_subtype_val).mul (Complex.continuous_conj.comp (hφc j _))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hK₂ : Integrable (fun k : adelicMaximalCompact K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
      ((hW₂cont.comp continuous_subtype_val).mul (Complex.continuous_conj.comp (hφc j _))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hcoefj : ∫ k : adelicMaximalCompact K, (ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) +
          ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        (∫ k : adelicMaximalCompact K, ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        ∫ k : adelicMaximalCompact K, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
      rw [← integral_add hK₁ hK₂]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [_hφEflat j ((((t + τ : ℝ) : ℂ)) * Complex.I) k]
      ring

    have hswap : ∫ k : adelicMaximalCompact K, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∫ k : adelicMaximalCompact K, ψ₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
            conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by

      set cτ : ℂ := (τ : ℂ) * Complex.I with hcτ
      obtain ⟨hOo, hOpc, hOax, hOhalf, hEan, hNan, hEc, hNc, hEeq, hNeq⟩ := _hEE j
      have hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s)
          (fun g : AdelicGL2 (𝓞 K) K => φE j (s + cτ) g) := fun s => by
        rw [hμ', hν', Ws48.Axis.etaFst_mul_normPowChar K hαm, Ws48.Axis.etaSnd_mul_normPowChar_inv K hαm]
        exact _hφE j _
      have hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE j (p.1 + cτ) p.2) :=
        (_hφEjc j).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
      have hφfhol : ∀ g : AdelicGL2 (𝓞 K) K, Differentiable ℂ (fun s => φE j (s + cτ) g) := fun g =>
        (_hφEhol j g).comp (differentiable_id.add_const _)
      have hφfKu : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
          FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
            (fun k : ↥(archRowIsometrySubgroup K w) => φE j (s + cτ) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W := fun w => by
        obtain ⟨W, h1, h2⟩ := _hφEKu j w
        exact ⟨W, h1, fun s g => h2 _ g⟩
      let eτ : ℂ ≃ₜ ℂ := Homeomorph.addRight cτ
      have hre : ∀ s : ℂ, (s + cτ).re = s.re := fun s => by simp [hcτ]
      have hEφ : IsOpen (eτ ⁻¹' OE j) ∧ IsPreconnected (eτ ⁻¹' OE j) ∧ {s : ℂ | s.re = 0} ⊆ (eτ ⁻¹' OE j) ∧
          {s : ℂ | 1 / 2 < s.re} ⊆ (eτ ⁻¹' OE j) ∧
          (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE j (s + cτ) g) (eτ ⁻¹' OE j)) ∧
          (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE j (s + cτ) g) (eτ ⁻¹' OE j)) ∧
          ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE j (p.1 + cτ) p.2) ((eτ ⁻¹' OE j) ×ˢ Set.univ) ∧
          ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE j (p.1 + cτ) p.2) ((eτ ⁻¹' OE j) ×ˢ Set.univ) ∧
          (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
            EE j (s + cτ) g = φE j (s + cτ) g + ∑' ξ : K, φE j (s + cτ) (adelicWeyl (𝓞 K) K
              * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
          (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
            NE j (s + cτ) g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (fun g : AdelicGL2 (𝓞 K) K => φE j (s + cτ) g) g) := by
        have hmem : ∀ s : ℂ, s ∈ eτ ⁻¹' OE j ↔ s + cτ ∈ OE j := fun s => Iff.rfl
        refine ⟨eτ.isOpen_preimage.2 hOo, eτ.isPreconnected_preimage.2 hOpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro s hs; exact (hmem s).2 (hOax (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hre, hs]))
        · intro s hs; exact (hmem s).2 (hOhalf (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hre]; exact hs))
        · intro g
          exact (hEan g).comp (analyticOnNhd_id.add analyticOnNhd_const) (fun s hs => hs)
        · intro g
          exact (hNan g).comp (analyticOnNhd_id.add analyticOnNhd_const) (fun s hs => hs)
        · refine hEc.comp (((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn) ?_
          intro p hp; exact ⟨hp.1, Set.mem_univ _⟩
        · refine hNc.comp (((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn) ?_
          intro p hp; exact ⟨hp.1, Set.mem_univ _⟩
        · intro s hs g; exact hEeq (s + cτ) (by rw [hre]; exact hs) g
        · intro s hs g; exact hNeq (s + cτ) (by rw [hre]; exact hs) g
      have h4 := AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
        K N hN hαm μ' ν' _hμ' _hν' _hμ'ic _hν'ic _hμ'c _hν'c
        (fun s (g : AdelicGL2 (𝓞 K) K) => φE j (s + cτ) g) hφf (fun s => _hφEK j _) (fun s => _hφEf j _) hφfjc hφfhol hφfKu
        (fun s g u hu => _hφElev j _ g u hu)
        ψ₂ _hψ₂' _hψ₂K _hψ₂sm _hψ₂jc _hψ₂hol _hψ₂Ku _hψ₂lev
        (eτ ⁻¹' OE j) (fun s g => EE j (s + cτ) g) (fun s g => NE j (s + cτ) g) hEφ O₂ E₂ N₂ hC₂ t
      simp only [hcτ] at h4
      rw [es'] at h4
      have h5 := congrArg (starRingEnd ℂ) h4
      rw [← integral_conj, ← integral_conj] at h5
      simp only [map_mul, Complex.conj_conj] at h5
      calc _ = ∫ k : adelicMaximalCompact K, conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
                (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) :=
              integral_congr_ae (Filter.Eventually.of_forall fun k => by ring)
        _ = _ := h5
        _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun k => by
                   show _ = ψ₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
                     conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
                       NE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                   rw [map_mul]; ring)
    rw [← hcoef j, hcoefj, hswap]

  have hac : Continuous fun k : adelicMaximalCompact K => a (k : AdelicGL2 (𝓞 K) K) := _ha.comp continuous_subtype_val
  have hψ₁c' : Continuous (ψ₁ ((t : ℂ) * Complex.I)) := _hψ₁jc.comp (Continuous.prodMk continuous_const continuous_id)
  have hI1 : Integrable (fun k : adelicMaximalCompact K => a (k : AdelicGL2 (𝓞 K) K) * conj (ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
    (hac.mul (Complex.continuous_conj.comp (hψ₁c'.comp continuous_subtype_val))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI2 : Integrable (fun k : adelicMaximalCompact K => a (k : AdelicGL2 (𝓞 K) K) * conj (N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) := by
    have hN2c : Continuous fun k : adelicMaximalCompact K => N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) := by
      have h : Continuous fun k : adelicMaximalCompact K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) :=
        hW₂cont.comp continuous_subtype_val
      have h2 : Continuous fun k : adelicMaximalCompact K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)) * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) :=
        continuous_const.mul h
      have hv : ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)) ≠ 0 := by
        exact_mod_cast (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos K).ne' (adelicAddHaar_adelicBox_lt_top K).ne).ne'
      convert h2 using 1
      funext k; rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    exact (hac.mul (Complex.continuous_conj.comp hN2c)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvolreal : conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ = ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ := by rw [map_inv₀, Complex.conj_ofReal]
  have hLHS : (∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
      ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * ∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (N₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj ((fun g : AdelicGL2 (𝓞 K) K => ψ₁ ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    rw [← integral_const_mul, ← integral_add hI1 (hI2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    beta_reduce
    rw [map_add, map_mul, hvolreal]
    ring
  rw [hLHS]
  have hintφ : ∀ j : Fin n, Integrable (fun k : adelicMaximalCompact K => a (k : AdelicGL2 (𝓞 K) K) * conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
    fun j => (hac.mul (Complex.continuous_conj.comp (hφc j _))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc (∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj ((fun g : AdelicGL2 (𝓞 K) K => ψ₁ ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * N₂ (-((t : ℂ) * Complex.I)) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      = ∫ k, ∑ j : Fin n, conj (c j) * (a (k : AdelicGL2 (𝓞 K) K) * conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        beta_reduce
        rw [hWk k, map_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_mul, _hφEflat j ((((t + τ : ℝ) : ℂ)) * Complex.I) k]; ring
    _ = ∑ j : Fin n, conj (c j) * ∫ k, a (k : AdelicGL2 (𝓞 K) K) * conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
        rw [integral_finsetSum _ (fun j _ => (hintφ j).const_mul _)]
        exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    _ = _ := Finset.sum_congr rfl fun j _ => by rw [hd j, mul_comm]

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
    ∃ κ : ℝ, 0 < κ ∧
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
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
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
          (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (ιX : Type) [Fintype ιX]
      (μX νX : ιX → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμX : ∀ e, IsUnitaryChar (𝓞 K) K (μX e)) (_hνX : ∀ e, IsUnitaryChar (𝓞 K) K (νX e))
      (_hμicX : ∀ e, IsIdeleClassChar (𝓞 K) K (μX e)) (_hνicX : ∀ e, IsIdeleClassChar (𝓞 K) K (νX e))
      (_hμcX : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μX e x : ℂˣ) : ℂ))
      (_hνcX : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νX e x : ℂˣ) : ℂ))
      (_hμνX : ∀ (e : ιX)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μX e (z : (AdeleRing (𝓞 K) K)ˣ) * νX e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rX : ιX → ιX) (_hrX : ∀ e, μX (rX e) = νX e ∧ νX (rX e) = μX e)
      (_hdistX : ∀ e e' : ιX, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μX e x ≠ μX e' x ∨ νX e x ≠ νX e' x)
      (_hdistPX : ∀ (i : ιP) (e : ιX), ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP i x ≠ μX e x ∨ νP i x ≠ νX e x)
      (emX : ιX → ιE) (τX : ιX → ℝ)
      (_hemX : ∀ e : ιX, μX e = μ (emX e) * NumberField.TateGlobal.normPowChar K (τX e) ∧
        νX e = ν (emX e) * (NumberField.TateGlobal.normPowChar K (τX e))⁻¹)
      (ψf' : ιP ⊕ ιX → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf' : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (Sum.elim μP μX e) αm hαm s) (etaSnd (Sum.elim νP νX e) αm hαm s) (ψf' e s))
      (_hψjc' : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf' e p.1 p.2))
      (_hψhol' : ∀ e g, Differentiable ℂ (fun s => ψf' e s g))
      (_hψK' : ∀ e s, IsArchKFinite K (ψf' e s)) (_hψsm' : ∀ e s, IsKfSmooth K (ψf' e s))
      (_hψKu' : ∀ (e : ιP ⊕ ιX) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf' e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψdec' : ∀ (e : ιP ⊕ ιX) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf' e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ' : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ' : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ')
      (_hψrep' : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ' g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf' e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψlev' : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf' i s (g * u) = ψf' i s g)
      (_hψty' : ∀ i (s : ℂ), ψf' i s ∈ archCutSubmodule K tysK),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        AutomorphicForm.pseudoEisenstein K ψ' g *
          conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g -
            (κ : ℂ) * ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0  := by
  intro αm hαm
  classical

  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  obtain ⟨c, hc0, hcT, hc⟩ := NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa K
  obtain ⟨D, hDm, hDF, -⟩ :=
    @NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow K _ _
      (NumberField.Idele.ideleBorel K) (NumberField.Idele.borelSpace_ideleBorel K) (NumberField.Idele.idelicHaar K)
      (NumberField.Idele.isHaarMeasure_idelicHaar K)
  obtain ⟨V, hV0, hVT, hV⟩ := NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi K D hDm hDF
  obtain ⟨κ'', hκ'', hCPW⟩ := AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ, C₀ = c.toReal * ((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal * V.toReal ^ 2 *
      Real.log (β / α) / (16 * Real.pi) := ⟨_, rfl⟩
  have hC₀pos : 0 < C₀ := by
    have h1 : 0 < c.toReal := ENNReal.toReal_pos hc0 hcT
    have h2 : 0 < ((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal :=
      ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos K).ne' (adelicAddHaar_adelicBox_lt_top K).ne
    have h3 : 0 < V.toReal := ENNReal.toReal_pos hV0 hVT
    have h4 : 0 < Real.log (β / α) := Real.log_pos ((one_lt_div hα).2 hαβ)
    rw [hC₀def]; positivity
  refine ⟨C₀ / κ'', div_pos hC₀pos hκ'', ?_⟩
  intro ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _ μP νP _hμ _hν _hμic _hνic _hμc _hμνP rP _hr _hdist ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνc _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty pψ _hpψ _hpψc _hpψo ιX _ μX νX _hμX _hνX _hμicX _hνicX _hμcX _hνcX _hμνX rX _hrX _hdistX _hdistPX emX τX _hemX ψf' _hψf' _hψjc' _hψhol' _hψK' _hψsm' _hψKu' _hψdec' ψ' _hψ' _hψrep' _hψlev' _hψty'
  have hNbot : N ≠ ⊥ := Ws48.WPW.ne_bot_of_forall_dvd_mem K SK N hN

  have hθ'aut : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (AutomorphicForm.pseudoEisenstein K ψ') :=
    AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β)
      hΦs hΦ ξK ψ' _hψ'
  obtain ⟨pψ', hpψ', hpψ'c, hpψ'o⟩ :=
    AutomorphicForm.exists_isAutomorphicFnAt_residualProjection_of_isAutomorphicFnAt_canonicalTruncationDomain
      K α β hα hαβ ξK hξc hξt hξu (AutomorphicForm.pseudoEisenstein K ψ') hθ'aut

  have hμQ : ∀ e : ιP ⊕ ιX, IsUnitaryChar (𝓞 K) K (Sum.elim μP μX e) := fun e => by cases e with | inl i => exact _hμ i | inr x => exact _hμX x
  have hνQ : ∀ e : ιP ⊕ ιX, IsUnitaryChar (𝓞 K) K (Sum.elim νP νX e) := fun e => by cases e with | inl i => exact _hν i | inr x => exact _hνX x
  have hμicQ : ∀ e : ιP ⊕ ιX, IsIdeleClassChar (𝓞 K) K (Sum.elim μP μX e) := fun e => by cases e with | inl i => exact _hμic i | inr x => exact _hμicX x
  have hνicQ : ∀ e : ιP ⊕ ιX, IsIdeleClassChar (𝓞 K) K (Sum.elim νP νX e) := fun e => by cases e with | inl i => exact _hνic i | inr x => exact _hνicX x
  have hμcQ : ∀ e : ιP ⊕ ιX, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((Sum.elim μP μX e x : ℂˣ) : ℂ) := fun e => by cases e with | inl i => exact _hμc i | inr x => exact _hμcX x
  have hνcQ : ∀ e : ιP ⊕ ιX, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((Sum.elim νP νX e x : ℂˣ) : ℂ) := fun e => by cases e with | inl i => exact _hνc i | inr x => exact _hνcX x
  have hμνQ : ∀ (e : ιP ⊕ ιX) (z : ↥((productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z)),
      Sum.elim μP μX e (z : (AdeleRing (𝓞 K) K)ˣ) * Sum.elim νP νX e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z := fun e z => by
    cases e with | inl i => exact _hμνP i z | inr x => exact _hμνX x z
  have hrQ : ∀ e : ιP ⊕ ιX, Sum.elim μP μX (Sum.map rP rX e) = Sum.elim νP νX e ∧ Sum.elim νP νX (Sum.map rP rX e) = Sum.elim μP μX e := fun e => by
    cases e with | inl i => exact _hr i | inr x => exact _hrX x
  have hdistQ : ∀ e e' : ιP ⊕ ιX, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
      Sum.elim μP μX e x ≠ Sum.elim μP μX e' x ∨ Sum.elim νP νX e x ≠ Sum.elim νP νX e' x := by
    intro e e' hne
    cases e with
    | inl i => cases e' with
      | inl i' => exact _hdist i i' (fun h => hne (congrArg Sum.inl h))
      | inr x => exact _hdistPX i x
    | inr x => cases e' with
      | inl i' =>
        obtain ⟨z, hz, h⟩ := _hdistPX i' x
        exact ⟨z, hz, h.imp Ne.symm Ne.symm⟩
      | inr x' => exact _hdistX x x' (fun h => hne (congrArg Sum.inr h))

  obtain ⟨ψfQ, hψfQ⟩ : ∃ ψfQ : ιP ⊕ ιX → ℂ → AdelicGL2 (𝓞 K) K → ℂ, ψfQ = fun e => Sum.elim ψf (fun _ _ _ => (0 : ℂ)) e := ⟨_, rfl⟩
  have hψfQ_inl : ∀ i, ψfQ (Sum.inl i) = ψf i := fun i => by rw [hψfQ]; rfl
  have hψfQ_inr : ∀ x, ψfQ (Sum.inr x) = fun _ _ => (0 : ℂ) := fun x => by rw [hψfQ]; rfl
  have hψfQ_ind : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (Sum.elim μP μX e) αm hαm s) (etaSnd (Sum.elim νP νX e) αm hαm s) (ψfQ e s) := by
    intro e s; cases e with
    | inl i => rw [hψfQ_inl]; exact _hψf i s
    | inr x => rw [hψfQ_inr]; exact isInducedSection_zero _ _
  have hψfQ_jc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψfQ e p.1 p.2) := by
    intro e; cases e with
    | inl i => rw [hψfQ_inl]; exact _hψjc i
    | inr x => rw [hψfQ_inr]; exact continuous_const
  have hψfQ_hol : ∀ e g, Differentiable ℂ (fun s => ψfQ e s g) := by
    intro e g; cases e with
    | inl i => rw [hψfQ_inl]; exact _hψhol i g
    | inr x => rw [hψfQ_inr]; exact differentiable_const _
  have hψfQ_dec : ∀ (e : ιP ⊕ ιX) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψfQ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t := by
    intro e n σ₀ C hC; cases e with
    | inl i => rw [hψfQ_inl]; exact _hψdec i n σ₀ C hC
    | inr x => rw [hψfQ_inr]; exact Ws48.WPW.decay_zero C n σ₀
  have hψQrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
      ψ g = ∑ e : ιP ⊕ ιX, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψfQ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g := by
    intro σ' g
    rw [Fintype.sum_sum_type, _hψrep σ' g]
    simp only [hψfQ_inl, hψfQ_inr, integral_zero, mul_zero, Finset.sum_const_zero, add_zero]

  obtain ⟨Mc', hMc'⟩ := Ws48.WPW.exists_meromorphicNF_weylIntertwining K hαm (Sum.elim μP μX) (Sum.elim νP νX)
    hμQ hνQ hμicQ hνicQ hμcQ hνcQ ψf' _hψf' _hψjc' _hψhol' _hψK' _hψsm' _hψKu'

  have h05 := AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
    K hαm α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦ c hc0 hcT hc D hDm hDF V hV0 hVT hV
    ξK (ιP ⊕ ιX) (Sum.elim μP μX) (Sum.elim νP νX) hμQ hνQ hμicQ hνicQ hμcQ hμνQ (Sum.map rP rX) hrQ hdistQ
    ψfQ ψf' hψfQ_ind _hψf' hψfQ_jc _hψjc' hψfQ_hol _hψhol' _hψK' _hψsm' _hψKu' hνcQ hψfQ_dec _hψdec'
    ψ ψ' _hψ _hψ' hψQrep _hψrep' Mc' hMc' pψ pψ' _hpψ hpψ' _hpψc hpψ'c _hpψo hpψ'o
  rw [Fintype.sum_sum_type] at h05
  simp only [hψfQ_inl, hψfQ_inr, Sum.map_inl, Sum.map_inr, zero_mul, integral_zero, mul_zero, add_zero,
    Finset.sum_const_zero, productionPinsOf_D, productionPinsOf_μ] at h05
  rw [← hC₀def] at h05

  have hψc : ∀ (i : ιP) (s : ℂ), Continuous (ψf i s) := fun i s => (_hψjc i).comp (Continuous.prodMk continuous_const continuous_id)
  have hbr : ∀ (i : ιP) (t : ℝ),
      (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (ψf' (Sum.inl i) ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I))) (fun s : ℂ => Mc' (Sum.inl (rP i)) s (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K) =
      ∑ j : Fin (nE (em i)),
        (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
        conj ((∫ k, ψf' (Sum.inl i) ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
              ∫ k, ψf' (Sum.inl (rP i)) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
                  conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
    intro i t
    exact Ws48.WPW.bracket_eq K N hNbot tysK hαm (μ (em i)) (ν (em i)) (_hμE _) (_hνE _) (_hμicE _) (_hνicE _) (_hμcE _) (_hνcE _)
      (nE (em i)) (φE (em i)) (_hφE (em i)) (_hφEK (em i)) (_hφEf (em i)) (_hφEjc (em i)) (_hφEhol (em i)) (_hφEKu (em i))
      (_hφEflat (em i)) (_hφElev (em i)) (_hφEty (em i)) (_hφEon (em i)) (_hφEspan (em i)) (OE (em i)) (EE (em i)) (NE (em i)) (_hEE (em i))
      (τ i) (μP i) (νP i) (_hem i) (_hμ i) (_hν i) (_hμic i) (_hνic i) (_hμc i) (_hνc i)
      (ψf' (Sum.inl i)) (_hψf' (Sum.inl i)) (_hψjc' _) (_hψhol' _) (_hψK' _) (_hψsm' _) (_hψKu' _) (_hψlev' _) (_hψty' _)
      (μP (rP i)) (νP (rP i)) (_hr i) (ψf' (Sum.inl (rP i))) (_hψf' (Sum.inl (rP i))) (_hψjc' _) (_hψhol' _) (_hψK' _) (_hψsm' _)
      (_hψKu' _) (_hψlev' _) (_hψty' _) (Mc' (Sum.inl (rP i))) (hMc' (Sum.inl (rP i))) (ψf i ((t : ℂ) * Complex.I)) (hψc i _) t
  simp only [hbr] at h05

  obtain ⟨cC, hcC⟩ : ∃ cC : (i : ιP) → ℝ → Fin (nE (em i)) → ℂ, cC = fun (i : ιP) (t : ℝ) (j : Fin (nE (em i))) =>
      ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := ⟨_, rfl⟩
  obtain ⟨aA, haA⟩ : ∃ aA : (i : ιP) → ℝ → Fin (nE (em i)) → ℂ, aA = fun (i : ιP) (t : ℝ) (j : Fin (nE (em i))) =>
      (∫ k, ψf' (Sum.inl i) ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        ∫ k, ψf' (Sum.inl (rP i)) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
          conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := ⟨_, rfl⟩
  have hcC' : ∀ (i : ιP) (t : ℝ) (j : Fin (nE (em i))), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = cC i t j := by
    intro i t j; rw [hcC]
  have haA' : ∀ (i : ιP) (t : ℝ) (j : Fin (nE (em i))), (∫ k, ψf' (Sum.inl i) ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        ∫ k, ψf' (Sum.inl (rP i)) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
          conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = aA i t j := by
    intro i t j; rw [haA]
  simp only [hcC', haA'] at h05

  have hmy : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (AutomorphicForm.pseudoEisenstein K ψ' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, pψ g * conj (pψ' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) +
        (C₀ : ℂ) * ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), cC i t j * conj (aA i t j) := h05
  clear h05
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), conj (cC i t j) * aA i t j := ⟨_, rfl⟩
  have hconjZ : conj (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), cC i t j * conj (aA i t j)) = Z := by
    rw [hZ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, Complex.conj_conj]

  have hL2 : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f → MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
    intro f hf
    exact ((AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK (AutomorphicForm.canonicalTruncationDomain K α β) f).1 hf).2
  have hθaut : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (AutomorphicForm.pseudoEisenstein K ψ) :=
    AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦ ξK ψ _hψ
  have mθ := hL2 _ hθaut
  have mθ' := hL2 _ hθ'aut
  have mp := hL2 _ _hpψ
  have mp' := hL2 _ hpψ'
  have hK4 : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (AutomorphicForm.pseudoEisenstein K ψ' g - pψ' g) * conj (pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0 := by
    refine Ws48.WPW.integral_mul_conj_eq_zero_of_forall_mem_of_closure _ _ _ (mθ'.sub mp') mp
      {h | IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h ∧ h ∈ AutomorphicForm.residualSpan (𝓞 K) K ((productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))).Z ξK} ?_ ?_
    · intro q hq
      exact ⟨hL2 q hq.1, hpψ'o q hq.1 hq.2⟩
    · intro ε hε
      obtain ⟨r, hr1, hr2, hr3⟩ := _hpψc ε hε
      exact ⟨r, ⟨hr2, hr1⟩, hr3⟩

  have hI_θθ : Integrable (fun g => AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    mθ'.integrable_mul mθ.star
  have hI_θp : Integrable (fun g => AutomorphicForm.pseudoEisenstein K ψ' g * conj (pψ g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    mθ'.integrable_mul mp.star
  have hI_pp : Integrable (fun g => pψ' g * conj (pψ g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := mp'.integrable_mul mp.star
  have hW : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (C₀ : ℂ) * Z := by

    have h1 := congrArg (starRingEnd ℂ) hmy
    rw [← integral_conj, map_add, ← integral_conj, map_mul, Complex.conj_ofReal, hconjZ] at h1
    simp only [map_mul, Complex.conj_conj] at h1

    have h2 : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, pψ' g * conj (pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
      have := hK4
      rw [← sub_eq_zero, ← integral_sub hI_θp hI_pp, ← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      beta_reduce; ring
    calc (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
        = (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          rw [← integral_sub hI_θθ hI_θp]
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          beta_reduce; rw [map_sub]; ring
      _ = (C₀ : ℂ) * Z := by
          rw [h2]
          have e1 : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
              ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, conj (AutomorphicForm.pseudoEisenstein K ψ g) * AutomorphicForm.pseudoEisenstein K ψ' g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
            integral_congr_ae (Filter.Eventually.of_forall fun g => by ring)
          have e2 : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, pψ' g * conj (pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, conj (pψ g) * pψ' g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
            integral_congr_ae (Filter.Eventually.of_forall fun g => by ring)
          rw [e1, e2, h1]; ring

  have hub := AutomorphicForm.exists_forall_mem_canonicalTruncationDomain_pseudoEisenstein_eq_zero_of_lt_adelicHeight K α β hα hαβ ξK ψ' _hψ'
  have hA2 := (AutomorphicForm.setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
    ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol
      _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP μP νP _hμ _hν _hμic _hνic _hμc _hμνP rP _hr _hdist ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνc _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty
    (AutomorphicForm.pseudoEisenstein K ψ') hθ'aut hub).2
  have hemQ : ∀ e : ιP ⊕ ιX, Sum.elim μP μX e = μ (Sum.elim em emX e) * NumberField.TateGlobal.normPowChar K (Sum.elim τ τX e) ∧
      Sum.elim νP νX e = ν (Sum.elim em emX e) * (NumberField.TateGlobal.normPowChar K (Sum.elim τ τX e))⁻¹ := fun e => by
    cases e with | inl i => exact _hem i | inr x => exact _hemX x
  have hCP := (hCPW ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol
      _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE (ιP ⊕ ιX) (Sum.elim μP μX) (Sum.elim νP νX) hμQ hνQ hμicQ hνicQ hμcQ hμνQ (Sum.map rP rX) hrQ hdistQ
    ψf' _hψf' _hψjc' _hψhol' hνcQ _hψdec' ψ' _hψ' _hψrep' (Sum.elim em emX) (Sum.elim τ τX) hemQ).2
  have hΘ' : ∀ (i : ιP) (t : ℝ) (j : Fin (nE (em i))),
      (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (κ'' : ℂ) * aA i t j := by
    intro i t j
    have h := hCP (Sum.inl i) j t
    simp only [Sum.elim_inl, Sum.map_inl] at h
    rw [← haA']
    exact h
  obtain ⟨Pk, hPkdef⟩ : ∃ Pk : AdelicGL2 (𝓞 K) K → ℂ, Pk = fun g => ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g := ⟨_, rfl⟩
  have hfold : ∀ g : AdelicGL2 (𝓞 K) K, (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) = Pk g := fun g => by rw [hPkdef]
  have hP : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (Pk g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (κ'' : ℂ) * Z := by
    have h1 : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (Pk g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
            (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
      rw [hPkdef]; exact hA2
    rw [h1, hZ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hcC', hΘ']; ring

  simp only [hfold]
  have hIW : Integrable (fun g => AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    mθ'.integrable_mul (mθ.sub mp).star
  have hκ0 : (((C₀ / κ'' : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hC₀pos hκ'').ne'
  by_cases hint : Integrable (fun g => AutomorphicForm.pseudoEisenstein K ψ' g * conj (Pk g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))
  · have hsplit : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g *
          conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g - (((C₀ / κ'' : ℝ)) : ℂ) * Pk g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
          (((C₀ / κ'' : ℝ)) : ℂ) * ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ' g * conj (Pk g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
      rw [← integral_const_mul, ← integral_sub hIW (hint.const_mul _)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      beta_reduce
      rw [map_sub, map_mul, Complex.conj_ofReal]
      ring
    rw [hsplit, hW, hP]
    have hκ'' : (κ'' : ℂ) ≠ 0 := by exact_mod_cast hκ''.ne'
    push_cast
    field_simp
    ring
  · have hnot : ¬ Integrable (fun g => AutomorphicForm.pseudoEisenstein K ψ' g *
        conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g - (((C₀ / κ'' : ℝ)) : ℂ) * Pk g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
      intro hI
      apply hint
      have heq : (fun g => AutomorphicForm.pseudoEisenstein K ψ' g * conj (Pk g)) = fun g =>
          ((((C₀ / κ'' : ℝ)) : ℂ))⁻¹ * (AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) -
            AutomorphicForm.pseudoEisenstein K ψ' g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g - (((C₀ / κ'' : ℝ)) : ℂ) * Pk g)) := by
        funext g
        simp only [map_sub, map_mul, Complex.conj_ofReal]
        field_simp
        ring
      rw [heq]
      exact (hIW.sub hI).const_mul _
    exact integral_undef hnot

end S_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_sub_residualProj_sub_mul_sum_integral_sum_inner_mul_axis_continuation_eq_zero_of_matched_paleyWiener_of_cuspBasis
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_sub_residualProj_sub_mul_sum_integral_sum_inner_mul_axis_continuation_eq_zero_of_matched_paleyWiener_of_cuspBasis (solution)
