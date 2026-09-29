-- Prove2me | solution 1 for AutomorphicForm.setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c74ae627-5db2-5033-b845-d8d972d94f8d

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

import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain_of_flat
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm
open scoped Topology

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

noncomputable section

namespace PacketCuspOrthProof

theorem packet_orth {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SFinite μ]
    {ι : Type*} [Fintype ι] {J : ι → Type*} [∀ i, Fintype (J i)]
    (b : X → ℂ) (c : ∀ i, J i → ℝ → ℂ) (E : ∀ i, J i → ℝ → X → ℂ)
    (hF : ∀ i j, MeasureTheory.Integrable (fun p : X × ℝ => c i j p.2 * E i j p.2 p.1 * conj (b p.1))
      (μ.prod MeasureTheory.volume))
    (horth : ∀ i j (t : ℝ), ∫ x, E i j t x * conj (b x) ∂μ = 0) :
    ∫ x, (∑ i, ∫ t : ℝ, ∑ j, c i j t * E i j t x) * conj (b x) ∂μ = 0 := by
  classical
  have hae : ∀ i j, ∀ᵐ x ∂μ, MeasureTheory.Integrable (fun t : ℝ => c i j t * E i j t x * conj (b x)) :=
    fun i j => (hF i j).prod_right_ae
  have hae' : ∀ᵐ x ∂μ, ∀ i j, MeasureTheory.Integrable (fun t : ℝ => c i j t * E i j t x * conj (b x)) := by
    rw [MeasureTheory.ae_all_iff]; intro i; rw [MeasureTheory.ae_all_iff]; exact hae i
  have hpt : ∀ᵐ x ∂μ, (∑ i, ∫ t : ℝ, ∑ j, c i j t * E i j t x) * conj (b x) =
      ∑ i, ∑ j, ∫ t : ℝ, c i j t * E i j t x * conj (b x) := by
    filter_upwards [hae'] with x hx
    by_cases hb : b x = 0
    · simp [hb]
    · have hbc : conj (b x) ≠ 0 := by simpa using hb
      have hint : ∀ i j, MeasureTheory.Integrable (fun t : ℝ => c i j t * E i j t x) := by
        intro i j
        have h := (hx i j).mul_const ((conj (b x))⁻¹)
        refine h.congr (MeasureTheory.ae_of_all _ fun t => ?_)
        simp only []
        rw [mul_assoc (c i j t * E i j t x), mul_inv_cancel₀ hbc, mul_one]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint i j), Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (MeasureTheory.integral_mul_const _ _).symm
  rw [MeasureTheory.integral_congr_ae hpt,
    MeasureTheory.integral_finsetSum _ (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun j _ => (hF i j).integral_prod_left))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => (hF i j).integral_prod_left)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [MeasureTheory.integral_integral_swap (hF i j)]
  have h0 : ∀ t : ℝ, ∫ x, c i j t * E i j t x * conj (b x) ∂μ = 0 := fun t => by
    simp_rw [mul_assoc]
    rw [MeasureTheory.integral_const_mul, horth, mul_zero]
  simp [h0]

theorem integral_norm_le_one_of_sq {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {φ : X → ℂ}
    (hint : MeasureTheory.Integrable (fun x => ‖φ x‖) μ) (hint2 : MeasureTheory.Integrable (fun x => ‖φ x‖ ^ 2) μ)
    (h2 : ∫ x, ‖φ x‖ ^ 2 ∂μ = 1) : ∫ x, ‖φ x‖ ∂μ ≤ 1 := by
  have hpt : ∀ x, ‖φ x‖ ≤ (1 + ‖φ x‖ ^ 2) / 2 := fun x => by nlinarith [sq_nonneg (‖φ x‖ - 1), norm_nonneg (φ x)]
  calc ∫ x, ‖φ x‖ ∂μ ≤ ∫ x, (1 + ‖φ x‖ ^ 2) / 2 ∂μ :=
        MeasureTheory.integral_mono hint (((MeasureTheory.integrable_const 1).add hint2).div_const 2) hpt
    _ = 1 := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_add (MeasureTheory.integrable_const 1) hint2,
          MeasureTheory.integral_const, h2]
        simp

theorem one_add_sum_le {V : Type*} [Fintype V] (t s : ℝ) (a b p q : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 ≤ q v) :
    1 + ∑ v, (|t + s + a v| + |t + s - b v| + p v + q v) ≤
      (1 + |t|) * (1 + ∑ v, (2 + |s + a v| + |s - b v| + p v + q v)) := by
  have h1 : ∀ v, |t + s + a v| + |t + s - b v| + p v + q v ≤ 2 * |t| + (|s + a v| + |s - b v| + p v + q v) := by
    intro v
    have e1 : |t + s + a v| ≤ |t| + |s + a v| := by
      rw [show t + s + a v = t + (s + a v) by ring]; exact abs_add_le _ _
    have e2 : |t + s - b v| ≤ |t| + |s - b v| := by
      rw [show t + s - b v = t + (s - b v) by ring]; exact abs_add_le _ _
    linarith
  have h2 : ∑ v, (|t + s + a v| + |t + s - b v| + p v + q v) ≤ ∑ v, (2 * |t| + (|s + a v| + |s - b v| + p v + q v)) :=
    Finset.sum_le_sum fun v _ => h1 v
  set R : V → ℝ := fun v => |s + a v| + |s - b v| + p v + q v with hRdef
  have h3 : ∑ v, (2 * |t| + (|s + a v| + |s - b v| + p v + q v)) = 2 * |t| * (Fintype.card V : ℝ) + ∑ v, R v := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp only [hRdef]; ring
  have h4 : ∑ v, (2 + |s + a v| + |s - b v| + p v + q v) = 2 * (Fintype.card V : ℝ) + ∑ v, R v := by
    have : (fun v => 2 + |s + a v| + |s - b v| + p v + q v) = fun v => 2 + R v := funext fun v => by simp only [hRdef]; ring
    rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [h3] at h2
  rw [h4]
  have hR : 0 ≤ ∑ v, R v := Finset.sum_nonneg fun v _ => by have := hp v; have := hq v; simp only [hRdef]; positivity
  have ht : 0 ≤ |t| := abs_nonneg t
  have hc : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  nlinarith [hR, ht, mul_nonneg ht hR, hc, mul_nonneg ht hc]

end PacketCuspOrthProof

open PacketCuspOrthProof MeasureTheory in
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
      (i₀ : ι),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) * conj (b i₀ g)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc
    hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP _ μP νP hμP hνP hμPic hνPic hμPc hμνP
    rP hr hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνPc hψdec ψ hψ hψrep em τ hem hψlev hψty i₀
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  obtain ⟨-, -, -, hΦS, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hnull : NullMeasurableSet (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (nullMeasurableSet_restrict_of_subset hΦS).mp hFD.nullMeasurableSet
  have hμΦ : (adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hFD
    rwa [Set.inter_eq_left.mpr hΦS] at h
  haveI hfin : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := isFiniteMeasure_restrict.mpr hμΦ.ne
  have haeΦ : ∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), x ∈ AutomorphicForm.canonicalTruncationDomain K α β := ae_restrict_mem₀ hnull

  obtain ⟨h₀, hh₀, hfloor, -⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain K α β hα hαβ

  have hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) :=
    fun z => by rw [Real.rpow_zero]; exact hξu z
  obtain ⟨CE, A, B, hCE, hbound⟩ :=
    AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain_of_flat
      K SK ξK hξc hξt N hN tysK 0 hξw α β hα hαβ

  obtain ⟨kB, hkB⟩ := exists_nat_ge B
  obtain ⟨Cb, hCb0, hCb⟩ :=
    AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
      K α β hα hαβ ξK hξc hξt SK N hN tysK (cls i₀) (b i₀) (hb i₀).2 kB
  have hbcont : Continuous (b i₀) := AutomorphicForm.continuous_of_mem_isotypicCuspSubmodule (hb i₀).2.1

  set Lb : ℝ := Cb * h₀ ^ (B - (kB : ℝ)) with hLb
  have hLb0 : 0 ≤ Lb := mul_nonneg hCb0 (Real.rpow_nonneg hh₀.le _)
  have hbH : ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
      NumberField.AdelicHeight.adelicHeight K g ^ B * ‖b i₀ g‖ ≤ Lb := by
    intro g hg
    have hHpos : 0 < NumberField.AdelicHeight.adelicHeight K g := lt_of_lt_of_le hh₀ (hfloor g hg)
    have h1 := hCb g (hΦS hg)
    have h2 : NumberField.AdelicHeight.adelicHeight K g ^ B * (Cb * (NumberField.AdelicHeight.adelicHeight K g)⁻¹ ^ kB) =
        Cb * NumberField.AdelicHeight.adelicHeight K g ^ (B - (kB : ℝ)) := by
      rw [Real.rpow_sub hHpos, Real.rpow_natCast, inv_pow, div_eq_mul_inv]; ring
    calc NumberField.AdelicHeight.adelicHeight K g ^ B * ‖b i₀ g‖
        ≤ NumberField.AdelicHeight.adelicHeight K g ^ B * (Cb * (NumberField.AdelicHeight.adelicHeight K g)⁻¹ ^ kB) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hHpos.le _)
      _ = Cb * NumberField.AdelicHeight.adelicHeight K g ^ (B - (kB : ℝ)) := h2
      _ ≤ Cb * h₀ ^ (B - (kB : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCb0
          exact Real.rpow_le_rpow_of_nonpos hh₀ (hfloor g hg) (by linarith)

  have hdec : ∀ i : ιP, ∃ m : ℝ → ℝ, Integrable m ∧ ∀ (t : ℝ), ∀ g ∈ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)),
      (1 + |t|) ^ A * ‖ψf i ((t : ℂ) * Complex.I) g‖ ≤ m t := by
    intro i
    obtain ⟨m, hm, -, h⟩ := hψdec i A 0 _ (isCompact_adelicMaximalCompact K)
    refine ⟨m, hm, fun t g hg => ?_⟩
    have := h 0 (by simp) t g hg
    simpa using this
  choose m hm_int hm using hdec

  have hterm : ∀ (i : ιP) (j : Fin (nE (em i))),
      Integrable (fun p : AdelicGL2 (𝓞 K) K × ℝ =>
        (∫ k, ψf i ((p.2 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((p.2 + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          EE (em i) j ((((p.2 + τ i : ℝ) : ℂ)) * Complex.I) p.1 * conj (b i₀ p.1))
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod volume) := by
    intro i j
    obtain ⟨hOo, -, haxis, -, -, -, hcontE, -, -, -⟩ := hEE (em i) j

    obtain ⟨τμ, mμ, hτμ, hmμ, -⟩ :=
      NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (μ (em i)) (hμ (em i)) (hμc (em i))
    obtain ⟨τν, mν, hτν, hmν, -⟩ :=
      NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (ν (em i)) (hν (em i)) (hνc (em i))
    have hμν' : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      intro z
      rw [Real.rpow_zero, Complex.ofReal_one, mul_one, ← Units.val_mul, hμν (em i) z]

    have hsq : ∫ k, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by
      have h := hφEon (em i) j j
      simp only [if_true] at h
      have hfun : (fun k : adelicMaximalCompact K => φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))) =
          fun k : adelicMaximalCompact K => ((‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 : ℝ) : ℂ) := by
        funext k; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hfun] at h
      have h2 : ((∫ k, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) : ℝ) : ℂ) = 1 := by
        rw [← h]; exact integral_ofReal.symm
      exact_mod_cast h2
    have hE := hbound hαm (μ (em i)) (ν (em i)) (hμ (em i)) (hν (em i)) (hμic (em i)) (hνic (em i)) (hμc (em i)) (hνc (em i)) hμν' τμ τν hτμ hτν mμ mν hmμ hmν
      (φE (em i) j) (hφE (em i) j) (hφEK (em i) j) (hφEf (em i) j) (hφEjc (em i) j) (hφEhol (em i) j) (hφEKu (em i) j) (hφEflat (em i) j) (hφElev (em i) j)
      (hφEty (em i) j) hsq.le (OE (em i) j) (EE (em i) j) (NE (em i) j) (hEE (em i) j)

    set D₀ : ℝ := 1 + ∑ v : InfinitePlace K, (2 + |τ i + τμ v| + |τ i - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) with hD₀
    have hD₀pos : 0 ≤ D₀ := by
      simp only [hD₀]
      exact add_nonneg zero_le_one (Finset.sum_nonneg fun v _ => by positivity)
    have hEbd : ∀ (t : ℝ), ∀ y ∈ AutomorphicForm.canonicalTruncationDomain K α β, ‖EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) y‖ ≤
        CE * D₀ ^ A * (1 + |t|) ^ A * NumberField.AdelicHeight.adelicHeight K y ^ B := by
      intro t y hy
      have h1 := hE (t + τ i) y hy
      have hbase := one_add_sum_le t (τ i) τμ τν (fun v => (|mμ v| : ℝ)) (fun v => (|mν v| : ℝ))
        (fun v => by positivity) (fun v => by positivity)
      have hb0 : 0 ≤ 1 + ∑ v : InfinitePlace K, (|t + τ i + τμ v| + |t + τ i - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) :=
        add_nonneg zero_le_one (Finset.sum_nonneg fun v _ => by positivity)
      have hH0 : 0 ≤ NumberField.AdelicHeight.adelicHeight K y ^ B :=
        Real.rpow_nonneg (le_trans hh₀.le (hfloor y hy)) _
      calc ‖EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) y‖
          ≤ CE * (1 + ∑ v : InfinitePlace K, (|t + τ i + τμ v| + |t + τ i - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
              NumberField.AdelicHeight.adelicHeight K y ^ B := by
            exact_mod_cast h1
        _ ≤ CE * ((1 + |t|) * D₀) ^ A * NumberField.AdelicHeight.adelicHeight K y ^ B := by
            gcongr
        _ = CE * D₀ ^ A * (1 + |t|) ^ A * NumberField.AdelicHeight.adelicHeight K y ^ B := by rw [mul_pow]; ring

    have hck : Continuous fun p : ℝ × adelicMaximalCompact K =>
        ψf i ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K) *
          conj (φE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K)) := by
      refine Continuous.mul ?_ (Complex.continuous_conj.comp ?_)
      · exact (hψjc i).comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const |>.prodMk
          (continuous_subtype_val.comp continuous_snd))
      · exact (hφEjc (em i) j).comp (((Complex.continuous_ofReal.comp ((continuous_fst).add continuous_const)).mul
          continuous_const).prodMk (continuous_subtype_val.comp continuous_snd))
    have hc_cont : Continuous fun t : ℝ => ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
      have h := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K)
        (f := fun (t : ℝ) (k : adelicMaximalCompact K) => ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) hck isCompact_univ
      simpa only [Measure.restrict_univ] using h

    have hE_cont : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => EE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) p.2 := by
      have hg : Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => (((((p.1 + τ i : ℝ) : ℂ)) * Complex.I), p.2) :=
        ((Complex.continuous_ofReal.comp (continuous_fst.add continuous_const)).mul continuous_const).prodMk continuous_snd
      refine hcontE.comp_continuous hg fun p => ⟨haxis ?_, Set.mem_univ _⟩
      simp

    have intKR : ∀ f : adelicMaximalCompact K → ℝ, Continuous f → Integrable f (maximalCompactHaar K) :=
      fun f hf => hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    have hmnn : ∀ t : ℝ, 0 ≤ m i t := fun t =>
      le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (hm i t 1 (adelicMaximalCompact K).one_mem)

    have hc_bd : ∀ t : ℝ, ‖∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤
        m i t * ((1 + |t|) ^ A)⁻¹ := by
      intro t
      have hpow : 0 < (1 + |t|) ^ A := by positivity
      set M : ℝ := m i t * ((1 + |t|) ^ A)⁻¹ with hM
      have hM0 : 0 ≤ M := mul_nonneg (hmnn t) (inv_nonneg.mpr hpow.le)
      have hψ_bd : ∀ k : adelicMaximalCompact K, ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ M := by
        intro k
        have h := hm i t k k.2
        rw [hM, ← div_eq_mul_inv, le_div_iff₀ hpow, mul_comm]
        exact h
      have hφc : Continuous fun k : adelicMaximalCompact K =>
          ‖φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ :=
        continuous_norm.comp ((hφEjc (em i) j).comp (continuous_const.prodMk continuous_subtype_val))
      have hψc : Continuous fun k : adelicMaximalCompact K => ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ :=
        continuous_norm.comp ((hψjc i).comp (continuous_const.prodMk continuous_subtype_val))
      have hsq' : ∫ k, ‖φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = 1 := by
        rw [← hsq]; congr 1; funext k; rw [hφEflat (em i) j _ k]
      have hone := integral_norm_le_one_of_sq (maximalCompactHaar K) (intKR _ hφc) (intKR _ (hφc.pow 2)) hsq'
      calc ‖∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
              conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖
          ≤ ∫ k, ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
              conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ k, M * ‖φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) := by
            refine integral_mono (intKR _ ((hψc.mul hφc).congr fun k => ?_)) (intKR _ (continuous_const.mul hφc)) fun k => ?_
            · simp only [Pi.mul_apply, norm_mul, Complex.norm_conj]
            · rw [norm_mul, Complex.norm_conj]
              exact mul_le_mul_of_nonneg_right (hψ_bd k) (norm_nonneg _)
        _ = M * ∫ k, ‖φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) :=
            integral_const_mul _ _
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left hone hM0
        _ = M := mul_one M

    have hbd : ∀ (t : ℝ), ∀ y ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        ‖(∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) y * conj (b i₀ y)‖ ≤ CE * D₀ ^ A * Lb * m i t := by
      intro t y hy
      have hpow : 0 < (1 + |t|) ^ A := by positivity
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hH0 : 0 ≤ NumberField.AdelicHeight.adelicHeight K y ^ B :=
        Real.rpow_nonneg (le_trans hh₀.le (hfloor y hy)) _
      calc _ ≤ (m i t * ((1 + |t|) ^ A)⁻¹) * (CE * D₀ ^ A * (1 + |t|) ^ A * NumberField.AdelicHeight.adelicHeight K y ^ B) * ‖b i₀ y‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (hc_bd t) (hEbd t y hy) (norm_nonneg _) (mul_nonneg (hmnn t) (inv_nonneg.mpr hpow.le)))
              (norm_nonneg _)
        _ = CE * D₀ ^ A * m i t * (NumberField.AdelicHeight.adelicHeight K y ^ B * ‖b i₀ y‖) := by field_simp
        _ ≤ CE * D₀ ^ A * m i t * Lb :=
            mul_le_mul_of_nonneg_left (hbH y hy) (by have := hmnn t; positivity)
        _ = CE * D₀ ^ A * Lb * m i t := by ring

    have hFcont : Continuous fun p : AdelicGL2 (𝓞 K) K × ℝ =>
        (∫ k, ψf i ((p.2 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((p.2 + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          EE (em i) j ((((p.2 + τ i : ℝ) : ℂ)) * Complex.I) p.1 * conj (b i₀ p.1) :=
      ((hc_cont.comp continuous_snd).mul (hE_cont.comp (continuous_snd.prodMk continuous_fst))).mul
        (Complex.continuous_conj.comp (hbcont.comp continuous_fst))
    have hG : Integrable (fun p : AdelicGL2 (𝓞 K) K × ℝ => (1 : ℝ) * ((CE * D₀ ^ A * Lb) * m i p.2))
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod volume) :=
      MeasureTheory.Integrable.mul_prod (f := fun _ : AdelicGL2 (𝓞 K) K => (1 : ℝ)) (integrable_const 1) ((hm_int i).const_mul _)
    refine hG.mono' hFcont.aestronglyMeasurable ?_
    have hae : ∀ᵐ p : AdelicGL2 (𝓞 K) K × ℝ ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod volume), p.1 ∈ AutomorphicForm.canonicalTruncationDomain K α β :=
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) (ν := volume)).ae haeΦ
    filter_upwards [hae] with p hp
    rw [one_mul]
    have := hbd p.2 p.1 hp
    linarith

  have horth : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g * conj (b i₀ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
    intro i j t
    obtain ⟨-, -, haxis, -⟩ := hEE (em i) j
    exact AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem K α β hα hαβ ΦK cK uK d₁K d₂K TK
      hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν hμ hν hμic hνic
      hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE
      (em i) j _ (haxis (by simp)) i₀

  have hP := packet_orth ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) (b i₀)
    (fun (i : ιP) (j : Fin (nE (em i))) (t : ℝ) => (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)))
    (fun (i : ιP) (j : Fin (nE (em i))) (t : ℝ) (g : AdelicGL2 (𝓞 K) K) => EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g)
    (fun i j => by simpa only using hterm i j)
    (fun i j t => by simpa only using horth i j t)
  simpa only using hP

end
end S_AutomorphicForm_setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener (solution)
