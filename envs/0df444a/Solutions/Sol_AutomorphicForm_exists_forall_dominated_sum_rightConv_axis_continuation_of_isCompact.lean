-- Prove2me | solution 1 for AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/45c356b4-e158-58da-9c01-6f6a6bc1f66d

import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_dominated_sum_rightConv_axis_continuation_of_isCompact
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem L1A.dsum_bound {n : ℕ} (a : Fin n → Fin n → ℂ) (u v : Fin n → ℂ) (Ba Bu Bv : ℝ)
    (ha : ∀ i j, ‖a i j‖ ≤ Ba) (hu : ∀ i, ‖u i‖ ≤ Bu) (hv : ∀ j, ‖v j‖ ≤ Bv)
    (hBa : 0 ≤ Ba) (hBu : 0 ≤ Bu) :
    ‖∑ i, ∑ j, a i j * (u i * conj (v j))‖ ≤ ((n : ℕ) : ℝ) ^ 2 * (Ba * (Bu * Bv)) := by
  calc ‖∑ i, ∑ j, a i j * (u i * conj (v j))‖
      ≤ ∑ i, ‖∑ j, a i j * (u i * conj (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖a i j * (u i * conj (v j))‖ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, Ba * (Bu * Bv) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        have h1 := ha i j; have h2 := hu i; have h3 := hv j
        have : 0 ≤ ‖u i‖ * ‖v j‖ := by positivity
        gcongr
    _ = ((n : ℕ) : ℝ) ^ 2 * (Ba * (Bu * Bv)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring

theorem L1A.final_bound (n AE B₀ : ℕ) (Ca CE P W S : ℝ) (hCa : 0 ≤ Ca) (hCE : 0 ≤ CE)
    (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hS : S ≤ ((n : ℕ) : ℝ) ^ 2 * (Ca * (1 + P) ^ (-((2 * AE + B₀ : ℕ) : ℝ)) *
      (CE * (1 + (P + W)) ^ AE * (CE * (1 + (P + W)) ^ AE)))) :
    S ≤ ((n : ℕ) : ℝ) ^ 2 * (Ca * (CE * CE)) * (1 + W) ^ (2 * AE) * (1 + P) ^ (-(B₀ : ℝ)) := by
  refine hS.trans ?_
  have h1P : 0 < 1 + P := by positivity
  have hPW : (1 + (P + W)) ^ AE ≤ ((1 + W) * (1 + P)) ^ AE :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hW hP]) _
  have hkey : (1 + P) ^ (-((2 * AE + B₀ : ℕ) : ℝ)) * ((1 + P) ^ AE * (1 + P) ^ AE) =
      (1 + P) ^ (-(B₀ : ℝ)) := by
    rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_add h1P]
    congr 1; push_cast; ring
  have hr : 0 ≤ (1 + P) ^ (-((2 * AE + B₀ : ℕ) : ℝ)) := Real.rpow_nonneg h1P.le _
  calc ((n : ℕ) : ℝ) ^ 2 * (Ca * (1 + P) ^ (-((2 * AE + B₀ : ℕ) : ℝ)) *
          (CE * (1 + (P + W)) ^ AE * (CE * (1 + (P + W)) ^ AE)))
      ≤ ((n : ℕ) : ℝ) ^ 2 * (Ca * (1 + P) ^ (-((2 * AE + B₀ : ℕ) : ℝ)) *
          (CE * ((1 + W) * (1 + P)) ^ AE * (CE * ((1 + W) * (1 + P)) ^ AE))) := by gcongr
    _ = ((n : ℕ) : ℝ) ^ 2 * (Ca * (CE * CE)) * (1 + W) ^ (2 * AE) *
          ((1 + P) ^ (-((2 * AE + B₀ : ℕ) : ℝ)) * ((1 + P) ^ AE * (1 + P) ^ AE)) := by
        rw [mul_pow]; ring
    _ = _ := by rw [hkey]

theorem L1A.summable_dom {ιE : Type*} (nE : ιE → ℕ) (D₀ : ℕ) (hcard : ∀ e, nE e ≤ D₀) (c : ℝ) (hc : 0 ≤ c)
    (A : ℕ) (W : ιE → ℝ) (W₀ : ℝ) (hW0 : ∀ e, 0 ≤ W e) (hW : ∀ e, 0 < nE e → W e ≤ W₀)
    (I : ιE → ℝ) (hI : ∀ e, 0 ≤ I e) (hs : Summable fun e => if 0 < nE e then I e else 0) :
    Summable fun e => ((nE e : ℕ) : ℝ) ^ 2 * c * (1 + W e) ^ A * I e := by
  refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_)
    (hs.mul_left (((D₀ : ℕ) : ℝ) ^ 2 * c * (1 + W₀) ^ A))
  · have := hI e; have := hW0 e; positivity
  · by_cases hpos : 0 < nE e
    · rw [if_pos hpos]
      have h1 := hI e; have h2 := hW e hpos; have h3 := hW0 e
      have h4 : ((nE e : ℕ) : ℝ) ≤ ((D₀ : ℕ) : ℝ) := by exact_mod_cast hcard e
      gcongr
    · have h0 : nE e = 0 := Nat.eq_zero_of_not_pos hpos
      rw [if_neg hpos, h0]
      simp

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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    (∀ (x : AdelicGL2 (𝓞 K) K) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ D : ιE → ℝ → ℝ, (∀ e, Integrable (D e)) ∧ (Summable fun e : ιE => ∫ t : ℝ, D e t) ∧
        ∀ (e : ιE) (t : ℝ), ∀ y ∈ C,
          ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
              (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
              (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y))‖ ≤ D e t) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _iC μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf
    hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE f hf hfc hfact hbi harch x C hC

  have hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) := by
    intro z; rw [Real.rpow_zero]; exact hξu z
  have hμν' : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
      ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) : ℂ) =
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    intro e z
    rw [Real.rpow_zero, Complex.ofReal_one, mul_one, ← Units.val_mul, hμν e z]
  have hpairs' : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
      IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
      IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
      ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
      IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
      Continuous φ₀ → IsArchKFinite K φ₀ →
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
      φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
      ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z := by
    intro μ' ν' h1 h2 h3 h4 h5 h6 h7
    refine hpairs μ' ν' h1 h2 h3 h4 h5 h6 (fun z => Units.ext ?_)
    have h := h7 z
    rw [Real.rpow_zero, Complex.ofReal_one, mul_one] at h
    rw [Units.val_mul]; exact h

  obtain ⟨D₀, τμ, τν, mμ, mν, M₀, nρ, ρs, B₀, hcard, hτ, hm, hM₀, -, hsum⟩ :=
    AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2 K α β hα hαβ ΦK
      cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK (fun _ => 0) (fun _ _ => 0) 0 hξw hαm ιE μ ν
      hμ hν hμic hνic hμc hνc hμν' hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan
      hpairs' OE EE NE hEE
  obtain ⟨hint, hsumm, -⟩ := hsum B₀ le_rfl

  obtain ⟨CE, AE, hCE, hE⟩ :=
    AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat K SK ξK hξc hξt N hN tysK 0 hξw
      (insert x C) (hC.insert x)

  have hnorm : ∀ (e : ιE) (j : Fin (nE e)),
      ∫ k, ‖φE e j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1 := by
    intro e j
    have h := hφEon e j j
    rw [if_pos rfl] at h
    have hk : ∀ g : AdelicGL2 (𝓞 K) K, φE e j 0 g * conj (φE e j 0 g) = ((‖φE e j 0 g‖ ^ 2 : ℝ) : ℂ) := fun g => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    simp_rw [hk] at h
    rw [integral_complex_ofReal] at h
    exact (Complex.ofReal_eq_one.mp h).le
  have hEb : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ), ∀ y ∈ insert x C,
      ‖EE e j ((t : ℂ) * Complex.I) y‖ ≤
        CE * (1 + ∑ v : InfinitePlace K,
          (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ))) ^ AE :=
    fun e j t y hy => hE hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν' e)
      (τμ e) (τν e) (fun v z h1 h2 => (hτ e v z h1 h2).1) (fun v z h1 h2 => (hτ e v z h1 h2).2)
      (mμ e) (mν e) (fun v z h1 => (hm e v z h1).1) (fun v z h1 => (hm e v z h1).2)
      (φE e j) (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j) (hφEflat e j) (hφElev e j)
      (hφEty e j) (hnorm e j) (OE e j) (EE e j) (NE e j) (hEE e j) t y hy

  obtain ⟨Ca, hCa, ha⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn K SK ξK hξc hξt N hN tysK 0 hξw
      f hf hfc hfact (2 * AE + B₀)
  have hab : ∀ (e : ιE) (i j : Fin (nE e)) (t : ℝ),
      ‖∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
          conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤
        Ca * (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-((2 * AE + B₀ : ℕ) : ℝ)) := by
    intro e i j t
    obtain ⟨a', -, -, hb⟩ := ha hαm (μ e) (ν e) (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (hμν' e)
      (τμ e) (τν e) (fun v z h1 h2 => (hτ e v z h1 h2).1) (fun v z h1 h2 => (hτ e v z h1 h2).2)
      (φE e i) (φE e j) (hφE e i) (hφE e j) (hφEK e i) (hφEK e j) (hφEf e i) (hφEf e j)
      (hφEjc e i) (hφEjc e j) (hφEhol e i) (hφEhol e j) (hφEKu e i) (hφEKu e j)
      (hφEflat e i) (hφEflat e j) (hφElev e i) (hφElev e j) (hφEty e i) (hφEty e j) (hnorm e i) (hnorm e j)
    have hbt := hb t
    simp only [zero_div, Real.rpow_zero, Complex.ofReal_one, mul_one] at hbt
    exact le_trans (le_add_of_nonneg_right (norm_nonneg _)) hbt

  refine ⟨fun e t => ((nE e : ℕ) : ℝ) ^ 2 * (Ca * (CE * CE)) *
      (1 + ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ))) ^ (2 * AE) *
      (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B₀ : ℝ)), ?_, ?_, ?_⟩
  ·
    intro e
    exact (hint e).const_mul _
  ·
    have hW0 : ∀ e : ιE, 0 ≤ ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)) := fun e => by positivity
    have hWle : ∀ e : ιE, 0 < nE e → ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)) ≤
        ∑ _v : InfinitePlace K, ((M₀ : ℝ) + (M₀ : ℝ)) := fun e he =>
      Finset.sum_le_sum fun v _ => by
        have h1 : (|mμ e v| : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast (hM₀ e he v).1
        have h2 : (|mν e v| : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast (hM₀ e he v).2
        exact add_le_add h1 h2
    have hIe : ∀ e : ιE, 0 ≤ ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B₀ : ℝ)) := fun e =>
      integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
    have key := L1A.summable_dom nE D₀ hcard (Ca * (CE * CE)) (by positivity) (2 * AE)
      (fun e => ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ))) _ hW0 hWle
      (fun e => ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B₀ : ℝ))) hIe hsumm
    refine key.congr fun e => ?_
    dsimp only
    exact (integral_const_mul _ _).symm
  ·
    intro e t y hy
    dsimp only
    have hx : x ∈ insert x C := Set.mem_insert x C
    have hy' : y ∈ insert x C := Set.mem_insert_of_mem x hy
    have hsplit : ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v| + (|mμ e v| : ℝ) + (|mν e v| : ℝ)) =
        ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|) +
          ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    have hEi : ∀ i : Fin (nE e), ‖EE e i ((t : ℂ) * Complex.I) x‖ ≤
        CE * (1 + (∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|) +
          ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)))) ^ AE := fun i => by
      have := hEb e i t x hx; rwa [hsplit] at this
    have hEj : ∀ j : Fin (nE e), ‖EE e j ((t : ℂ) * Complex.I) y‖ ≤
        CE * (1 + (∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|) +
          ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ)))) ^ AE := fun j => by
      have := hEb e j t y hy'; rwa [hsplit] at this
    have hds := L1A.dsum_bound _ _ _ _ _ _ (fun i j => hab e i j t) hEi hEj
      (mul_nonneg hCa.le (Real.rpow_nonneg (by positivity) _)) (by positivity)
    exact L1A.final_bound (nE e) AE B₀ Ca CE _ _ _ hCa.le hCE.le (by positivity) (by positivity) hds

end S_AutomorphicForm_exists_forall_dominated_sum_rightConv_axis_continuation_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_dominated_sum_rightConv_axis_continuation_of_isCompact (solution)
