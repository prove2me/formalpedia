-- Prove2me | solution 1 for AutomorphicForm.setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation_mul_conj_eq_tsum_integral_sum_mul_setIntegral_indicator_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cf2641a4-729c-574b-814d-203e854addea

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
import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
import Theorems.Thm_AutomorphicForm_continuous_integral_rightConv_axis_mul_conj_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation_mul_conj_eq_tsum_integral_sum_mul_setIntegral_indicator_mul_conj
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

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

theorem FEIS.measure_canonicalTruncationDomain_lt_top (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    adelicGLHaar (Fin 2) (𝓞 K) K (canonicalTruncationDomain K α β) < ⊤ := by
  by_cases h : ∃ d, IsTruncationDatum K α β d
  · have hspec := canonicalTruncationData_spec K h
    obtain ⟨-, -, -, hsub, hFD⟩ := hspec
    have := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K α β hα hαβ (canonicalTruncationDomain K α β) hFD
    exact lt_of_le_of_lt (measure_mono (Set.subset_inter Set.Subset.rfl hsub)) this
  · have : canonicalTruncationDomain K α β = ∅ := by
      show (canonicalTruncationData K α β).2.2 = ∅
      unfold canonicalTruncationData
      rw [dif_neg h]
    rw [this, measure_empty]
    exact ENNReal.zero_lt_top

theorem FEIS.dsum_bound {n : ℕ} (a : Fin n → Fin n → ℂ) (u v : Fin n → ℂ) (Ba Bu Bv : ℝ)
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

theorem FEIS.final_bound (n AE B₀ : ℕ) (Ca CE P W S : ℝ) (hCa : 0 ≤ Ca) (hCE : 0 ≤ CE)
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

theorem FEIS.summable_dom {ιE : Type*} (nE : ιE → ℕ) (D₀ : ℕ) (hcard : ∀ e, nE e ≤ D₀) (c : ℝ) (hc : 0 ≤ c)
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

theorem FEIS.dom
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
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ D : ιE → ℝ → ℝ, (∀ e, Integrable (D e)) ∧ (Summable fun e : ιE => ∫ t : ℝ, D e t) ∧
        ∀ (e : ιE) (t : ℝ), ∀ x ∈ C, ∀ y ∈ C,
          ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
              (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
              (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y))‖ ≤ D e t := by
  intro αm hαm ιE _iC μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf
    hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE f hf hfc hfact hbi harch C hC

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
      C hC

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
  have hEb : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ), ∀ y ∈ C,
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
    have key := FEIS.summable_dom nE D₀ hcard (Ca * (CE * CE)) (by positivity) (2 * AE)
      (fun e => ∑ v : InfinitePlace K, ((|mμ e v| : ℝ) + (|mν e v| : ℝ))) _ hW0 hWle
      (fun e => ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B₀ : ℝ))) hIe hsumm
    refine key.congr fun e => ?_
    dsimp only
    exact (integral_const_mul _ _).symm
  ·
    intro e t x hx y hy
    dsimp only
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
      have := hEb e j t y hy; rwa [hsplit] at this
    have hds := FEIS.dsum_bound _ _ _ _ _ _ (fun i j => hab e i j t) hEi hEj
      (mul_nonneg hCa.le (Real.rpow_nonneg (by positivity) _)) (by positivity)
    exact FEIS.final_bound (nE e) AE B₀ Ca CE _ _ _ hCa.le hCE.le (by positivity) (by positivity) hds

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
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)) (_hC : IsCompact C)
      (A : Set (AdelicGL2 (𝓞 K) K)) (_hA : A ⊆ C) (_hAm : MeasurableSet A)
      (B : Set (AdelicGL2 (𝓞 K) K)) (_hB : B ⊆ C) (_hBm : MeasurableSet B),
    ∫ p in A ×ˢ B, (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) p.1 * conj (EE e j ((t : ℂ) * Complex.I) p.2))) ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) =
      ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            ((∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                B.indicator (fun _ => (1 : ℂ)) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                A.indicator (fun _ => (1 : ℂ)) g * conj (EE e i ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by
  intro αm hαm ιE _iC μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf
    hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE f hf hfc hfact hbi harch
    C hC A hA hAm B hB hBm
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  obtain ⟨D, hDi, hDs, hDb⟩ := FEIS.dom K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc
    hξt N hN tysK hξu hαm ιE μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu
    hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE f hf hfc hfact hbi harch C hC

  have hac : ∀ (e : ιE) (i j : Fin (nE e)), Continuous fun t : ℝ =>
      (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
        conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) :=
    fun e i j => AutomorphicForm.continuous_integral_rightConv_axis_mul_conj_of_isArchKFinite_family K hαm (μ e) (ν e)
      (hμ e) (hν e) (hμic e) (hνic e) (hμc e) (hνc e) (φE e i) (hφE e i) (hφEK e i) (hφEf e i) (hφEjc e i)
      (hφEhol e i) (hφEKu e i) (φE e j) (hφE e j) (hφEK e j) (hφEf e j) (hφEjc e j) (hφEhol e j) (hφEKu e j) f hf hfc
  have hax : ∀ t : ℝ, ((t : ℂ) * Complex.I) ∈ {s : ℂ | s.re = 0} := fun t => by simp
  have hEc : ∀ (e : ιE) (i : Fin (nE e)),
      Continuous fun q : ℝ × AdelicGL2 (𝓞 K) K => EE e i ((q.1 : ℂ) * Complex.I) q.2 := by
    intro e i
    obtain ⟨-, -, haxs, -, -, -, hEjc, -⟩ := hEE e i
    exact hEjc.comp_continuous
      (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
      fun p => ⟨haxs (hax p.1), Set.mem_univ _⟩
  have hEg : ∀ (e : ιE) (i : Fin (nE e)) (t : ℝ),
      Continuous fun g : AdelicGL2 (𝓞 K) K => EE e i ((t : ℂ) * Complex.I) g := fun e i t =>
    (hEc e i).comp (continuous_const.prodMk continuous_id)

  set μ₀ : Measure (AdelicGL2 (𝓞 K) K) :=
    (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) with hμ₀
  haveI : IsFiniteMeasure μ₀ :=
    ⟨by rw [hμ₀, Measure.restrict_apply_univ]; exact FEIS.measure_canonicalTruncationDomain_lt_top K α β hα hαβ⟩
  set a : (e : ιE) → Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    ∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
      conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with ha
  set E : (e : ιE) → Fin (nE e) → ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun e i t x =>
    EE e i ((t : ℂ) * Complex.I) x with hE
  have hfa : ∀ e i j (t : ℝ), (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) *
      conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = a e i j t :=
    fun _ _ _ _ => rfl
  have hfE : ∀ e i (t : ℝ) x, EE e i ((t : ℂ) * Complex.I) x = E e i t x := fun _ _ _ _ => rfl
  simp only [hfa, hfE] at hDb ⊢
  have hac' : ∀ e i j, Continuous (a e i j) := fun e i j => by simpa only [hfa] using hac e i j
  have hEc' : ∀ e i, Continuous fun q : ℝ × AdelicGL2 (𝓞 K) K => E e i q.1 q.2 := fun e i => by
    simpa only [hfE] using hEc e i
  have hEg' : ∀ e i t, Continuous (E e i t) := fun e i t => by simpa only [hfE] using hEg e i t

  set F : ιE → (AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K) → ℝ → ℂ := fun e p t =>
    ∑ i : Fin (nE e), ∑ j : Fin (nE e), a e i j t * (E e i t p.1 * conj (E e j t p.2)) with hF
  have hfF : ∀ e p t, (∑ i : Fin (nE e), ∑ j : Fin (nE e), a e i j t * (E e i t p.1 * conj (E e j t p.2))) = F e p t :=
    fun _ _ _ => rfl
  have hFc : ∀ e, Continuous fun z : (AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K) × ℝ => F e z.1 z.2 := by
    intro e
    simp only [← hfF]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hac' e i j).comp continuous_snd).mul
      (((hEc' e i).comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).mul
        (Complex.continuous_conj.comp ((hEc' e j).comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))))

  have hIndB : ∀ e j t, ∫ g, B.indicator (fun _ => (1 : ℂ)) g * conj (E e j t g) ∂μ₀ =
      ∫ y in B, conj (E e j t y) ∂μ₀ := by
    intro e j t
    rw [← integral_indicator hBm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hIndA : ∀ e i t, conj (∫ g, A.indicator (fun _ => (1 : ℂ)) g * conj (E e i t g) ∂μ₀) =
      ∫ x in A, E e i t x ∂μ₀ := by
    intro e i t
    rw [← integral_conj, ← integral_indicator hAm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  simp only [hIndB, hIndA]

  rcases C.eq_empty_or_nonempty with hCe | ⟨x₀, hx₀⟩
  · have hA0 : A = ∅ := Set.subset_eq_empty hA hCe
    have hB0 : B = ∅ := Set.subset_eq_empty hB hCe
    subst hA0 hB0
    simp

  have hD0 : ∀ e t, 0 ≤ D e t := fun e t => (norm_nonneg _).trans (hDb e t x₀ hx₀ x₀ hx₀)
  have hπmem : ∀ᵐ p ∂((μ₀.prod μ₀).restrict (A ×ˢ B)), p ∈ A ×ˢ B := ae_restrict_mem (hAm.prod hBm)

  have hI1 : ∀ e, Integrable (Function.uncurry (F e)) (((μ₀.prod μ₀).restrict (A ×ˢ B)).prod volume) := by
    intro e
    refine Integrable.mono' (Integrable.mul_prod (f := fun _ => (1 : ℝ)) (integrable_const 1) (hDi e))
      (hFc e).aestronglyMeasurable ?_
    have h1 : ∀ᵐ z ∂(((μ₀.prod μ₀).restrict (A ×ˢ B)).prod volume), z.1 ∈ A ×ˢ B :=
      (Measure.quasiMeasurePreserving_fst (μ := (μ₀.prod μ₀).restrict (A ×ˢ B)) (ν := (volume : Measure ℝ))).ae hπmem
    filter_upwards [h1] with z hz
    rw [one_mul]
    exact hDb e z.2 z.1.1 (hA hz.1) z.1.2 (hB hz.2)

  have hswap : ∀ e, ∫ p, (∫ t, F e p t) ∂((μ₀.prod μ₀).restrict (A ×ˢ B)) =
      ∫ t, ∫ p, F e p t ∂((μ₀.prod μ₀).restrict (A ×ˢ B)) := fun e => integral_integral_swap (hI1 e)

  have hinner : ∀ e t, ∫ p, F e p t ∂((μ₀.prod μ₀).restrict (A ×ˢ B)) =
      ∑ i : Fin (nE e), ∑ j : Fin (nE e), a e i j t * ((∫ x in A, E e i t x ∂μ₀) * ∫ y in B, conj (E e j t y) ∂μ₀) := by
    intro e t
    have hterm : ∀ (i j : Fin (nE e)), Integrable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        a e i j t * (E e i t p.1 * conj (E e j t p.2))) ((μ₀.prod μ₀).restrict (A ×ˢ B)) := by
      intro i j
      have hcont : Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
          a e i j t * (E e i t p.1 * conj (E e j t p.2)) :=
        continuous_const.mul (((hEg' e i t).comp continuous_fst).mul
          (Complex.continuous_conj.comp ((hEg' e j t).comp continuous_snd)))
      obtain ⟨Bd, hBd⟩ := (hC.prod hC).exists_bound_of_continuousOn hcont.continuousOn
      refine (integrable_const Bd).mono' hcont.aestronglyMeasurable ?_
      filter_upwards [hπmem] with p hp
      exact hBd p ⟨hA hp.1, hB hp.2⟩
    simp only [← hfF]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hterm i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hterm i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    congr 1
    exact setIntegral_prod_mul (fun x => E e i t x) (fun y => conj (E e j t y)) A B

  have hG_int : ∀ e, Integrable (fun p => ∫ t, F e p t) ((μ₀.prod μ₀).restrict (A ×ˢ B)) :=
    fun e => (hI1 e).integral_prod_left
  have hG_bd : ∀ e, ∫ p, ‖∫ t, F e p t‖ ∂((μ₀.prod μ₀).restrict (A ×ˢ B)) ≤
      (∫ t, D e t) * (((μ₀.prod μ₀).restrict (A ×ˢ B)) Set.univ).toReal := by
    intro e
    have := integral_mono_of_nonneg (μ := (μ₀.prod μ₀).restrict (A ×ˢ B))
      (Filter.Eventually.of_forall fun p => norm_nonneg (∫ t, F e p t)) (integrable_const (∫ t, D e t)) ?_
    · rw [integral_const, smul_eq_mul, mul_comm] at this
      simpa [Measure.real] using this
    · filter_upwards [hπmem] with p hp
      exact norm_integral_le_of_norm_le (hDi e)
        (Filter.Eventually.of_forall fun t => hDb e t p.1 (hA hp.1) p.2 (hB hp.2))
  have hsumG : Summable fun e => ∫ p, ‖∫ t, F e p t‖ ∂((μ₀.prod μ₀).restrict (A ×ˢ B)) :=
    Summable.of_nonneg_of_le (fun e => integral_nonneg fun p => norm_nonneg _) hG_bd (hDs.mul_right _)
  have hts := integral_tsum_of_summable_integral_norm hG_int hsumG

  rw [← hts]
  refine tsum_congr fun e => ?_
  rw [hswap e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [hinner e t]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end S_AutomorphicForm_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation_mul_conj_eq_tsum_integral_sum_mul_setIntegral_indicator_mul_conj
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation_mul_conj_eq_tsum_integral_sum_mul_setIntegral_indicator_mul_conj (solution)
