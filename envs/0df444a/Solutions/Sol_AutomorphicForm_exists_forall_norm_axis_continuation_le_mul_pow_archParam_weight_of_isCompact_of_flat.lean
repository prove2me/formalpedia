-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/afe03dec-fc3c-5b3e-bb4c-44c8ef9b2e78

import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_centreCutSiegelSet_mul_of_flat
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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

namespace P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (Ω : Set (AdelicGL2 (𝓞 K) K)), IsCompact Ω →
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g))
      (t : ℝ), ∀ y ∈ Ω,
      ‖Eψ ((t : ℂ) * Complex.I) y‖ ≤ C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A := by
  intro αm Ω hΩ
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K

  obtain ⟨T, c, hc, u, hcov⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov12 := hcov 1 2 (by norm_num) (by norm_num)
  have hTc : IsCompact ((T : Set (AdelicGL2 (𝓞 K) K))) := T.finite_toSet.isCompact

  obtain ⟨C₁, A₁, B₁, hC₁, hG⟩ :=
    AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_centreCutSiegelSet_mul_of_flat K SK ξK hξc hξt N hN tysK w hξw
      c u 1 2 hc (T : Set (AdelicGL2 (𝓞 K) K)) hTc

  obtain ⟨h₀, hh₀, hfloor⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact K c u 1 2 hc
      (T : Set (AdelicGL2 (𝓞 K) K)) hTc

  rcases Ω.eq_empty_or_nonempty with hΩe | hΩne
  · refine ⟨1, 0, one_pos, ?_⟩
    intro hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hψfn Oψ Eψ Nψ hEψ t y hy
    rw [hΩe] at hy
    exact absurd hy (Set.notMem_empty y)

  have hHc : Continuous (NumberField.AdelicHeight.adelicHeight K) := NumberField.AdelicHeight.continuous_adelicHeight K
  obtain ⟨yM, hyM, hmax⟩ := hΩ.exists_isMaxOn hΩne hHc.continuousOn
  obtain ⟨ym, hym, hmin⟩ := hΩ.exists_isMinOn hΩne hHc.continuousOn
  have hHm : 0 < NumberField.AdelicHeight.adelicHeight K ym := NumberField.AdelicHeight.adelicHeight_pos ym
  obtain ⟨hunip, hcent⟩ := NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul K

  have hpt : ∀ y ∈ Ω, ∃ (γ : GL (Fin 2) K) (z : (AdeleRing (𝓞 K) K)ˣ) (sx : AdelicGL2 (𝓞 K) K) (x : AdelicGL2 (𝓞 K) K),
      sx ∈ centreCutSiegelSet K c u 1 2 ∧ x ∈ (T : Set (AdelicGL2 (𝓞 K) K)) ∧
      sx * x = AutomorphicForm.globalPoints (𝓞 K) K γ * (y * AutomorphicForm.centralScalar (𝓞 K) K z) ∧
      NumberField.AdelicHeight.adelicHeight K (sx * x) ^ B₁ ≤
        max ((max (NumberField.AdelicHeight.adelicHeight K yM) (NumberField.AdelicHeight.adelicHeight K ym)⁻¹) ^ B₁) (h₀ ^ B₁) := by
    intro y hy
    obtain ⟨γ, z, hmem⟩ := hcov12 y
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨x, hxT, hmem⟩ := hmem
    obtain ⟨sx, hsx, hEq⟩ := hmem
    have hEq' : sx * x = AutomorphicForm.globalPoints (𝓞 K) K γ * (y * AutomorphicForm.centralScalar (𝓞 K) K z) := by
      rw [← mul_assoc]; exact hEq
    refine ⟨γ, z, sx, x, hsx, hxT, hEq', ?_⟩
    have hlow : h₀ ≤ NumberField.AdelicHeight.adelicHeight K (sx * x) := hfloor sx hsx x hxT
    have hHy : 0 < NumberField.AdelicHeight.adelicHeight K y := NumberField.AdelicHeight.adelicHeight_pos y

    have hup : NumberField.AdelicHeight.adelicHeight K (sx * x) ≤
        max (NumberField.AdelicHeight.adelicHeight K yM) (NumberField.AdelicHeight.adelicHeight K ym)⁻¹ := by
      rw [hEq', AutomorphicForm.SiegelCovering.mul_centralScalar_comm, ← mul_assoc,
        AutomorphicForm.SiegelCovering.mul_centralScalar_comm, mul_assoc, hcent]
      by_cases hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
      · rw [NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup K
          ((AutomorphicForm.mem_borelSubgroup_iff K).mpr hγ) y]
        exact le_max_of_le_left (hmax hy)
      · have h1 := NumberField.AdelicHeight.adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ y
        refine le_max_of_le_right ?_
        rw [← one_div, le_div_iff₀ hHm]
        calc NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.globalPoints (𝓞 K) K γ * y) *
              NumberField.AdelicHeight.adelicHeight K ym
            ≤ NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.globalPoints (𝓞 K) K γ * y) *
              NumberField.AdelicHeight.adelicHeight K y := by
              gcongr
              · exact (NumberField.AdelicHeight.adelicHeight_pos _).le
              · exact hmin hy
          _ ≤ 1 := h1
    by_cases hB : 0 ≤ B₁
    · exact le_max_of_le_left (Real.rpow_le_rpow (hh₀.le.trans hlow) hup hB)
    · exact le_max_of_le_right (Real.rpow_le_rpow_of_nonpos hh₀ hlow (le_of_lt (not_le.mp hB)))
  have hMpos : 0 < max ((max (NumberField.AdelicHeight.adelicHeight K yM) (NumberField.AdelicHeight.adelicHeight K ym)⁻¹) ^ B₁) (h₀ ^ B₁) :=
    lt_max_of_lt_right (Real.rpow_pos_of_pos hh₀ _)
  refine ⟨C₁ * max ((max (NumberField.AdelicHeight.adelicHeight K yM) (NumberField.AdelicHeight.adelicHeight K ym)⁻¹) ^ B₁) (h₀ ^ B₁), A₁,
    mul_pos hC₁ hMpos, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hψfn Oψ Eψ Nψ hEψ t y hy
  obtain ⟨γ, z, sx, x, hsx, hxT, hEq, hHB⟩ := hpt y hy
  have hs : ((t : ℂ) * Complex.I) ∈ Oψ := hEψ.2.2.1 (by simp)
  have hAut := AutomorphicForm.axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family K hαm μ ν hμ hν
    hμic hνic hμc hνc ψf hψf hψfK hψff hψfjc hψfhol hψfKu Oψ Eψ Nψ hEψ ((t : ℂ) * Complex.I) hs γ
    (y * AutomorphicForm.centralScalar (𝓞 K) K z)
  have hCen := AutomorphicForm.axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family K hαm μ ν hμ hν
    hμic hνic hμc hνc ψf hψf hψfK hψff hψfjc hψfhol hψfKu Oψ Eψ Nψ hEψ ((t : ℂ) * Complex.I) hs z y
  have hGb := hG hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hψfn Oψ Eψ Nψ hEψ t sx hsx x hxT
  have hnorm : ‖Eψ ((t : ℂ) * Complex.I) y‖ = ‖Eψ ((t : ℂ) * Complex.I) (sx * x)‖ := by
    rw [hEq, hAut, AutomorphicForm.SiegelCovering.mul_centralScalar_comm, hCen, norm_mul, norm_mul, hμ z, hν z,
      one_mul, one_mul]
  rw [hnorm]
  calc ‖Eψ ((t : ℂ) * Complex.I) (sx * x)‖
      ≤ C₁ * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A₁ * NumberField.AdelicHeight.adelicHeight K (sx * x) ^ B₁ := hGb
    _ ≤ C₁ * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A₁ *
          max ((max (NumberField.AdelicHeight.adelicHeight K yM) (NumberField.AdelicHeight.adelicHeight K ym)⁻¹) ^ B₁) (h₀ ^ B₁) := by
        gcongr
    _ = _ := by ring

end S_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat (solution)
