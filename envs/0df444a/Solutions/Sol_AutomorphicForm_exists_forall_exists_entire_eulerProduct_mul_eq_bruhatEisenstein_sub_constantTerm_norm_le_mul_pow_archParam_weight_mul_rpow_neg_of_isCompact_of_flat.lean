-- Prove2me | solution 1 for AutomorphicForm.exists_forall_exists_entire_eulerProduct_mul_eq_bruhatEisenstein_sub_constantTerm_norm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4ec61e89-70f0-5cb7-9454-f7dd4fae8fdd

import Theorems.Thm_AutomorphicForm_exists_forall_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_norm_tsum_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
import Theorems.Thm_AutomorphicForm_bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
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
import Definitions.Def_AutomorphicForm_ConstantTerm
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_exists_entire_eulerProduct_mul_eq_bruhatEisenstein_sub_constantTerm_norm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain Filter Topology
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
    (Ω : Set (AdelicGL2 (𝓞 K) K)) (hΩ : IsCompact Ω) (c' : ℝ) (hc' : 0 < c') (N' : ℕ)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (C : ℝ) (A : ℕ), SK ⊆ S ∧ 0 < C ∧
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
      (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s h =>
      ψf s h + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * h)
    ∃ V : ℂ → AdelicGL2 (𝓞 K) K → ℂ,
      (∀ h : AdelicGL2 (𝓞 K) K, Differentiable ℂ (fun s => V s h)) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 K) K), 1 < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
            (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * V s h
          = E s h -
            AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun u => AutomorphicForm.unipotentGL2 u) (E s) h) ∧
      ∀ (t : ℝ) (b : ↥(adelicBorel (𝓞 K) K)) (ω : AdelicGL2 (𝓞 K) K),
        ω ∈ Ω → c' ≤ (((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)) →
        ‖V ((t : ℂ) * Complex.I) ((b : AdelicGL2 (𝓞 K) K) * ω)‖ ≤
          C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
            (((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)) ^ (-(N' : ℝ)) := by
  intro αm
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  have hψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K
  obtain ⟨S, C, A, hSK, hC, H⟩ :=
    AutomorphicForm.exists_forall_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_norm_tsum_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat K SK ξK hξc hξt N hN tysK w hξw (NumberField.StandardAddChar.stdAddChar K) hψ Ω hΩ c' hc' N'
  refine ⟨S, C, A, hSK, hC, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK hψff hψfjc hψfhol hψfKu
    hψfflat hψflev hψfty hψfn ϖ hϖ
  obtain ⟨𝒱, h1, h2, h4, h5⟩ := H hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK
    hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty hψfn ϖ hϖ
  intro E
  refine ⟨fun s h => ∑' ξ : {ξ : K // ξ ≠ 0}, 𝒱 ξ s h, ?_, ?_, ?_⟩

  · intro h s₀
    obtain ⟨u, hu, hle⟩ := h4 h (Metric.closedBall s₀ 1) (isCompact_closedBall _ _)
    have hd : DifferentiableOn ℂ (fun s => ∑' ξ : {ξ : K // ξ ≠ 0}, 𝒱 ξ s h) (Metric.ball s₀ 1) :=
      Complex.differentiableOn_tsum_of_summable_norm hu
        (fun ξ => (h1 ξ h).differentiableOn)
        Metric.isOpen_ball (fun ξ w hw => hle ξ w (Metric.ball_subset_closedBall hw))
    exact hd.differentiableAt (Metric.ball_mem_nhds _ one_pos)

  · intro s h hs
    have hφc : ∀ s, Continuous (ψf s) := fun s => hψfjc.comp (Continuous.prodMk_right s)
    have hF := AutomorphicForm.bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary K hαm μ ν
      hμ hν (NumberField.StandardAddChar.stdAddChar K) hψ ψf hψf hψfK hψff hφc h s hs
    have hEsub : E s h - constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun u => unipotentGL2 u) (E s) h
        = ∑' ξ : {ξ : K // ξ ≠ 0}, whittakerCoefficient K (productionPins K)
            (NumberField.StandardAddChar.stdAddChar K) (E s) (ξ : K) h := by
      rw [sub_eq_iff_eq_add']
      exact hF
    rw [hEsub]
    have hWξ : ∀ ξ : {ξ : K // ξ ≠ 0}, whittakerCoefficient K (productionPins K)
        (NumberField.StandardAddChar.stdAddChar K) (E s) (ξ : K) h
          = (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * 𝒱 ξ s h := fun ξ => h2 ξ s h hs
    rw [tsum_congr hWξ, tsum_mul_left]

  · intro t b ω hω hb
    obtain ⟨hsum, hle⟩ := h5 t b ω hω hb
    calc ‖∑' ξ : {ξ : K // ξ ≠ 0}, 𝒱 ξ ((t : ℂ) * Complex.I) ((b : AdelicGL2 (𝓞 K) K) * ω)‖
        ≤ ∑' ξ : {ξ : K // ξ ≠ 0}, ‖𝒱 ξ ((t : ℂ) * Complex.I) ((b : AdelicGL2 (𝓞 K) K) * ω)‖ :=
          norm_tsum_le_tsum_norm hsum
      _ ≤ _ := hle

end S_AutomorphicForm_exists_forall_exists_entire_eulerProduct_mul_eq_bruhatEisenstein_sub_constantTerm_norm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_exists_entire_eulerProduct_mul_eq_bruhatEisenstein_sub_constantTerm_norm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat (solution)
