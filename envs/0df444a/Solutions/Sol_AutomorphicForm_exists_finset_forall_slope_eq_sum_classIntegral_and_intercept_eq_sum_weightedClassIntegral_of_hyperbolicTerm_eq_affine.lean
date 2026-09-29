-- Prove2me | solution 1 for AutomorphicForm.exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/92a96dbc-3375-5825-a4af-a40a9a6de8aa

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_setIntegral_canonicalTruncationDomain_adelicKernelHyperbolicPart_sub_indicator_constantTerm_eq_mul_sum_mul_integral_add_sum_of_eq_mul_sum_orbital_add_sum_weightedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply"
p2m_attr_erase "simp" "Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace H5ASMi

theorem affine_unique {A B A' B' : ℂ} {R₀ : ℝ}
    (h : ∀ R : ℝ, R₀ ≤ R → (R : ℂ) * A + B = (R : ℂ) * A' + B') : A = A' ∧ B = B' := by
  have h0 := h R₀ le_rfl
  have h1 := h (R₀ + 1) (by linarith)
  have hA : A = A' := by
    have : ((R₀ + 1 : ℝ) : ℂ) * A + B - ((R₀ : ℂ) * A + B) = ((R₀ + 1 : ℝ) : ℂ) * A' + B' - ((R₀ : ℂ) * A' + B') := by
      rw [h1, h0]
    push_cast at this
    linear_combination this
  refine ⟨hA, ?_⟩
  rw [hA] at h0
  linear_combination h0
end H5ASMi

open AutomorphicForm in
open scoped TensorProduct.RightActions in
open scoped Classical in

theorem H5ASM.Kclass
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (hdeg : (Module.finrank K L).Prime)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (c₀ : ℂ)
    (hgeo :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
        (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f)
        (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
        (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
        (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        c₀ * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →

      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
        (hSLF : IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))
        (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL)
        (harch : IsArchBiFinite L tysL φL)
        (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ)
        (hfam : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fam m) ∧
          IsArchBiFinite K tysK (fam m) ∧
          IsArchTestFactor K faK ∧
          (∀ v ∈ SK, IsLocalTestFn K v (fSK v)) ∧
          ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
            IsFinTestFactor K ff ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
                ff h = ∏ v ∈ SK ∪ T,
                  (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                    else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) →
                ff h = 0) ∧
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
        (hmatch : AreMatchingAt K L σ.symm (SK ∪ T) φL
          (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x)),
      ∀ (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ), ξK ∈ Ξ →
      ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      ∀ (A B : ℂ) (R₀ : ℝ),
      (∀ R : ℝ, R₀ ≤ R →
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (R : ℂ) * A + B) →
      ∀ (DK : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K)
        (hgenK : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K))
    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K K DK 1 h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 K) K)))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant]

    (Λ₀K : Subgroup (GL (Fin 2) K))
    (hΛ₀K : ∀ γ : GL (Fin 2) K, γ ∈ Λ₀K ↔ (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ Set.range (algebraMap K K))
    (κ₀K : ℝ) (hκ₀Kpos : 0 < κ₀K) (ΩK' : Set HK)
    (hΩK' : IsFundamentalDomain ((Λ₀K.map (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf HK) ΩK' μHK)
    (hκ₀K : ∀ (y : AdelicGL2 (𝓞 K) K) (R : ℝ),
      ∫⁻ h in ΩK', ‖Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y))‖ₑ ∂μHK =
        ENNReal.ofReal (κ₀K * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight K y)
          - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y))|))

    (hκ₀K' : ∀ (y : AdelicGL2 (𝓞 K) K) (R : ℝ),
        (NumberField.AdelicHeight.adelicHeight K y *
            NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y) ≤ Real.exp (2 * R) →
          IntegrableOn (fun h : HK => Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y))) ΩK' μHK ∧
          ∫ h in ΩK', Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)) ∂μHK =
            ((κ₀K * (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight K y)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y))) : ℝ) : ℂ)))

    (ΔK : Set (GL (Fin 2) K))
    (hΔKd : ∀ t ∈ ΔK, (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1)
    (hΔKdisj : ∀ t ∈ ΔK, ∀ t' ∈ ΔK, t ≠ t' →
      Disjoint {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}
        {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)})
    (hΔKcov : {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgenK (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ ΔK, {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)})
,
      ∃ Δf : Finset (GL (Fin 2) K), (↑Δf ⊆ ΔK) ∧
        (∀ t ∈ ΔK, t ∉ Δf → ∀ y : AdelicGL2 (𝓞 K) K, (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m ((y)⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * (y))) ∂νZK) = 0) ∧
        (∀ t ∈ Δf, Integrable (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) => (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK))
            (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) ∧
          Integrable (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK))
            (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) ∧
        A = ∑ t ∈ Δf, 2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K), (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) ∧
        B = ∑ t ∈ Δf, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
                - Real.log (NumberField.AdelicHeight.adelicHeight K
                    (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) := by
  intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
    ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ξK hξK m hm A B R₀ hSPK DK hgenK
    HK hHKc hHK μHK _ _ Λ₀K hΛ₀K κ₀K hκ₀Kpos ΩK' hΩK' hκ₀K hκ₀K' ΔK hΔKd hΔKdisj hΔKcov
  have hξK1 : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ξK ⟨DK.unitsAct 1 z, Subgroup.mem_top _⟩ = ξK ⟨z, Subgroup.mem_top z⟩ := by
    intro z
    simp only [map_one, MulAut.one_apply]
  obtain ⟨hξKc, hξKt, -⟩ := (hΞ ξK).1 hξK
  obtain ⟨-, -, hfaK, hfSK, ff, hffin, hprod, hvan, hfeq⟩ := hfam m hm
  have hFT : AutomorphicForm.IsFactorizableTestFn K (fam m) := ⟨faK, ff, hfaK, hffin, hfeq⟩
  obtain ⟨hc0, hTc, hΦ₀S, hΦ₀s, hΦ₀⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have C0 :=
    AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn
      K K α β hα hαβ ΦK νZK ΩK hΩK DK 1 hgenK ξK hξKc hξKt _ _ _ _ hc0 _ hTc _ hΦ₀S hΦ₀s hΦ₀
  have C1 := C0 HK hHKc hHK μHK
  have C2 := C1 Λ₀K hΛ₀K κ₀K hκ₀Kpos ΩK' hΩK'
  have C3 := C2 hκ₀K
  have C4 := C3 hκ₀K'
  have C5 := C4 ΔK hΔKd hΔKdisj hΔKcov
  have CP := C5 hξK1 (fam m) hFT
  clear C0 C1 C2 C3 C4 C5
  obtain ⟨Δf, hsub, hvan0, hint, R₁, hR₁⟩ := CP
  have BR :=
    AutomorphicForm.setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell
      K α β ΦK ΦK νZK ΩK DK hgenK ξK (fam m)
  have key : ∀ R : ℝ, max R₀ R₁ ≤ R →
      (R : ℂ) * A + B = (R : ℂ) * (∑ t ∈ Δf, 2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K), (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                AutomorphicForm.sigmaAdelicAct K K DK 1 (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) + (∑ t ∈ Δf, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
                - Real.log (NumberField.AdelicHeight.adelicHeight K
                    (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                AutomorphicForm.sigmaAdelicAct K K DK 1 (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) := by
    intro R hR
    have h1 := hSPK R (le_trans (le_max_left _ _) hR)
    have h2 := (hR₁ R (le_trans (le_max_right _ _) hR)).2.2
    rw [← h1, ← BR R, h2]
  have hAB := H5ASMi.affine_unique key
  simp only [AutomorphicForm.sigmaAdelicAct_one, MonoidHom.id_apply] at hvan0 hint hAB
  exact ⟨Δf, hsub, hvan0, hint, hAB.1, hAB.2⟩

open AutomorphicForm in
open scoped TensorProduct.RightActions in
open scoped Classical in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (hdeg : (Module.finrank K L).Prime)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (c₀ : ℂ)
    (hgeo :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
        (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f)
        (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
        (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
        (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        c₀ * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →

      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
        (hSLF : IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))
        (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL)
        (harch : IsArchBiFinite L tysL φL)
        (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ)
        (hfam : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fam m) ∧
          IsArchBiFinite K tysK (fam m) ∧
          IsArchTestFactor K faK ∧
          (∀ v ∈ SK, IsLocalTestFn K v (fSK v)) ∧
          ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
            IsFinTestFactor K ff ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
                ff h = ∏ v ∈ SK ∪ T,
                  (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                    else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) →
                ff h = 0) ∧
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
        (hmatch : AreMatchingAt K L σ.symm (SK ∪ T) φL
          (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x)),
      ∀ (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ), ξK ∈ Ξ →
      ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      ∀ (A B : ℂ) (R₀ : ℝ),
      (∀ R : ℝ, R₀ ≤ R →
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (R : ℂ) * A + B) →
      ∀ (DK : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K)
        (hgenK : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K))
    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K K DK 1 h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 K) K)))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant]

    (Λ₀K : Subgroup (GL (Fin 2) K))
    (hΛ₀K : ∀ γ : GL (Fin 2) K, γ ∈ Λ₀K ↔ (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ Set.range (algebraMap K K))
    (κ₀K : ℝ) (hκ₀Kpos : 0 < κ₀K) (ΩK' : Set HK)
    (hΩK' : IsFundamentalDomain ((Λ₀K.map (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf HK) ΩK' μHK)
    (hκ₀K : ∀ (y : AdelicGL2 (𝓞 K) K) (R : ℝ),
      ∫⁻ h in ΩK', ‖Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y))‖ₑ ∂μHK =
        ENNReal.ofReal (κ₀K * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight K y)
          - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y))|))

    (hκ₀K' : ∀ (y : AdelicGL2 (𝓞 K) K) (R : ℝ),
        (NumberField.AdelicHeight.adelicHeight K y *
            NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y) ≤ Real.exp (2 * R) →
          IntegrableOn (fun h : HK => Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y))) ΩK' μHK ∧
          ∫ h in ΩK', Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)) ∂μHK =
            ((κ₀K * (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight K y)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y))) : ℝ) : ℂ)))

    (ΔK : Set (GL (Fin 2) K))
    (hΔKd : ∀ t ∈ ΔK, (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1)
    (hΔKdisj : ∀ t ∈ ΔK, ∀ t' ∈ ΔK, t ≠ t' →
      Disjoint {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}
        {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)})
    (hΔKcov : {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgenK (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ ΔK, {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)})

    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τK : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))))
    (hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure)
    (hτKc : ∀ γ ∈ ΔK, ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
          g (s : AdelicGL2 (𝓞 K) K) ∂(τK γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (IK JK : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK γ z))
    (hJK : ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
            -Real.log (NumberField.AdelicHeight.adelicHeight K x)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (JK γ z)),
      ∃ Δf : Finset (GL (Fin 2) K), (↑Δf ⊆ ΔK) ∧
      ∀ S : Finset (GL (Fin 2) K), Δf ⊆ S → (↑S ⊆ ΔK) →
      (∀ t ∈ S, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z) νZK) ∧
      (∀ t ∈ S, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK t z) νZK) ∧
      (A = ∑ t ∈ S, 2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z ∂νZK)) ∧
      (B = ∑ t ∈ S, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK t z ∂νZK)) := by
  intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
    ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ξK hξK m hm A B R₀ hSPK DK hgenK
    HK hHKc hHK μHK _ _ Λ₀K hΛ₀K κ₀K hκ₀Kpos ΩK' hΩK' hκ₀K hκ₀K' ΔK hΔKd hΔKdisj hΔKcov
    cHK hcHK hHKμ cτK hcτK τK hτK hτKc IK JK hIK hJK
  have KC := H5ASM.Kclass K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
      T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
      ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch
    ξK hξK m hm A B R₀ hSPK DK hgenK HK hHKc hHK μHK Λ₀K hΛ₀K κ₀K hκ₀Kpos ΩK' hΩK' hκ₀K hκ₀K' ΔK hΔKd hΔKdisj hΔKcov
  obtain ⟨Δf, hsub, hvan0, hint, hAK, hBK⟩ := KC
  obtain ⟨hξKc, hξKt, -⟩ := (hΞ ξK).1 hξK
  obtain ⟨-, -, hfaK, hfSK, ff, hffin, hprod, hvan, hfeq⟩ := hfam m hm
  have hFT : AutomorphicForm.IsFactorizableTestFn K (fam m) := ⟨faK, ff, hfaK, hffin, hfeq⟩
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K (fam m) hFT
  have hHK2 : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0) := by
    intro h
    rw [hHK h]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, ?_⟩
      rw [AutomorphicForm.sigmaAdelicAct_one, MonoidHom.id_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
  refine ⟨Δf, hsub, fun S hΔS hSΔ => ?_⟩
  have hΔf : ∀ γ ∈ S, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1 := by
    intro γ hγ
    obtain ⟨h1, h2, h3⟩ := hΔKd γ (hSΔ hγ)
    rw [Algebra.norm_self, MonoidHom.id_apply] at h3
    exact ⟨h1, h2, h3⟩

  have hlamO0 : ∀ γ ∈ S, γ ∉ Δf →
      (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) => (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)) = fun _ => 0 := by
    intro γ hγ hγf
    funext q
    exact hvan0 γ (hSΔ hγ) hγf _
  have hlamWO0 : ∀ γ ∈ S, γ ∉ Δf →
      (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)) = fun _ => 0 := by
    intro γ hγ hγf
    funext q
    rw [hvan0 γ (hSΔ hγ) hγf _, mul_zero]
  have hO_S : ∀ γ ∈ S, Integrable (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) => (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)) (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) := by
    intro γ hγ
    by_cases hγf : γ ∈ Δf
    · exact (hint γ hγf).1
    · rw [hlamO0 γ hγ hγf]; exact integrable_zero _ _ _
  have hWO_S : ∀ γ ∈ S, Integrable (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)) (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) := by
    intro γ hγ
    by_cases hγf : γ ∈ Δf
    · exact (hint γ hγf).2
    · rw [hlamWO0 γ hγ hγf]; exact integrable_zero _ _ _
  have hO0 : ∀ γ ∈ S, γ ∉ Δf → (∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K), (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) = 0 := by
    intro γ hγ hγf
    show MeasureTheory.integral (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) => (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)) = 0
    rw [hlamO0 γ hγ hγf]; exact integral_zero _ _
  have hWO0 : ∀ γ ∈ S, γ ∉ Δf → (∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
                - Real.log (NumberField.AdelicHeight.adelicHeight K
                    (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) = 0 := by
    intro γ hγ hγf
    show MeasureTheory.integral (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)) = 0
    rw [hlamWO0 γ hγ hγf]; exact integral_zero _ _
  have hsum1 : (∑ t ∈ S, 2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K), (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) = ∑ t ∈ Δf, 2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K), (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) := by
    symm
    apply Finset.sum_subset hΔS
    intro t ht htf
    rw [hO0 t ht htf, mul_zero]
  have hsum2 : (∑ t ∈ S, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
                - Real.log (NumberField.AdelicHeight.adelicHeight K
                    (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) = ∑ t ∈ Δf, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
                - Real.log (NumberField.AdelicHeight.adelicHeight K
                    (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              fam m (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K t *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) := by
    symm
    apply Finset.sum_subset hΔS
    intro t ht htf
    rw [hWO0 t ht htf, mul_zero]
  have B0 := AutomorphicForm.setIntegral_canonicalTruncationDomain_adelicKernelHyperbolicPart_sub_indicator_constantTerm_eq_mul_sum_mul_integral_add_sum_of_eq_mul_sum_orbital_add_sum_weightedOrbital
      K α β hα hαβ ΦK νZK ΩK hΩK ξK hξKc hξKt HK hHKc hHK2 μHK cHK hcHK hHKμ cτK hcτK τK hτK (fam m) hfc hfcs
  have key : ∀ R : ℝ, R₀ ≤ R → (R : ℂ) * A + B = (R : ℂ) * (∑ t ∈ S, 2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z ∂νZK)) + (∑ t ∈ S, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK t z ∂νZK)) := by
    intro R hR
    have hdisp := hSPK R hR
    rw [hAK, hBK, ← hsum1, ← hsum2] at hdisp
    have B1 := B0 R S (fun t => ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1))) hΔf (fun γ hγ => hτKc γ (hSΔ hγ))
      hO_S hWO_S hdisp IK JK
      (fun γ hγ z => hIK γ (hSΔ hγ) z) (fun γ hγ z => hJK γ (hSΔ hγ) z)
    rw [← hSPK R hR]
    exact B1.2.2
  have hintK : (∀ t ∈ S, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z) νZK) ∧ (∀ t ∈ S, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK t z) νZK) := by
    have hdisp := hSPK R₀ le_rfl
    rw [hAK, hBK, ← hsum1, ← hsum2] at hdisp
    have B1 := B0 R₀ S (fun t => ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1))) hΔf (fun γ hγ => hτKc γ (hSΔ hγ))
      hO_S hWO_S hdisp IK JK
      (fun γ hγ z => hIK γ (hSΔ hγ) z) (fun γ hγ z => hJK γ (hSΔ hγ) z)
    exact ⟨B1.1, B1.2.1⟩
  have hAB := H5ASMi.affine_unique key
  exact ⟨hintK.1, hintK.2, hAB.1, hAB.2⟩

end S_AutomorphicForm_exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine (solution)
