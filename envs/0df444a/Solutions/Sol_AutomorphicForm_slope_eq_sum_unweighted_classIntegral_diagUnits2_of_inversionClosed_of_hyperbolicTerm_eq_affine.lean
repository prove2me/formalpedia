-- Prove2me | solution 1 for AutomorphicForm.slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2e4fd4ff-b128-5655-8a21-f5bc9a242a9d

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
import Theorems.Thm_AutomorphicForm_exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Theorems.Thm_AutomorphicForm_forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine
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

namespace AutomorphicForm p2m_export "AutomorphicForm" "centralizerBorel semiLocalIntegralSet twistedCentralizerBorel IsOrbitalIntegralOn AreMatchingLocal semiLocalComponent IsSemiLocalFactorization IsUnitFactorizableAboveOfType AreMatchingAt IsUnitFactorizableOfTypeAt IsLocalTestFn localIntegralSet IsBiInvariantUnder IsArchTestFactor IsFinTestFactor ArchTypeFamily IsArchBiFinite productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 constantTerm HeckeEigensystem.cNorm HeckeEigensystem sigmaAdelicAct centralCell hyperbolicCell ellipticCell highSet adelicKernelCentralPart adelicKernelHyperbolicPart adelicKernelEllipticPart SatakeCombination.slotIndex SatakeCombination.slotFamilyCoeff canonicalTruncationDomain IsWeightedOrbitalIntegralOn adelicWeyl exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2" end AutomorphicForm
p2m_open_scoped "AutomorphicForm" in

theorem AutomorphicForm.globalPoints_diagUnits2_hw47 (K : Type) [Field K] [NumberField K] (u : Kˣ) :
    AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 u 1) =
      diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1 := by
  apply Units.ext
  ext i j
  change (algebraMap K (AdeleRing (𝓞 K) K)) (((diagUnits2 u 1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) = _
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp

p2m_open_scoped "AutomorphicForm" in

theorem AutomorphicForm.centralScalar_comm_hw47 (K : Type) [Field K] [NumberField K]
    (z : (AdeleRing (𝓞 K) K)ˣ) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    AutomorphicForm.centralScalar (𝓞 K) K z * g = g * AutomorphicForm.centralScalar (𝓞 K) K z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change Matrix.scalar (Fin 2) ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine.AutomorphicForm in
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

    (ΔKfin : Finset (GL (Fin 2) K))
    (hΔKf : ∀ γ ∈ ΔKfin, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (hΔKinj : ∀ γ ∈ ΔKfin, ∀ γ' ∈ ΔKfin,
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 =
        (γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1 → γ = γ')
    (hΔKinv : ∀ γ ∈ ΔKfin, ∃ u : Kˣ, (u : K) ≠ 1 ∧ γ = diagUnits2 u 1 ∧ diagUnits2 u⁻¹ 1 ∈ ΔKfin)
    (hΔKc : ∀ u : Kˣ, (u : K) ≠ 1 →
      (∀ γ ∈ ΔKfin, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ (u : K)) →
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          fam m (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z *
            diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0)

    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τK : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))))
    (hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure)
    (hτKc : ∀ γ ∈ ΔKfin, ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
          g (s : AdelicGL2 (𝓞 K) K) ∂(τK γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (IK JK : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ γ ∈ ΔKfin, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK γ z))
    (hJK : ∀ γ ∈ ΔKfin, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
            -Real.log (NumberField.AdelicHeight.adelicHeight K x)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (JK γ z)),
      (∀ γ ∈ ΔKfin, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z) νZK) ∧
      A = ∑ γ ∈ ΔKfin, (κ₀K : ℂ) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK) := by
  intro T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
    ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ξK hξK m hm A B R₀ hSPK DK hgenK
    HK hHKc hHK μHK _iH _iR Λ₀K hΛ₀K κ₀K hκ₀Kpos ΩK' hΩK' hκ₀K hκ₀K' ΔKfin hΔKf hΔKinj hΔKinv hΔKc
    cHK hcHK hHKμ cτK hcτK τK hτK hτKc IK JK hIK hJK
  classical

  have hnorm : ∀ x : K, Algebra.norm K x = x := fun x => by rw [Algebra.norm_self, MonoidHom.id_apply]
  have e00 : ∀ u v : Kˣ, ((diagUnits2 u v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = (u : K) := fun _ _ => rfl
  have e11 : ∀ u v : Kˣ, ((diagUnits2 u v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = (v : K) := fun _ _ => rfl
  have e10 : ∀ u v : Kˣ, ((diagUnits2 u v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := fun _ _ => rfl
  have e01 : ∀ u v : Kˣ, ((diagUnits2 u v : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := fun _ _ => rfl
  have hrat : ∀ u : Kˣ, ((diagUnits2 u 1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 /
      ((diagUnits2 u 1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K) := by
    intro u; rw [e00, e11, Units.val_one, div_one]
  have hinj1 : ∀ u u' : Kˣ, diagUnits2 u (1 : Kˣ) = diagUnits2 u' 1 → u = u' := by
    intro u u' h
    apply Units.ext
    have h' := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simpa only [e00] using h'

  obtain ⟨-, hcov29, hdis29⟩ :=
    LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal (K := K) (L := K) hgenK
  let cls : GL (Fin 2) K → Set (GL (Fin 2) K) := fun t => {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
      t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}
  let good : GL (Fin 2) K → Prop := fun t =>
      (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        (t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1
  have hgoodU : ∀ u : Kˣ, (u : K) ≠ 1 → good (diagUnits2 u 1) := fun u hu => ⟨e10 u 1, e01 u 1, by rw [hrat]; exact hu⟩
  have hgoodΔ : ∀ γ ∈ ΔKfin, good γ := fun γ hγ => hΔKf γ hγ
  have hclsU : ∀ u u' : Kˣ, cls (diagUnits2 u' 1) = cls (diagUnits2 u 1) ↔ ((u' : K) = u ∨ (u' : K) = (u : K)⁻¹) := by
    intro u u'
    have h := (hdis29 (diagUnits2 u 1) (diagUnits2 u' 1) ⟨e10 u 1, e01 u 1⟩ ⟨e10 u' 1, e01 u' 1⟩).2
    simp only [e00, e11, hnorm, Units.val_one] at h
    refine h.trans ⟨?_, ?_⟩
    · rintro ⟨ζ, hζ, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
      · left
        rw [mul_one] at h2
        rw [h1, ← h2, one_mul]
      · right
        rw [mul_one] at h1
        rw [h1]
        exact eq_inv_of_mul_eq_one_left h2.symm
    · rintro (h1 | h1)
      · exact ⟨1, one_ne_zero, Or.inl ⟨by rw [h1, one_mul], by rw [mul_one]⟩⟩
      · exact ⟨(u : K)⁻¹, inv_ne_zero u.ne_zero, Or.inr ⟨by rw [h1, mul_one], by rw [inv_mul_cancel₀ u.ne_zero]⟩⟩

  have hufex : ∀ γ : GL (Fin 2) K, ∃ u : Kˣ, γ ∈ ΔKfin → ((u : K) ≠ 1 ∧ γ = diagUnits2 u 1 ∧ diagUnits2 u⁻¹ 1 ∈ ΔKfin) := by
    intro γ
    by_cases hγ : γ ∈ ΔKfin
    · obtain ⟨u, hu⟩ := hΔKinv γ hγ
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hγ⟩
  choose uf huf using hufex
  have huf1 : ∀ γ ∈ ΔKfin, ((uf γ : Kˣ) : K) ≠ 1 := fun γ hγ => (huf γ hγ).1
  have hγ_eq : ∀ γ ∈ ΔKfin, γ = diagUnits2 (uf γ) 1 := fun γ hγ => (huf γ hγ).2.1
  let bar : GL (Fin 2) K → GL (Fin 2) K := fun γ => diagUnits2 (uf γ)⁻¹ 1
  have hbar_mem : ∀ γ ∈ ΔKfin, bar γ ∈ ΔKfin := fun γ hγ => (huf γ hγ).2.2
  have hcls_bar : ∀ γ ∈ ΔKfin, cls (bar γ) = cls γ := by
    intro γ hγ
    have e := hγ_eq γ hγ
    have h : cls (diagUnits2 (uf γ)⁻¹ 1) = cls (diagUnits2 (uf γ) 1) :=
      (hclsU (uf γ) (uf γ)⁻¹).mpr (Or.inr (by rw [Units.val_inv_eq_inv_val]))
    rw [← e] at h
    exact h
  have hbar_bar : ∀ γ ∈ ΔKfin, bar (bar γ) = γ := by
    intro γ hγ
    have h1 := hγ_eq (bar γ) (hbar_mem γ hγ)
    have h2 : uf (bar γ) = (uf γ)⁻¹ := hinj1 _ _ h1.symm
    show diagUnits2 (uf (bar γ))⁻¹ 1 = γ
    rw [h2, inv_inv]
    exact (hγ_eq γ hγ).symm
  have hcls_mem : ∀ γ ∈ ΔKfin, ∀ γ' ∈ ΔKfin, cls γ' = cls γ → γ' = γ ∨ γ' = bar γ := by
    intro γ hγ γ' hγ' h
    rw [hγ_eq γ hγ, hγ_eq γ' hγ'] at h
    rcases (hclsU (uf γ) (uf γ')).mp h with h1 | h1
    · left
      exact (hγ_eq γ' hγ').trans ((congrArg (fun v : Kˣ => diagUnits2 v (1 : Kˣ)) (Units.ext h1)).trans
        (hγ_eq γ hγ).symm)
    · right
      exact (hγ_eq γ' hγ').trans (congrArg (fun v : Kˣ => diagUnits2 v (1 : Kˣ))
        (Units.ext (by rw [h1, Units.val_inv_eq_inv_val])))
  have hratγ : ∀ γ ∈ ΔKfin, Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) =
      ((uf γ : Kˣ) : K) := by
    intro γ hγ
    rw [hnorm]
    have e := hγ_eq γ hγ
    calc (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1
        = ((diagUnits2 (uf γ) 1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 /
            ((diagUnits2 (uf γ) 1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by rw [← e]
      _ = ((uf γ : Kˣ) : K) := hrat _
  have hbfix : ∀ γ ∈ ΔKfin, (bar γ = γ ↔ ((uf γ : Kˣ) : K) = -1) := by
    intro γ hγ
    constructor
    · intro h
      have h2 : (uf γ)⁻¹ = uf γ := hinj1 _ _ (h.trans (hγ_eq γ hγ))
      have h3' : uf γ * uf γ = 1 := by
        calc uf γ * uf γ = (uf γ)⁻¹ * uf γ := by rw [h2]
          _ = 1 := inv_mul_cancel _
      have h3 : ((uf γ : Kˣ) : K) * ((uf γ : Kˣ) : K) = 1 := by
        rw [← Units.val_mul, h3', Units.val_one]
      rcases mul_self_eq_one_iff.mp h3 with h4 | h4
      · exact absurd h4 (huf1 γ hγ)
      · exact h4
    · intro hu
      have h2 : (uf γ)⁻¹ = uf γ := Units.ext (by rw [Units.val_inv_eq_inv_val, hu, inv_neg, inv_one])
      show diagUnits2 (uf γ)⁻¹ 1 = γ
      rw [h2]
      exact (hγ_eq γ hγ).symm

  let SS : Set (Set (GL (Fin 2) K)) := {s | ∃ u : Kˣ, (u : K) ≠ 1 ∧ cls (diagUnits2 u 1) = s}
  have hSS : ∀ s : SS, ∃ u : Kˣ, (u : K) ≠ 1 ∧ cls (diagUnits2 u 1) = (s : Set (GL (Fin 2) K)) := fun s => s.2
  choose udef hudef using hSS
  let meets : Set (GL (Fin 2) K) → Prop := fun s => ∃ γ ∈ ΔKfin, cls γ = s

  have hTK := AutomorphicForm.forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
    K νZK cτK hcτK
  let τK' : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))) :=
    fun γ => if γ ∈ ΔKfin then τK γ else if h : good γ then (hTK γ h.1 h.2.1 h.2.2).choose else τK γ
  have hτK' : ∀ γ : GL (Fin 2) K, (τK' γ).IsHaarMeasure := by
    intro γ
    by_cases h1 : γ ∈ ΔKfin
    · simp only [τK', if_pos h1]
      exact hτK γ
    · by_cases h2 : good γ
      · simp only [τK', if_neg h1, dif_pos h2]
        exact (hTK γ h2.1 h2.2.1 h2.2.2).choose_spec.1
      · simp only [τK', if_neg h1, dif_neg h2]
        exact hτK γ
  have hτKc' : ∀ γ : GL (Fin 2) K, good γ → ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
          g (s : AdelicGL2 (𝓞 K) K) ∂(τK' γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK) := by
    intro γ hg g
    by_cases h1 : γ ∈ ΔKfin
    · simp only [τK', if_pos h1]
      exact hτKc γ h1 g
    · simp only [τK', if_neg h1, dif_pos hg]
      exact (hTK γ hg.1 hg.2.1 hg.2.2).choose_spec.2 g
  let IK' : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun γ z => if γ ∈ ΔKfin then IK γ z else 0
  let JK' : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun γ z => if γ ∈ ΔKfin then JK γ z else 0

  have hvan : ∀ s : SS, ¬ meets s → ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K),
      fam m (AutomorphicForm.centralScalar (𝓞 K) K z *
        (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 (udef s) 1) * x)) = 0 := by
    intro s hs z x
    have hmiss : ∀ γ ∈ ΔKfin, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠
        ((udef s : Kˣ) : K) := by
      intro γ hγ heq
      apply hs
      refine ⟨γ, hγ, ?_⟩
      have heq' : ((uf γ : Kˣ) : K) = ((udef s : Kˣ) : K) := by rw [← hratγ γ hγ, hnorm]; exact heq
      rw [hγ_eq γ hγ, Units.ext heq']
      exact (hudef s).2
    have hre : AutomorphicForm.centralScalar (𝓞 K) K z *
          (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 (udef s) 1) * x) =
        x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (udef s)) 1) * x := by
      rw [AutomorphicForm.globalPoints_diagUnits2_hw47]
      generalize (diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (udef s)) 1 :
          AdelicGL2 (𝓞 K) K) = d
      calc AutomorphicForm.centralScalar (𝓞 K) K z * (x⁻¹ * d * x)
          = (AutomorphicForm.centralScalar (𝓞 K) K z * x⁻¹) * d * x := by simp only [mul_assoc]
        _ = (x⁻¹ * AutomorphicForm.centralScalar (𝓞 K) K z) * d * x := by
            rw [AutomorphicForm.centralScalar_comm_hw47 K z x⁻¹]
        _ = x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z * d) * x := by simp only [mul_assoc]
    rw [hre]
    exact hΔKc (udef s) (hudef s).1 hmiss z x

  have run : ∀ pick : SS → GL (Fin 2) K,
      (∀ s : SS, good (pick s) ∧ cls (pick s) = (s : Set (GL (Fin 2) K))) →
      (∀ s : SS, pick s ∉ ΔKfin → pick s = diagUnits2 (udef s) 1 ∧ ¬ meets s) →
      (∀ γ ∈ ΔKfin, γ ∈ Set.range pick →
          Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z) νZK) ∧
      A = ∑ t ∈ ΔKfin.filter (fun t => t ∈ Set.range pick),
          2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z ∂νZK) := by
    intro pick hpick hdef
    have hgoodR : ∀ γ ∈ Set.range pick, good γ := by
      rintro _ ⟨s, rfl⟩
      exact (hpick s).1
    have hd : ∀ t ∈ Set.range pick, (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1 := by
      intro t ht
      obtain ⟨h1, h2, h3⟩ := hgoodR t ht
      exact ⟨h1, h2, by rw [hnorm]; exact h3⟩
    have hdisj : ∀ t ∈ Set.range pick, ∀ t' ∈ Set.range pick, t ≠ t' → Disjoint (cls t) (cls t') := by
      rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩ hne
      have hss : (s : Set (GL (Fin 2) K)) ≠ s' := fun h => hne (by rw [Subtype.ext h])
      rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
      intro hne'
      have h := ((hdis29 (pick s') (pick s) ⟨(hpick s').1.1, (hpick s').1.2.1⟩
        ⟨(hpick s).1.1, (hpick s).1.2.1⟩).1).mp hne'
      exact hss (by rw [← (hpick s).2, ← (hpick s').2]; exact h)
    have hcov : {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgenK (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ} ⊆
        ⋃ t ∈ Set.range pick, cls t := by
      intro δ hδ
      obtain ⟨t, ⟨ht10, ht01⟩, htN, ht⟩ := hcov29 δ hδ
      have hdet : ((t : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := (t.isUnit.map Matrix.detMonoidHom).ne_zero
      rw [Matrix.det_fin_two, ht10, mul_zero, sub_zero] at hdet
      have h00 : (t : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
      have h11 : (t : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
      rw [hnorm] at htN
      let u : Kˣ := Units.mk0 ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) (div_ne_zero h00 h11)
      have hu1 : (u : K) ≠ 1 := htN
      have hct : cls (diagUnits2 u 1) = cls t := by
        refine ((hdis29 t (diagUnits2 u 1) ⟨ht10, ht01⟩ ⟨e10 u 1, e01 u 1⟩).2).mpr
          ⟨((t : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹, inv_ne_zero h11, Or.inl ⟨?_, ?_⟩⟩
        · rw [hnorm, hnorm, hnorm, e00]
          show (t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1 = _
          rw [div_eq_mul_inv, mul_comm]
        · rw [hnorm, hnorm, hnorm, e11, Units.val_one]
          exact (inv_mul_cancel₀ h11).symm
      have hs : cls (diagUnits2 u 1) ∈ SS := ⟨u, hu1, rfl⟩
      refine Set.mem_iUnion₂.mpr ⟨pick ⟨_, hs⟩, ⟨⟨_, hs⟩, rfl⟩, ?_⟩
      show δ ∈ cls (pick ⟨_, hs⟩)
      rw [(hpick ⟨_, hs⟩).2]
      show δ ∈ cls (diagUnits2 u 1)
      rw [hct]
      exact ht
    have hIK' : ∀ γ ∈ Set.range pick, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK' γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK' γ z) := by
      rintro _ ⟨s, rfl⟩ z
      by_cases h1 : pick s ∈ ΔKfin
      · simp only [τK', IK', if_pos h1]
        exact hIK (pick s) h1 z
      · obtain ⟨hps, hns⟩ := hdef s h1
        simp only [IK', if_neg h1]
        rw [hps]
        exact ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero,
          fun x hx => absurd (hvan s hns z x) hx⟩, by simp⟩
    have hJK' : ∀ γ ∈ Set.range pick, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
            -Real.log (NumberField.AdelicHeight.adelicHeight K x)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK' γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (JK' γ z) := by
      rintro _ ⟨s, rfl⟩ z
      by_cases h1 : pick s ∈ ΔKfin
      · simp only [τK', JK', if_pos h1]
        exact hJK (pick s) h1 z
      · obtain ⟨hps, hns⟩ := hdef s h1
        simp only [JK', if_neg h1]
        rw [hps]
        exact ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero,
          fun x hx => absurd (hvan s hns z x) hx⟩, by simp [hvan s hns z]⟩
    obtain ⟨Δf, hΔf, hall⟩ :=
      AutomorphicForm.exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
        K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen hdeg SK SL hSL hSsat hS ξL hξc hξt hξσ N hN tysL φa φS faK fSK X hXc hX
        ΦK hΦKs hΦK νZK ΩK hΩK Ξ hΞ N' hN' tysK c₀ hgeo
        T hTdisj hT2 hTSL ws w' hw' ϖs hϖirr hϖs0 ns rTs hrTs zs hzs ϖKs hϖKirr hϖKs0 nKs rKs hrKs zKs hzKs
        ks js φL hφL hφLc φf hSLF hbi harch fam hfam hmatch ξK hξK m hm A B R₀ hSPK
        DK hgenK HK hHKc hHK μHK Λ₀K hΛ₀K κ₀K hκ₀Kpos ΩK' hΩK' hκ₀K hκ₀K'
        (Set.range pick) hd hdisj hcov cHK hcHK hHKμ cτK hcτK τK' hτK' (fun γ hγ => hτKc' γ (hgoodR γ hγ))
        IK' JK' hIK' hJK'
    have hFsub : (↑(Δf ∪ ΔKfin.filter (fun t => t ∈ Set.range pick)) : Set (GL (Fin 2) K)) ⊆ Set.range pick := by
      intro t ht
      rcases Finset.mem_union.mp (Finset.mem_coe.mp ht) with h | h
      · exact hΔf (Finset.mem_coe.mpr h)
      · exact (Finset.mem_filter.mp h).2
    obtain ⟨hint, -, hA, -⟩ := hall (Δf ∪ ΔKfin.filter (fun t => t ∈ Set.range pick)) Finset.subset_union_left hFsub
    refine ⟨?_, ?_⟩
    · intro γ hγ hγr
      have h := hint γ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hγr⟩))
      simp only [IK', if_pos hγ] at h
      exact h
    · rw [hA]
      have hzero : ∀ t ∈ Δf ∪ ΔKfin.filter (fun t => t ∈ Set.range pick), t ∉ ΔKfin.filter (fun t => t ∈ Set.range pick) →
          2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK' t z ∂νZK) = 0 := by
        intro t ht htF
        have htn : t ∉ ΔKfin := fun h => htF (Finset.mem_filter.mpr ⟨h, hFsub (Finset.mem_coe.mpr ht)⟩)
        simp only [IK', if_neg htn, mul_zero, integral_zero]
      rw [← Finset.sum_subset Finset.subset_union_right hzero]
      refine Finset.sum_congr rfl fun t ht => ?_
      have htm : t ∈ ΔKfin := (Finset.mem_filter.mp ht).1
      simp only [IK', if_pos htm]

  let pick₁ : SS → GL (Fin 2) K := fun s => if h : meets s then h.choose else diagUnits2 (udef s) 1
  let pick₂ : SS → GL (Fin 2) K := fun s => if h : meets s then bar h.choose else diagUnits2 (udef s) 1
  have hpick₁ : ∀ s : SS, good (pick₁ s) ∧ cls (pick₁ s) = (s : Set (GL (Fin 2) K)) := by
    intro s
    by_cases h : meets s
    · simp only [pick₁, dif_pos h]
      exact ⟨hgoodΔ _ h.choose_spec.1, h.choose_spec.2⟩
    · simp only [pick₁, dif_neg h]
      exact ⟨hgoodU _ (hudef s).1, (hudef s).2⟩
  have hdef₁ : ∀ s : SS, pick₁ s ∉ ΔKfin → pick₁ s = diagUnits2 (udef s) 1 ∧ ¬ meets s := by
    intro s hn
    by_cases h : meets s
    · simp only [pick₁, dif_pos h] at hn
      exact absurd h.choose_spec.1 hn
    · refine ⟨?_, h⟩
      simp only [pick₁, dif_neg h]
  have hpick₂ : ∀ s : SS, good (pick₂ s) ∧ cls (pick₂ s) = (s : Set (GL (Fin 2) K)) := by
    intro s
    by_cases h : meets s
    · simp only [pick₂, dif_pos h]
      exact ⟨hgoodΔ _ (hbar_mem _ h.choose_spec.1), (hcls_bar _ h.choose_spec.1).trans h.choose_spec.2⟩
    · simp only [pick₂, dif_neg h]
      exact ⟨hgoodU _ (hudef s).1, (hudef s).2⟩
  have hdef₂ : ∀ s : SS, pick₂ s ∉ ΔKfin → pick₂ s = diagUnits2 (udef s) 1 ∧ ¬ meets s := by
    intro s hn
    by_cases h : meets s
    · simp only [pick₂, dif_pos h] at hn
      exact absurd (hbar_mem _ h.choose_spec.1) hn
    · refine ⟨?_, h⟩
      simp only [pick₂, dif_neg h]
  obtain ⟨hint₁, hA₁⟩ := run pick₁ hpick₁ hdef₁
  obtain ⟨hint₂, hA₂⟩ := run pick₂ hpick₂ hdef₂

  have hSSγ : ∀ γ ∈ ΔKfin, cls γ ∈ SS := fun γ hγ =>
    ⟨uf γ, huf1 γ hγ, by rw [← hγ_eq γ hγ]⟩
  have hmem_range : ∀ (pick : SS → GL (Fin 2) K),
      (∀ s : SS, good (pick s) ∧ cls (pick s) = (s : Set (GL (Fin 2) K))) →
      ∀ (γ : GL (Fin 2) K) (hγ : γ ∈ ΔKfin), (γ ∈ Set.range pick ↔ pick ⟨cls γ, hSSγ γ hγ⟩ = γ) := by
    intro pick hpick γ hγ
    constructor
    · rintro ⟨s, hs⟩
      have hs' : s = ⟨cls γ, hSSγ γ hγ⟩ := Subtype.ext (by rw [← (hpick s).2, hs])
      rw [← hs']
      exact hs
    · intro h
      exact ⟨_, h⟩
  have key : ∀ γ ∈ ΔKfin,
      ((if γ ∈ Set.range pick₁ then
          2 * ((κ₀K : ℂ) * (if Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK)
        else 0) +
       (if γ ∈ Set.range pick₂ then
          2 * ((κ₀K : ℂ) * (if Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK)
        else 0)) =
      2 * ((κ₀K : ℂ) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK)) ∧
      (γ ∈ Set.range pick₁ ∨ γ ∈ Set.range pick₂) := by
    intro γ hγ
    have hm : meets (cls γ) := ⟨γ, hγ, rfl⟩
    have hγ₁ : hm.choose ∈ ΔKfin ∧ cls hm.choose = cls γ := hm.choose_spec
    have hp1 : pick₁ ⟨cls γ, hSSγ γ hγ⟩ = hm.choose := by simp only [pick₁, dif_pos hm]
    have hp2 : pick₂ ⟨cls γ, hSSγ γ hγ⟩ = bar hm.choose := by simp only [pick₂, dif_pos hm]
    have m1 : γ ∈ Set.range pick₁ ↔ hm.choose = γ := by rw [hmem_range pick₁ hpick₁ γ hγ, hp1]
    have m2 : γ ∈ Set.range pick₂ ↔ bar hm.choose = γ := by rw [hmem_range pick₂ hpick₂ γ hγ, hp2]
    rw [hratγ γ hγ]
    rcases hcls_mem γ hγ hm.choose hγ₁.1 hγ₁.2 with h | h
    ·
      have in1 : γ ∈ Set.range pick₁ := m1.mpr h
      by_cases hu : ((uf γ : Kˣ) : K) = -1
      · have in2 : γ ∈ Set.range pick₂ := m2.mpr (by rw [h]; exact (hbfix γ hγ).mpr hu)
        refine ⟨?_, Or.inl in1⟩
        rw [if_pos in1, if_pos in2, if_pos hu]
        ring
      · have out2 : γ ∉ Set.range pick₂ := fun h2 => hu ((hbfix γ hγ).mp (by have e2 := m2.mp h2; rw [h] at e2; exact e2))
        refine ⟨?_, Or.inl in1⟩
        rw [if_pos in1, if_neg out2, if_neg hu]
        ring
    ·
      have in2 : γ ∈ Set.range pick₂ := m2.mpr (by rw [h]; exact hbar_bar γ hγ)
      by_cases hu : ((uf γ : Kˣ) : K) = -1
      · have in1 : γ ∈ Set.range pick₁ := m1.mpr (by rw [h]; exact (hbfix γ hγ).mpr hu)
        refine ⟨?_, Or.inr in2⟩
        rw [if_pos in1, if_pos in2, if_pos hu]
        ring
      · have out1 : γ ∉ Set.range pick₁ := fun h1 => hu ((hbfix γ hγ).mp (by have e1 := m1.mp h1; rw [h] at e1; exact e1))
        refine ⟨?_, Or.inr in2⟩
        rw [if_neg out1, if_pos in2, if_neg hu]
        ring

  refine ⟨fun γ hγ => ?_, ?_⟩
  · rcases (key γ hγ).2 with h | h
    · exact hint₁ γ hγ h
    · exact hint₂ γ hγ h
  · have e1 : (∑ t ∈ ΔKfin.filter (fun t => t ∈ Set.range pick₁),
          2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z ∂νZK)) + (∑ t ∈ ΔKfin.filter (fun t => t ∈ Set.range pick₂),
          2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z ∂νZK)) = 2 * ∑ γ ∈ ΔKfin, (κ₀K : ℂ) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK) := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun γ hγ => (key γ hγ).1)
    have e2 : (2 : ℂ) * A = 2 * ∑ γ ∈ ΔKfin, (κ₀K : ℂ) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK) := by
      rw [← e1, two_mul, ← hA₁, ← hA₂]
    exact mul_left_cancel₀ two_ne_zero e2

end S_AutomorphicForm_slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine
end P2MW
export P2MW.S_AutomorphicForm_slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine (solution)
