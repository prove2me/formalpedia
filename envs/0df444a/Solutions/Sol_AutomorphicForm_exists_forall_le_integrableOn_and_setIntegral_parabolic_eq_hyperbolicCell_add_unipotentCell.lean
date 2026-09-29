-- Prove2me | solution 1 for AutomorphicForm.exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6e652c7c-c257-5f76-898c-bb7f51ad1186

import Theorems.Thm_AutomorphicForm_exists_forall_le_lambdaT_adelicKernel_eq_centralElliptic_add_unipotentCell_add_hyperbolicCell
import Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_hyperbolicCell_and_unipotentCell_sub_indicator_constantTerm
import Theorems.Thm_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.gl2Weyl_val AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
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
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
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
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
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
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => AutomorphicForm.adelicKernel K f x y))
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
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
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) +
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  obtain ⟨hfcont, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hff
  obtain ⟨R₁, hI⟩ :=
    AutomorphicForm.exists_forall_le_integrableOn_hyperbolicCell_and_unipotentCell_sub_indicator_constantTerm
      K α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξ hξc hξt f hff
  obtain ⟨R₂, hP⟩ := AutomorphicForm.exists_forall_le_lambdaT_adelicKernel_eq_centralElliptic_add_unipotentCell_add_hyperbolicCell K ΦK f hfcont hfcs
  refine ⟨max R₁ R₂, fun R hR => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hI R (le_trans (le_max_left _ _) hR)
  refine ⟨h1, h2, h3, h4, ?_⟩

  have hpt : ∀ (x : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ),
      ((AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => AutomorphicForm.adelicKernel K f x y))
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) =
      (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
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
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) +
      (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) := by
    intro x z
    have hK := AutomorphicForm.adelicKernel_eq_four_parts_of_localFiniteness K (AutomorphicForm.adelicKernelLocalFiniteness K) hfcs (subset_tsupport f) x (AutomorphicForm.centralScalar (𝓞 K) K z * x)
    have hE' := hP R (le_trans (le_max_right _ _) hR) x z
    unfold AutomorphicForm.lambdaT at hE'
    beta_reduce at hE'
    rw [hK] at hE'
    linear_combination hE'
  have hcongr : (fun x : AdelicGL2 (𝓞 K) K => ∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => AutomorphicForm.adelicKernel K f x y))
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) =
      fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
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
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) + (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) := by
    funext x
    rw [← integral_add (h1 x) (h3 x)]
    congr 1
    funext z
    rw [hpt x z, mul_add]
  show (∫ x in AutomorphicForm.canonicalTruncationDomain K α β, (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => AutomorphicForm.adelicKernel K f x y))
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = _
  rw [hcongr, integral_add h2 h4]

end S_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell (solution)
