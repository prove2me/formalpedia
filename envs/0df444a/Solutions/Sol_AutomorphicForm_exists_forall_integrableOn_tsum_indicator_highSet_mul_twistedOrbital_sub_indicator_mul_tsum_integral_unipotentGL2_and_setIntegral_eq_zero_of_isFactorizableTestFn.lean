-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integrableOn_tsum_indicator_highSet_mul_twistedOrbital_sub_indicator_mul_tsum_integral_unipotentGL2_and_setIntegral_eq_zero_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b6ecb610-5e80-5d11-a172-5a731f0c87fe

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
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero
import Theorems.Thm_AutomorphicForm_exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit
import Theorems.Thm_AutomorphicForm_setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integrableOn_tsum_indicator_highSet_mul_twistedOrbital_sub_indicator_mul_tsum_integral_unipotentGL2_and_setIntegral_eq_zero_of_isFactorizableTestFn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
attribute [local instance] NumberField.AdelicHaar.adeleBorel in
open scoped TensorProduct.RightActions Classical in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Λ' : Subgroup (GL (Fin 2) L))
    (hΛ' : ∀ a : GL (Fin 2) L, a ∈ Λ' ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    {κ : Type} [Countable κ] (ra : κ → GL (Fin 2) L)
    (hrad : ∀ j, ((ra j : Matrix (Fin 2) (Fin 2) L)) 1 0 = 0 ∧ ((ra j : Matrix (Fin 2) (Fin 2) L)) 0 1 = 0)
    (hra : ∀ a : GL (Fin 2) L, ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → ∃! j, (ra j)⁻¹ * a ∈ Λ')
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
        (∑' i,
          (Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
             + Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
        - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L))))) Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      ∫ x in Φ₀,
        ((∑' i,
          (Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
             + Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
        - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L))))) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by
  classical

  obtain ⟨hφc, hφs⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hφ

  obtain ⟨R₀, hR₀⟩ :=
    AutomorphicForm.exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit
      K L νZL ΩL hΩL D σ hgen ξL hξc hξt c u d₁ d₂ hc Tc hTc δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr φ hφc hφs

  obtain ⟨-, -, R₁, hR₁⟩ :=
    AutomorphicForm.exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero
      K L α β hα hαβ Φ₀ νZL ΩL hΩL D σ hgen ξL hξc hξt c u d₁ d₂ hc Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ δ₀ hδ₀u hδ₀l hreg I hI φ hφ
  refine ⟨max R₀ R₁, fun R hR => ?_⟩
  obtain ⟨hPint, hP0⟩ := hR₁ R (le_of_max_le_right hR)

  have hae : ∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀), x ∈ Φ₀ := by
    rw [← Measure.restrict_restrict_of_subset (μ := (adelicGLHaar (Fin 2) (𝓞 L) L)) hΦ₀s]
    exact ae_restrict_mem₀ hΦ₀.nullMeasurableSet

  have hcen : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
      NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.centralScalar (𝓞 L) L z * g) =
        NumberField.AdelicHeight.adelicHeight L g :=
    (NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul L).2

  have hEq : (fun x : AdelicGL2 (𝓞 L) L =>
        Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x * ((∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) - (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * @AutomorphicForm.constantTerm _ (productionPinsOf L Φ₀ (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _ (productionPinsOf L Φ₀ (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t) (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)) (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL))) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀]
      (fun x : AdelicGL2 (𝓞 L) L =>
        (∑' i, (Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) + Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)} (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) * ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x * ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1 then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) * ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) + (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L))))) := by
    filter_upwards [hae] with x hx
    beta_reduce
    have hxS : x ∈ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂ := hΦ₀S hx

    have hS := (hR₀ R (le_of_max_le_left hR) x hxS).2

    have hC := (AutomorphicForm.setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
      K L νZL ΩL hΩL D σ hgen ξL hξc hξt δ₀ hδ₀u hδ₀l hreg I hI Λ hΛ r hr Φ₀ Λ' hΛ' ra hrad hra φ hφc hφs x R).2.2.2

    have hInd : (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)) (@AutomorphicForm.constantTerm _ (productionPinsOf L Φ₀ (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _ (productionPinsOf L Φ₀ (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t) (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))) (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL) =
        Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x * (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * @AutomorphicForm.constantTerm _ (productionPinsOf L Φ₀ (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _ (productionPinsOf L Φ₀ (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t) (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)) (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL) := by
      by_cases hRx : Real.exp R < NumberField.AdelicHeight.adelicHeight L x
      · have h1 : Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x = 1 :=
          Set.indicator_of_mem (show x ∈ {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} from hRx) _
        rw [h1, one_mul]
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        exact congrArg (fun t : ℂ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * t)
          (Set.indicator_of_mem
            (show AutomorphicForm.centralScalar (𝓞 L) L z * x ∈
                AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) from by
              rw [AutomorphicForm.mem_highSet_iff, hcen]; exact hRx) _)
      · have h1 : Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x = 0 :=
          Set.indicator_of_notMem (show x ∉ {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} from hRx) _
        rw [h1, zero_mul]
        refine setIntegral_eq_zero_of_forall_eq_zero ?_
        intro z _
        rw [Set.indicator_of_notMem
          (show AutomorphicForm.centralScalar (𝓞 L) L z * x ∉
              AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) from by
            rw [AutomorphicForm.mem_highSet_iff, hcen]; exact hRx), mul_zero]
    rw [hS, ← hC, hInd, mul_sub]
    try rfl

  refine ⟨hPint.congr_fun_ae hEq, ?_⟩
  rw [← integral_congr_ae hEq]
  exact hP0

end S_AutomorphicForm_exists_forall_integrableOn_tsum_indicator_highSet_mul_twistedOrbital_sub_indicator_mul_tsum_integral_unipotentGL2_and_setIntegral_eq_zero_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integrableOn_tsum_indicator_highSet_mul_twistedOrbital_sub_indicator_mul_tsum_integral_unipotentGL2_and_setIntegral_eq_zero_of_isFactorizableTestFn (solution)
