-- Prove2me | solution 1 for AutomorphicForm.integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ef9735c8-f9f3-5990-9eb2-5c4a105f184c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_integral_haarQuotient_integral_character_mul_twistedOrbital_eq_integral_quotient_ker_idelicNorm_character_mul_integral_haarQuotient_integral
import Theorems.Thm_AutomorphicForm_const_mul_eq_integral_haarQuotient_integral_ker_idelicNorm_centralScalar_of_isTwistedOrbitalIntegralOn_comp_baseChangeGL
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
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)

    (cμ : ℝ) (hcμ : 0 < cμ)
    (hμc : ∀ F : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂μ = cμ * ∫ g, F g ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (cH : ℝ) (hcH : 0 < cH)
    (hHc : ∀ g : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ h : H, g (h : AdelicGL2 (𝓞 L) L) ∂μH =
        cH * ∫ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 L) L p.1 *
            AutomorphicForm.baseChangeGL K L
              (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1))) ∂(νZL.prod νK))
    (cτ : ℝ) (hcτ : 0 < cτ)
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK)) :
    ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
    ∀ (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t →
    ∀ (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ →
      (∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
            g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
          cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK)) →
    ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ), Continuous φ → HasCompactSupport φ →

    (∀ (I : (AdeleRing (𝓞 L) L)ˣ → ℂ),
      (∀ w : (AdeleRing (𝓞 L) L)ˣ,
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
          ((fun g : AdelicGL2 (𝓞 L) L => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
            AutomorphicForm.baseChangeGL K L) (I w)) →
      Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
            (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) →
      Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * I wq.out)
        (HaarQuotient.measure νZL N1 μN) ∧
      ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) =
        ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * I wq.out
          ∂(HaarQuotient.measure νZL N1 μN)) ∧

    (∀ (J : (AdeleRing (𝓞 L) L)ˣ → ℂ),
      (∀ w : (AdeleRing (𝓞 L) L)ˣ,
        AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ
          (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
            -Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.baseChangeGL K L x))
              - Real.log (NumberField.AdelicHeight.adelicHeight L
                  (AutomorphicForm.adelicWeyl (𝓞 L) L * AutomorphicForm.baseChangeGL K L x)))
          δ τ
          ((fun g : AdelicGL2 (𝓞 L) L => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
            AutomorphicForm.baseChangeGL K L) (J w)) →
      Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) →
      Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * J wq.out)
        (HaarQuotient.measure νZL N1 μN) ∧
      ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) =
        ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * J wq.out
          ∂(HaarQuotient.measure νZL N1 μN)) := by
  intro t ht₁ ht₂ hreg δ hδ τ hτ hτc φ hφc hφs
  have hHcl : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)) := by assumption
  obtain ⟨hC1, hC1w⟩ :=
    AutomorphicForm.integral_haarQuotient_integral_character_mul_twistedOrbital_eq_integral_quotient_ker_idelicNorm_character_mul_integral_haarQuotient_integral
      K L νZL D σ hgen ξL hξc hξσ H hHcl hH μH N1 hN1c hN1 μN t ht₁ ht₂ hreg φ hφc hφs
  obtain ⟨hC2, hC2w⟩ :=
    AutomorphicForm.const_mul_eq_integral_haarQuotient_integral_ker_idelicNorm_centralScalar_of_isTwistedOrbitalIntegralOn_comp_baseChangeGL
      K L νZL D σ hgen H hHcl hH μH μ hμ cμ hcμ hμc νK cH hcH hHc cτ hcτ AK hAKc hAK μAK hμAK N1 hN1c hN1 μN
      cN hcN hNc t ht₁ ht₂ hreg δ hδ τ hτ hτc φ hφc hφs
  have hκ : ((cN * cτ / (cH * cμ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < cN * cτ / (cH * cμ) := by positivity
    exact_mod_cast this.ne'
  refine ⟨fun I hI hint => ?_, fun J hJ hint => ?_⟩
  · obtain ⟨hi, he⟩ := hC1 hint
    have hpt : ∀ w : (AdeleRing (𝓞 L) L)ˣ,
        ((ξL ⟨w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * I w =
          (((cN * cτ / (cH * cμ) : ℝ) : ℂ))⁻¹ * (((ξL ⟨w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH))) := by
      intro w
      rw [← hC2 w (I w) (hI w), ← mul_assoc, ← mul_assoc, mul_comm _ (((cN * cτ / (cH * cμ) : ℝ) : ℂ)), ← mul_assoc,
        mul_inv_cancel₀ hκ, one_mul]
    refine ⟨?_, ?_⟩
    · simp_rw [hpt]
      exact hi.const_mul _
    · simp_rw [hpt]
      rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hκ, one_mul]
      exact he
  · obtain ⟨hi, he⟩ := hC1w hint
    have hpt : ∀ w : (AdeleRing (𝓞 L) L)ˣ,
        ((ξL ⟨w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * J w =
          (((cN * cτ / (cH * cμ) : ℝ) : ℂ))⁻¹ * (((ξL ⟨w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) *
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH))) := by
      intro w
      rw [← hC2w w (J w) (hJ w), ← mul_assoc, ← mul_assoc, mul_comm _ (((cN * cτ / (cH * cμ) : ℝ) : ℂ)), ← mul_assoc,
        mul_inv_cancel₀ hκ, one_mul]
    refine ⟨?_, ?_⟩
    · simp_rw [hpt]
      exact hi.const_mul _
    · simp_rw [hpt]
      rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hκ, one_mul]
      exact he

end S_AutomorphicForm_integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn
end P2MW
export P2MW.S_AutomorphicForm_integral_haarQuotient_twistedOrbital_eq_const_mul_integral_quotient_ker_idelicNorm_of_isTwistedOrbitalIntegralOn (solution)
