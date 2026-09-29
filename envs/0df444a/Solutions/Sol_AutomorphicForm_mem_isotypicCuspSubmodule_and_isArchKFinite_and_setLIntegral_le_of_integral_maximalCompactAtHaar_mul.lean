-- Prove2me | solution 1 for AutomorphicForm.mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7257a10c-33c8-5cd5-b704-ed0e7f407317

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_isArchKFinite_integral_maximalCompactAtHaar_mul_of_translatesSpanFinite
import Theorems.Thm_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem Ws23B.continuous_of_mem (K : Type) [Field K] [NumberField K] (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : f ∈ isotypicCuspSubmodule K pins ξ N S Ψ) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx.continuous
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact continuous_const.mul hx

theorem Ws23B.left_invariant_of_mem (K : Type) [Field K] [NumberField K] (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : f ∈ isotypicCuspSubmodule K pins ξ N S Ψ) :
    ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * x) = f x := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    intro γ g
    letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := pins.mS
    letI : MeasureSpace (AdelicGL2 (𝓞 K) K) := ⟨pins.μ⟩
    have h : IsAutomorphicFnAt K pins ξ x := hx.smoothCusp.1.1
    unfold IsAutomorphicFnAt LsXiMemberAt at h
    exact h.left_invariant γ g
  | zero => exact fun _ _ => rfl
  | add x y _ _ hx hy => exact fun γ g => by simp only [Pi.add_apply, hx, hy]
  | smul c x _ hx => exact fun γ g => by simp only [Pi.smul_apply, hx]

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (ξ : (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ) (hκ0 : ∀ k, 0 ≤ κ k) (hκ1 : ∫ k, κ k ∂(maximalCompactAtHaar K ∅) = 1)
    (hκfin : ∃ s : Finset (↥(maximalCompactAt K ∅) → ℝ), ∀ a : ↥(maximalCompactAt K ∅),
      (fun k => κ (a * k)) ∈ Submodule.span ℝ (s : Set (↥(maximalCompactAt K ∅) → ℝ)))
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : f ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ) :
    (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ ∧
    IsArchKFinite K (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) ∧
    ∫⁻ x in Φ₀, (‖∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ∫⁻ x in Φ₀, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  ⟨AutomorphicForm.integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule K α β Φ₀ hΦ₀ hΦ₀s ξ N S Ψ κ hκc hκ0 hκ1 f hf,
   AutomorphicForm.isArchKFinite_integral_maximalCompactAtHaar_mul_of_translatesSpanFinite K κ hκc hκfin f
     (Ws23B.continuous_of_mem K _ ξ N S Ψ f hf),
   AutomorphicForm.setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain K α β Φ₀ hΦ₀ hΦ₀s κ
     hκc hκ0 hκ1 f (Ws23B.continuous_of_mem K _ ξ N S Ψ f hf) (Ws23B.left_invariant_of_mem K _ ξ N S Ψ f hf)⟩

end S_AutomorphicForm_mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul
end P2MW
export P2MW.S_AutomorphicForm_mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul (solution)
