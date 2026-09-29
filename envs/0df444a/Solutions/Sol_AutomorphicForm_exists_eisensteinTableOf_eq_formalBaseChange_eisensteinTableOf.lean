-- Prove2me | solution 1 for AutomorphicForm.exists_eisensteinTableOf_eq_formalBaseChange_eisensteinTableOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2b3dc28f-5041-57bd-bf91-c1d51026aa8d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_eisensteinTableOf_eq_formalBaseChange_eisensteinTableOf
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

namespace BcEis

theorem satakePow_add_mul {R : Type*} [CommRing R] (α β : R) :
    ∀ n : ℕ, satakePow n (α + β) (α * β) = α ^ n + β ^ n := by

  suffices h : ∀ n : ℕ, satakePow n (α + β) (α * β) = α ^ n + β ^ n ∧
      satakePow (n + 1) (α + β) (α * β) = α ^ (n + 1) + β ^ (n + 1) from fun n => (h n).1
  intro n
  induction n with
  | zero => exact ⟨by rw [satakePow_zero, pow_zero, pow_zero]; norm_num, by rw [satakePow_one, pow_one, pow_one]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, satakePow_add_two, ih.2, ih.1]
    ring

theorem mem_and_inv_mem_of_valued_eq_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) (h : Valued.v (t : v.adicCompletion K) = 1) :
    (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
  exact ⟨le_rfl, le_rfl⟩

theorem comp_idelicNorm_uniformizerIdele (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 L))
    (hχ : IsUnramifiedCharAt χ (w.under (𝓞 K))) :
    (χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) (uniformizerIdele L w) =
      χ (uniformizerIdele K (w.under (𝓞 K))) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal) := by
  obtain ⟨t, ht1, hN⟩ := M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit K L w
  rw [MonoidHom.comp_apply, hN, map_mul, map_pow]
  have hmem := mem_and_inv_mem_of_valued_eq_one (w.under (𝓞 K)) t ht1
  have h1 : χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K (w.under (𝓞 K)) t)) = 1 := hχ t hmem.1 hmem.2
  rw [h1, mul_one]

end BcEis

open BcEis in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (h1c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ))
    (h1t : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ₁ z = 1)
    (h2c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ))
    (h2t : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ₂ z = 1)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) :
    ∃ (M' : Ideal (𝓞 L)) (hM' : M' ≠ ⊥) (χ₁' χ₂' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁' z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
          χ₁' z = 1) ∧
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂' z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
          χ₂' z = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        ((formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).a w,
          (formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).b w) =
        ((LanglandsTunnell.Converse.eisensteinTableOf L M' hM' χ₁' χ₂').a w,
          (LanglandsTunnell.Converse.eisensteinTableOf L M' hM' χ₁' χ₂').b w) := by
  classical
  set Nm := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hNm

  have hNc : Continuous (Nm : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ) :=
    Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange K L)

  have hNp : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        Nm z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range := by
    rintro z ⟨u, rfl⟩
    refine ⟨Units.map (Algebra.norm K : L →* K) u, Units.ext ?_⟩
    show algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K (u : L)) =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm (algebraMap L (AdeleRing (𝓞 L) L) (u : L))
    rw [M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap]
  refine ⟨⊤, top_ne_bot, χ₁.comp Nm, χ₂.comp Nm, h1c.comp hNc, fun z hz => h1t _ (hNp z hz), h2c.comp hNc,
    fun z hz => h2t _ (hNp z hz), fun w hw => ?_⟩

  have hv : HeightOneSpectrum.under (𝓞 K) w ∉ SK := fun h => hw (hSL w h)
  obtain ⟨hu1, hu2⟩ := hunr _ hv
  have e1 := comp_idelicNorm_uniformizerIdele K L χ₁ w hu1
  have e2 := comp_idelicNorm_uniformizerIdele K L χ₂ w hu2
  simp only [formalBaseChange_a, formalBaseChange_b, LanglandsTunnell.Converse.eisensteinTableOf, hNm.symm ▸ e1,
    hNm.symm ▸ e2, Units.val_pow_eq_pow_val, satakePow_add_mul, mul_pow]

end S_AutomorphicForm_exists_eisensteinTableOf_eq_formalBaseChange_eisensteinTableOf
end P2MW
export P2MW.S_AutomorphicForm_exists_eisensteinTableOf_eq_formalBaseChange_eisensteinTableOf (solution)
