-- Prove2me | solution 1 for AutomorphicForm.exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/261c6668-6955-5e74-ba98-1c559165cad8

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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type)
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
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
      (ιP : Type)
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμP : ∀ i, IsUnitaryChar (𝓞 K) K (μP i)) (_hνP : ∀ i, IsUnitaryChar (𝓞 K) K (νP i))
      (_hμPic : ∀ i, IsIdeleClassChar (𝓞 K) K (μP i)) (_hνPic : ∀ i, IsIdeleClassChar (𝓞 K) K (νP i))
      (_hμPc : ∀ i, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μP i z : ℂˣ) : ℂ))
      (_hνPc : ∀ i, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((νP i z : ℂˣ) : ℂ))
      (_hμνP : ∀ (i : ιP) (z : (AdeleRing (𝓞 K) K)ˣ), μP i z * νP i z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hsec : ∀ i : ιP, ∃ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μP i) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (νP i) αm hαm ((t : ℂ) * Complex.I)) φ₀ ∧
        Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) ∧
        φ₀ ∈ archCutSubmodule K tysK ∧ φ₀ ≠ 0),
    ∃ (em : ιP → ιE) (τ : ιP → ℝ),
      ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹ := by
  intro αm hαm ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hpairs ιP μP νP _hμP _hνP _hμPic _hνPic _hμPc _hνPc _hμνP _hsec
  have key : ∀ i : ιP, ∃ (e : ιE) (τ : ℝ), μP i = μ e * NumberField.TateGlobal.normPowChar K τ ∧
      νP i = ν e * (NumberField.TateGlobal.normPowChar K τ)⁻¹ := by
    intro i
    obtain ⟨t, φ₀, hφ, hφc, hφK, hφlev, hφty, hφne⟩ := _hsec i
    obtain ⟨e, he⟩ := _hpairs (μP i) (νP i) (_hμP i) (_hνP i) (_hμPic i) (_hνPic i) (_hμPc i) (_hνPc i)
      (_hμνP i) t φ₀ hφ hφc hφK hφlev hφty hφne
    set χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μP i * (μ e)⁻¹ with hχdef
    have hχapp : ∀ z, χ z = μP i z * (μ e z)⁻¹ := fun z => rfl
    have hχu : IsUnitaryChar (𝓞 K) K χ := by
      intro z
      rw [hχapp, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, _hμP i z, _hμ e z, inv_one, mul_one]
    have hχc : Continuous χ := by
      have hc : Continuous fun z => ((χ z : ℂˣ) : ℂ) := by
        have hfun : (fun z => ((χ z : ℂˣ) : ℂ)) = fun z => ((μP i z : ℂˣ) : ℂ) * ((μ e z : ℂˣ) : ℂ)⁻¹ := by
          funext z; rw [hχapp, Units.val_mul, Units.val_inv_eq_inv_val]
        rw [hfun]
        exact (_hμPc i).mul ((_hμc e).inv₀ fun z => Units.ne_zero _)
      exact Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr hc
    have hχ1 : ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, χ z = 1 := by
      intro z hz
      rw [hχapp, ← (he z hz).1, mul_inv_cancel]
    obtain ⟨τ, hτ⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles K χ hχc hχu hχ1
    refine ⟨e, τ, ?_, ?_⟩
    · refine MonoidHom.ext fun z => ?_
      rw [MonoidHom.mul_apply, ← hτ, hχapp, mul_comm, inv_mul_cancel_right]
    · refine MonoidHom.ext fun z => ?_
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ← hτ, hχapp, mul_inv_rev, inv_inv]
      have h1 : μP i z * νP i z = μ e z * ν e z := by rw [_hμνP i z, _hμν e z]
      calc νP i z = (μP i z)⁻¹ * (μP i z * νP i z) := (inv_mul_cancel_left _ _).symm
        _ = (μP i z)⁻¹ * (μ e z * ν e z) := by rw [h1]
        _ = ν e z * (μ e z * (μP i z)⁻¹) := by ac_rfl
  choose em τ hem using key
  exact ⟨em, τ, hem⟩

end S_AutomorphicForm_exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection (solution)
