-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/728a0146-396b-5646-9d79-3b41f917c3d5

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ φ)
    (hφc : Continuous φ) (hφ0 : φ ≠ 0) :
    ∃ σ : ℝ, HasModulus F ξ σ := by
  obtain ⟨⟨hleft, hcentral⟩, -⟩ := (isAutomorphicFnAt_fdPins_iff F D ξ φ).mp hφ
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, φ g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)

  let μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := ξ.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) ≃* _).symm.toMonoidHom
  have hμ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, μ z = ξ ⟨z, Subgroup.mem_top z⟩ := fun z => rfl

  have hquot : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ((μ z : ℂˣ) : ℂ) = φ (centralScalar (𝓞 F) F z * g₀) / φ g₀ := by
    intro z
    rw [hμ, eq_div_iff hg₀]
    exact (hcentral ⟨z, Subgroup.mem_top z⟩ g₀).symm

  have hcS : Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
    have hval : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
        ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
          = Matrix.diagonal fun _ => (z : AdeleRing (𝓞 F) F) :=
      fun z => NumberField.AdelicVolume.centralScalar_val z
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have : (fun z : (AdeleRing (𝓞 F) F)ˣ =>
          ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          = fun z : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal fun _ : Fin 2 => ((↑z : AdeleRing (𝓞 F) F)) := funext hval
      show Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
        ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      rw [this]
      exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
    · have : (fun z : (AdeleRing (𝓞 F) F)ˣ =>
          ((↑((centralScalar (𝓞 F) F z)⁻¹ : AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          = fun z : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal fun _ : Fin 2 => ((↑(z⁻¹) : AdeleRing (𝓞 F) F)) := by
        funext z
        rw [← map_inv, hval]
      rw [this]
      exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

  have hc1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ) := by
    have : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
        = fun z => φ (centralScalar (𝓞 F) F z * g₀) / φ g₀ := funext hquot
    rw [this]
    exact (hφc.comp (hcS.mul continuous_const)).div_const _
  have hcont : Continuous μ := by
    refine Units.continuous_iff.2 ⟨hc1, ?_⟩
    have : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((↑((μ z)⁻¹) : ℂ))) = (fun z => ((μ z : ℂˣ) : ℂ)) ∘ fun z => z⁻¹ := by
      funext z
      simp only [Function.comp_apply, map_inv]
    rw [this]
    exact hc1.comp continuous_inv

  have hclass : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ := by
    intro u
    have hglob : centralScalar (𝓞 F) F (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u)
        = globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
      refine Units.ext ?_
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [centralScalar, globalPoints, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map,
          Matrix.diagonal]
    have h := hcentral ⟨Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u, Subgroup.mem_top _⟩ g₀
    have h' : φ (centralScalar (𝓞 F) F (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u) * g₀) = φ g₀ := by
      rw [hglob, hleft]
    rw [h'] at h

    have hξ : ((ξ ⟨Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) u, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = 1 :=
      (mul_eq_right₀ hg₀).mp h.symm
    exact Units.ext (by rw [hμ]; exact hξ)
  obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F μ hclass hcont
  exact ⟨σ, fun z => by simpa [hμ] using hσ z⟩

end S_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous (solution)
