-- Prove2me | solution 1 for AutomorphicForm.continuous_uncurry_finsum_chiDet_mul_chiDet_inv_and_apply_globalPoints_mul_and_apply_centralScalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/18809372-d620-5c01-8917-ac01e53e8b1d

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

import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_uncurry_finsum_chiDet_mul_chiDet_inv_and_apply_globalPoints_mul_and_apply_centralScalar_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem KRES.continuous_finsum {ι X : Type*} [TopologicalSpace X] (S : Set ι) (c : ι → ℂ)
    (u : ι → X → ℂ) (hu : ∀ i ∈ S, Continuous (u i)) (hu0 : ∀ i x, u i x ≠ 0) :
    Continuous fun x => ∑ᶠ i ∈ S, c i * u i x := by
  classical
  have hsupp : ∀ x, Function.support (fun i => c i * u i x) = {i | c i ≠ 0} := fun x => by
    ext i
    simp only [Function.mem_support, ne_eq, mul_eq_zero, hu0 i x, or_false, Set.mem_setOf_eq]
  by_cases hfin : (S ∩ {i | c i ≠ 0}).Finite
  · have heq : ∀ x, (∑ᶠ i ∈ S, c i * u i x) = ∑ i ∈ hfin.toFinset, c i * u i x := by
      intro x
      apply finsum_mem_eq_sum_of_inter_support_eq
      rw [hsupp x, Set.Finite.coe_toFinset, Set.inter_assoc, Set.inter_self]
    have hfun : (fun x => ∑ᶠ i ∈ S, c i * u i x) = fun x => ∑ i ∈ hfin.toFinset, c i * u i x :=
      funext heq
    rw [hfun]
    refine continuous_finset_sum _ fun i hi => ?_
    have hiS : i ∈ S := ((Set.Finite.mem_toFinset hfin).1 hi).1
    exact continuous_const.mul (hu i hiS)
  · have heq : ∀ x, (∑ᶠ i ∈ S, c i * u i x) = 0 := by
      intro x
      rw [finsum_mem_def]
      apply finsum_of_infinite_support
      rw [Set.support_indicator, hsupp x]
      exact hfin
    have hfun : (fun x => ∑ᶠ i ∈ S, c i * u i x) = fun _ => 0 := funext heq
    rw [hfun]
    exact continuous_const

theorem solution
    (K : Type) [Field K] [NumberField K]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    (Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ p.1 * chiDet (𝓞 K) K χ⁻¹ p.2)) ∧
    (∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K),
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ (AutomorphicForm.globalPoints (𝓞 K) K γ * x) * chiDet (𝓞 K) K χ⁻¹ y)) =
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y))) ∧
    (∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K),
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ (AutomorphicForm.globalPoints (𝓞 K) K γ * y))) =
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y))) ∧
    (∀ (a : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ (AutomorphicForm.centralScalar (𝓞 K) K a * x) * chiDet (𝓞 K) K χ⁻¹ y)) =
      ((ξK ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) *
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y))) ∧
    (∀ (a : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ (AutomorphicForm.centralScalar (𝓞 K) K a * y))) =
      (((ξK ⟨a, Subgroup.mem_top a⟩)⁻¹ : ℂˣ) : ℂ) *
      (∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y))) := by

  have hIC : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) →
      IsIdeleClassChar (𝓞 K) K χ ∧ IsIdeleClassChar (𝓞 K) K χ⁻¹ := by
    intro χ h
    have h1 : IsIdeleClassChar (𝓞 K) K χ := fun u => h _ (MonoidHom.mem_range.2 ⟨u, rfl⟩)
    exact ⟨h1, fun u => by rw [MonoidHom.inv_apply, h1 u, inv_one]⟩

  have hsq : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, SquaresToXi (𝓞 K) K ⊤ ξK χ →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((χ a : ℂˣ) : ℂ) ^ 2 = ((ξK ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) := by
    intro χ h a
    have h' := congrArg Units.val (h ⟨a, Subgroup.mem_top a⟩)
    rw [Units.val_pow_eq_pow_val] at h'
    exact h'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    refine KRES.continuous_finsum _ _ _ (fun χ hχ => ?_) (fun χ p => mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    have hc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ) := hχ.2.2
    have hci : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ⁻¹ z : ℂˣ) : ℂ) := by
      simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      exact hc.inv₀ fun z => (χ z).ne_zero
    exact (hc.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_fst)).mul
      (hci.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_snd))
  · intro γ x y
    exact finsum_mem_congr rfl fun χ hχ => by
      rw [chiDet_globalPoints_mul K χ (hIC χ hχ.2.1).1 γ x]
  · intro γ x y
    exact finsum_mem_congr rfl fun χ hχ => by
      rw [chiDet_globalPoints_mul K χ⁻¹ (hIC χ hχ.2.1).2 γ y]
  · intro a x y
    rw [mul_finsum_mem]
    exact finsum_mem_congr rfl fun χ hχ => by
      rw [chiDet_centralScalar_mul K, hsq χ hχ.1 a]
      ring
  · intro a x y
    rw [mul_finsum_mem]
    exact finsum_mem_congr rfl fun χ hχ => by
      rw [chiDet_centralScalar_mul K, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_pow, hsq χ hχ.1 a,
        ← Units.val_inv_eq_inv_val]
      ring

end S_AutomorphicForm_continuous_uncurry_finsum_chiDet_mul_chiDet_inv_and_apply_globalPoints_mul_and_apply_centralScalar_mul
end P2MW
export P2MW.S_AutomorphicForm_continuous_uncurry_finsum_chiDet_mul_chiDet_inv_and_apply_globalPoints_mul_and_apply_centralScalar_mul (solution)
