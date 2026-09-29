-- Prove2me | solution 1 for AutomorphicForm.lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/59748fe3-1718-507b-b9de-21501de62449

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace K42P3B

open MeasureTheory Topology NumberField AutomorphicForm

theorem bridge {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] (μ : Measure X) (ν : Measure Z)
    (F : X → Z → ℂ) (hre : ∀ x z, 0 ≤ (F x z).re) (him : ∀ x z, (F x z).im = 0)
    (hin : ∀ x, Integrable (F x) ν) (hout : Integrable (fun x => ∫ z, F x z ∂ν) μ) :
    (∫⁻ x, (∫⁻ z, ENNReal.ofReal ‖F x z‖ ∂ν) ∂μ) = ENNReal.ofReal (∫ x, (∫ z, F x z ∂ν) ∂μ).re := by
  have hnorm : ∀ x z, ‖F x z‖ = (F x z).re := by
    intro x z
    have h : F x z = ((F x z).re : ℂ) := Complex.ext rfl (by simp [him x z])
    rw [h, Complex.norm_real, Real.norm_of_nonneg (hre x z), Complex.ofReal_re]
  have hre_int : ∀ x, ∫ z, (F x z).re ∂ν = (∫ z, F x z ∂ν).re := by
    intro x
    have h := integral_re (hin x)
    simp only [RCLike.re_to_complex] at h
    exact h
  have hin_re : ∀ x, Integrable (fun z => (F x z).re) ν := by
    intro x
    have h := (hin x).re
    simp only [RCLike.re_to_complex] at h
    exact h
  have hinner : ∀ x, (∫⁻ z, ENNReal.ofReal ‖F x z‖ ∂ν) = ENNReal.ofReal (∫ z, F x z ∂ν).re := by
    intro x
    simp_rw [hnorm x]
    rw [← ofReal_integral_eq_lintegral_ofReal (hin_re x) (ae_of_all _ (hre x)), hre_int]
  rw [lintegral_congr hinner]
  have hg0 : ∀ x, 0 ≤ (∫ z, F x z ∂ν).re := fun x => by
    rw [← hre_int]
    exact integral_nonneg (hre x)
  have hout_re : Integrable (fun x => (∫ z, F x z ∂ν).re) μ := by
    have h := hout.re
    simp only [RCLike.re_to_complex] at h
    exact h
  have hre_out : ∫ x, (∫ z, F x z ∂ν).re ∂μ = (∫ x, (∫ z, F x z ∂ν) ∂μ).re := by
    have h := integral_re hout
    simp only [RCLike.re_to_complex] at h
    exact h
  rw [← ofReal_integral_eq_lintegral_ofReal hout_re (ae_of_all _ hg0), hre_out]

theorem isClosedEmbedding_glScalar {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] : IsClosedEmbedding (Matrix.GeneralLinearGroup.scalar (Fin 2) : Rˣ → GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  have hsc : IsClosedEmbedding ((Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun m : Matrix (Fin 2) (Fin 2) R => m 0 0)
      (fun a => ?_) ?_ ?_
    · show (Matrix.scalar (Fin 2) a) 0 0 = a
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    · exact continuous_id.matrix_elem 0 0
    · show Continuous fun a : R => Matrix.scalar (Fin 2) a
      simp_rw [Matrix.scalar_apply]
      exact (continuous_pi fun _ => continuous_id).matrix_diagonal
  exact hsc.units_map

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

noncomputable def sigmaHomeo : AdelicGL2 (𝓞 L) L ≃ₜ AdelicGL2 (𝓞 L) L where
  toFun := sigmaAdelicAct K L D σ
  invFun := sigmaAdelicAct K L D σ⁻¹
  left_inv x := by
    show ((sigmaAdelicAct K L D σ⁻¹).comp (sigmaAdelicAct K L D σ)) x = x
    rw [← sigmaAdelicAct_mul, inv_mul_cancel, sigmaAdelicAct_one]
    rfl
  right_inv x := by
    show ((sigmaAdelicAct K L D σ).comp (sigmaAdelicAct K L D σ⁻¹)) x = x
    rw [← sigmaAdelicAct_mul, mul_inv_cancel, sigmaAdelicAct_one]
    rfl
  continuous_toFun := continuous_sigmaAdelicAct K L D σ
  continuous_invFun := continuous_sigmaAdelicAct K L D σ⁻¹

theorem isClosedEmbedding_centralScalar :
    IsClosedEmbedding (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) :=
  isClosedEmbedding_glScalar

omit [NumberField K] in

theorem integrable_inner [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (A B : AdelicGL2 (𝓞 L) L) :
    Integrable (fun z : (AdeleRing (𝓞 L) L)ˣ =>
      φ (A * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * B))) νZL := by
  have h1 : HasCompactSupport
      ((((φ ∘ ⇑(Homeomorph.mulLeft A)) ∘ ⇑(sigmaHomeo K L D σ)) ∘ ⇑(Homeomorph.mulRight B)) ∘
        ⇑(centralScalar (𝓞 L) L)) :=
    (((hφs.comp_homeomorph _).comp_homeomorph _).comp_homeomorph _).comp_isClosedEmbedding
      (isClosedEmbedding_centralScalar L)
  have h2 : Continuous
      ((((φ ∘ ⇑(Homeomorph.mulLeft A)) ∘ ⇑(sigmaHomeo K L D σ)) ∘ ⇑(Homeomorph.mulRight B)) ∘
        ⇑(centralScalar (𝓞 L) L)) :=
    (((hφc.comp (Homeomorph.continuous _)).comp (Homeomorph.continuous _)).comp
      (Homeomorph.continuous _)).comp (isClosedEmbedding_centralScalar L).continuous
  exact h2.integrable_of_hasCompactSupport h1

end K42P3B

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφ0 : ∀ g : AdelicGL2 (𝓞 L) L, 0 ≤ (φ g).re ∧ (φ g).im = 0)
    (hint : Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
          (∫ z, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) :
    (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
          (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) =
      ENNReal.ofReal
        (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ z, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)).re := by
  have hin : ∀ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
      Integrable (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))) νZL := fun q =>
    K42P3B.integrable_inner K L D σ νZL φ hφc hφs
      (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t) (q.out : AdelicGL2 (𝓞 L) L)
  have key := K42P3B.bridge (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) νZL
    (fun (q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) =>
      φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
        AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))))
    (fun q z => (hφ0 _).1) (fun q z => (hφ0 _).2) hin hint
  exact key

end S_AutomorphicForm_lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg
end P2MW
export P2MW.S_AutomorphicForm_lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg (solution)
