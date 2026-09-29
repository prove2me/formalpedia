-- Prove2me | solution 1 for AutomorphicForm.isTwistedOrbitalIntegralOn_comp_scalar_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f114379f-d120-550e-98e9-82f514fc2ab0

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isTwistedOrbitalIntegralOn_comp_scalar_mul_iff

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem B5A2.scalarGL_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (c : R) := rfl
  simp only [Units.val_mul, h]
  exact (Matrix.scalar_commute (c : R) (fun r' => mul_comm _ _) _).eq

theorem B5A2.integral_map_subgroupCast {G : Type*} [Group G] [TopologicalSpace G]
    (H₁ H₂ : Subgroup G) (e : H₂ = H₁) (τ : @Measure H₁ (borel H₁)) (w : G → ℝ) (x : G) :
    ∫ t : H₂, w ((t : G) * x) ∂(@Measure.map H₁ H₂ (borel H₁) (borel H₂)
        (fun t => ⟨(t : G), e.symm ▸ t.2⟩) τ) =
      ∫ t : H₁, w ((t : G) * x) ∂τ := by
  subst e
  exact congrArg (fun ν => ∫ t : H₂, w ((t : G) * x) ∂ν) (@Measure.map_id H₂ (borel H₂) τ)

theorem solution
    (K L A : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ) (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ)
    (h : AutomorphicForm.twistedCentralizer K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) =
      AutomorphicForm.twistedCentralizer K L A σ δ) :
    AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ'
        (fun g => φ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g)) I ↔
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)
        (@Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ)
          (AutomorphicForm.twistedCentralizerBorel K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))
          (fun t => ⟨(t : GL (Fin 2) (L ⊗[K] A)), h.symm ▸ t.2⟩) τ')
        φ I := by
  have hconj : ∀ x : GL (Fin 2) (L ⊗[K] A),
      x⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) * (AutomorphicForm.sigmaGL K L A σ) x =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c * (x⁻¹ * δ * (AutomorphicForm.sigmaGL K L A σ) x) := by
    intro x
    rw [← mul_assoc x⁻¹ _ δ, ← B5A2.scalarGL_comm c x⁻¹]
    simp only [mul_assoc]
  unfold AutomorphicForm.IsTwistedOrbitalIntegralOn AutomorphicForm.IsTwistedSectionFnOn
  simp only [hconj, B5A2.integral_map_subgroupCast _ _ h]

end S_AutomorphicForm_isTwistedOrbitalIntegralOn_comp_scalar_mul_iff
end P2MW
export P2MW.S_AutomorphicForm_isTwistedOrbitalIntegralOn_comp_scalar_mul_iff (solution)
