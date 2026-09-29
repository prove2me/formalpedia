-- Prove2me | solution 1 for AutomorphicForm.exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/78c0d072-865c-521e-891b-602276399e70

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom

set_option autoImplicit false

open NumberField MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hι : IsEmpty (L →ₐ[K] InfiniteAdeleRing K)) (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (hφt : IsArchFactorBiFinite L tysL φa) :
    ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧
      (∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        ∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ 1 →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ))
          (τ' : @Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
            (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
          Coupled K L (InfiniteAdeleRing K) σ γ δ 1 τ τ' →
          ∃ I : ℂ,
            IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) δ τ' (φa ∘ archIdentGL K L) I ∧
              IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa I) ∧
      (∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        (¬ ∃ δ, IsNormOf K L (InfiniteAdeleRing K) σ γ δ) →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa 0) := by
  have hram :
      ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
      (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
      (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
      (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
        fun q : (Fin 2 → Fin 2 → ℂ) × P =>
          Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2))))
      (hΦl : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
        fun q : (Fin 2 → Fin 2 → ℂ) × P =>
          Φ (Matrix.of.symm (((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of q.1), q.2))))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL),
      ∃ F : (Fin 2 → Fin 2 → ℝ) × P → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
          fun r : (Fin 2 → Fin 2 → ℝ) × P =>
            F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
          fun r : (Fin 2 → Fin 2 → ℝ) × P =>
            F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) ∧
        (∀ (n : ℕ) (c : Fin n → ℂ) (q : Fin n → P),
          (∀ E : Fin 2 → Fin 2 → ℂ, ∑ j, c j * Φ (E, q j) = 0) →
            ∀ E' : Fin 2 → Fin 2 → ℝ, ∑ j, c j * F (E', q j) = 0) ∧
        (∀ p : P, ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ →
          ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ 1 →
          ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
            (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
              (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
            @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
            Coupled ℝ ℂ ℝ Complex.conjAe γ δ 1 τ τ' →
            ∀ I I' : ℂ,
              IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
                (fun y => Φ (Matrix.of.symm
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ),
                  p)) I' →
              IsOrbitalIntegralOn ℝ μA γ τ (fun g => F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)) I →
              I' = I) ∧
        (∀ p : P, ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
          ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
            @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μA γ τ (fun g => F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)) I →
              I = 0)
      := by
    exact
      AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq
  exact
    AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe
      K L hdeg σ hσ hι tysL φa hφa hφt hram

end S_AutomorphicForm_exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
end P2MW
export P2MW.S_AutomorphicForm_exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom (solution)
