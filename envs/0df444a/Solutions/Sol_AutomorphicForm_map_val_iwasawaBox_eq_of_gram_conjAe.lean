-- Prove2me | solution 1 for AutomorphicForm.map_val_iwasawaBox_eq_of_gram_conjAe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9f92c931-0c7b-5982-9837-964a8b4024b7

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Theorems.Thm_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_map_val_iwasawaBox_eq_of_gram_conjAe

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (c : ℝˣ)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (n₁ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal)
    (hgram₁ : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
               Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
         Measure.map (fun t : ↥(Subgroup.centralizer
               ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
             ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
               (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    @Measure.map _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) (glBorelOf ℝ)
        Subtype.val τ {g : GL (Fin 2) ℝ | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
              ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
              (g : Matrix (Fin 2) (Fin 2) ℝ) =
                !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} =
      ENNReal.ofReal (8 * Real.pi) * s := by
  letI iT : MeasurableSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) :=
    centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  letI iG : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  obtain ⟨hli, hspan, hmap⟩ := hgram₁
  obtain ⟨-, h2⟩ := AutomorphicForm.map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real
    c τ n₁ e₁ s hli hspan hmap
  have hclosed : IsClosed ((Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) : Set (GL (Fin 2) ℝ)) := by
    change IsClosed (Set.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
    exact Set.isClosed_centralizer _
  have hemb : MeasurableEmbedding (Subtype.val : (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) → GL (Fin 2) ℝ) :=
    Topology.IsEmbedding.subtypeVal.measurableEmbedding (by
      rw [Subtype.range_coe_subtype]; exact hclosed.measurableSet)
  rw [hemb.map_apply, mul_comm]
  exact h2

end S_AutomorphicForm_map_val_iwasawaBox_eq_of_gram_conjAe
end P2MW
export P2MW.S_AutomorphicForm_map_val_iwasawaBox_eq_of_gram_conjAe (solution)
