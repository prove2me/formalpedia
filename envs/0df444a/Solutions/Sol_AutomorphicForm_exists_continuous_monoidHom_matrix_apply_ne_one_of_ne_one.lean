-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5dbb2400-f86a-58c7-95c0-2b3caf998db1

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one

set_option autoImplicit false

open NumberField AutomorphicForm

namespace SepPtsProof

variable (F : Type) [Field F]

noncomputable def stdRepAt (w₀ : InfinitePlace F) :
    (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* Matrix (Fin 2) (Fin 2) ℂ :=
  ((RingHom.mapMatrix (InfinitePlace.Completion.extensionEmbedding w₀)).toMonoidHom.comp
    (Units.coeHom (Matrix (Fin 2) (Fin 2) w₀.Completion))).comp
    ((rowIsometrySubgroup₀ w₀.Completion).subtype.comp (Pi.evalMonoidHom _ w₀))

theorem stdRepAt_apply (w₀ : InfinitePlace F) (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    stdRepAt F w₀ κ i j =
      InfinitePlace.Completion.extensionEmbedding w₀ (((κ w₀ : GL (Fin 2) w₀.Completion) : Matrix (Fin 2) (Fin 2) w₀.Completion) i j) :=
  rfl

theorem continuous_stdRepAt (w₀ : InfinitePlace F) : Continuous (stdRepAt F w₀) := by
  refine continuous_matrix fun i j => ?_
  simp only [stdRepAt_apply]
  refine (InfinitePlace.Completion.isometry_extensionEmbedding w₀).continuous.comp ?_
  exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w₀))).matrix_elem i j

end SepPtsProof

theorem solution
    (F : Type) [Field F] [NumberField F]
    (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (hκ : κ ≠ 1) :
    ∃ (n : ℕ) (ρ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* Matrix (Fin n) (Fin n) ℂ),
      Continuous ρ ∧ ρ κ ≠ 1 := by
  classical

  obtain ⟨w₀, hw₀⟩ : ∃ w₀, κ w₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hκ (funext h)
  refine ⟨2, SepPtsProof.stdRepAt F w₀, SepPtsProof.continuous_stdRepAt F w₀, fun h1 => hw₀ ?_⟩

  apply Subtype.ext
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun h1 i) j
  rw [SepPtsProof.stdRepAt_apply] at hij
  have h1ij : (1 : Matrix (Fin 2) (Fin 2) ℂ) i j =
      InfinitePlace.Completion.extensionEmbedding w₀ ((1 : Matrix (Fin 2) (Fin 2) w₀.Completion) i j) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1ij] at hij
  exact (InfinitePlace.Completion.extensionEmbedding w₀).injective hij

end S_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one (solution)
