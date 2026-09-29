-- Prove2me | solution 1 for AutomorphicForm.isCompact_rowIsometrySubgroup_detOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a212af46-b978-5237-859d-985cf7777596

import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne

set_option autoImplicit false

open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel

theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    IsCompact (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) := by
  set A : Set w.Completion := {x | ‖x‖ ≤ 1} with hA_def
  have hA : IsCompact A := AutomorphicForm.isCompact_setOf_norm_le_one_completion F w
  set C : Set (Matrix (Fin 2) (Fin 2) w.Completion) := {m | ∀ i j, m i j ∈ A} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hA
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) w.Completion)) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))

  have hclosed : IsClosed (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) := by
    have hset : (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion))
        = {k : GL (Fin 2) w.Completion | ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1}
            ∩ {k : GL (Fin 2) w.Completion | IsRowIsometry k} := by
      ext k
      simp only [SetLike.mem_coe, mem_rowIsometrySubgroup₀_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hset]
    refine IsClosed.inter ?_ (isClosed_setOf_isRowIsometry w.Completion)
    exact isClosed_eq ((continuous_id.matrix_det).comp Units.continuous_val) continuous_const
  refine hK.of_isClosed_subset hclosed ?_
  have hmemC : ∀ k : GL (Fin 2) w.Completion, k ∈ rowIsometrySubgroup₀ w.Completion →
      (k : Matrix (Fin 2) (Fin 2) w.Completion) ∈ C := by
    intro k hk i j
    exact ((mem_rowIsometrySubgroup₀_iff _).1 hk).2.norm_apply_le_one i j
  intro k hk
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  exact ⟨hmemC k hk, _, hmemC k⁻¹ ((rowIsometrySubgroup₀ w.Completion).inv_mem hk), rfl⟩

end S_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
end P2MW
export P2MW.S_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne (solution)
