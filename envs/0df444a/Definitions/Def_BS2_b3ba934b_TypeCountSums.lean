-- Prove2me | Definitions.Def_BS2_b3ba934b_TypeCountSums
-- name    : BS2_b3ba934b_TypeCountSums
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:29:11.851626+00:00
-- url     : https://prove2.me/theorems/f3d6d932-e835-4c7d-9490-a7a9d774f061
-- title:
--   Sensitivity separation: TypeCountSums (complete source module)
-- statement:
--   Complete Lean source module `TypeCountSums` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/TypeCountSums.lean; original SHA-256 ffbb1ee9b8acc6d1ca3acc20dde60494badad8b690e58ce4450968bd126afeaf; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_GlobalAccounting

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundTypeCounts
open ThreeBoundAccounting
open scoped Classical BigOperators
noncomputable section
variable {V K : Type} [Fintype V] [Fintype K]

theorem card_filter_tag (H : Finset V) (tag : V → K) (p : K → Prop) :
    (H.filter fun v => p (tag v)).card =
      ∑ k, if p k then typeCount H tag k else 0 := by
  classical
  have hh := sum_grouped H tag (fun k => if p k then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at hh
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact hh

theorem sum_typeCounts (H : Finset V) (tag : V → K) :
    (∑ k, typeCount H tag k) = H.card := by
  classical
  simpa using (sum_grouped H tag (fun _ => 1)).symm

theorem typeCount_zero_of_forbidden (H : Finset V) (tag : V → K) (k : K)
    (h : ∀ v ∈ H, tag v ≠ k) : typeCount H tag k = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact h v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2

theorem nonempty_type_of_count_pos (H : Finset V) (tag : V → K) (k : K)
    (h : 0 < typeCount H tag k) : ∃ v ∈ H, tag v = k := by
  classical
  obtain ⟨v,hv⟩ := Finset.card_pos.mp h
  exact ⟨v,(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2⟩

end
end ThreeBoundTypeCounts


