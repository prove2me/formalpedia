-- Prove2me | solution 1 for AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d37a3d7c-f8d5-52c0-8543-0d9fc5954c14

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Topology

theorem solution (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c ∧ 0 < d₁ ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∈ 𝓝 g := by
  classical
  refine ⟨1 / 2, 1, 1 / 2, 2, {g}, by norm_num, by norm_num, ?_⟩
  have h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ interior (centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2) :=
    one_mem_interior_centreCutSiegelSet (by norm_num) one_ne_zero (by norm_num) (by norm_num)
  have hW : (⋃ x ∈ ({g} : Finset (AdelicGL2 (𝓞 F) F)), (· * x) '' centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2) =
      (· * g) '' centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2 := by
    ext h
    simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop, exists_eq_left]
  rw [hW]
  have hn : centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2 ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F) := mem_interior_iff_mem_nhds.mp h1
  have him := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hn
  rw [Homeomorph.coe_mulRight] at him
  simpa only [one_mul] using him

end S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds
end P2MW
export P2MW.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds (solution)
