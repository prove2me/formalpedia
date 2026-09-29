-- Prove2me | solution 1 for AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e295eac3-7003-558b-a3a9-ca161d3ec8d5

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact

open NumberField FLT.SmoothVectors AutomorphicForm

namespace Rho7aSol

theorem IsSmoothVector.finite_smul_image_of_isCompact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type*} [MulAction G M] {v : M} (hv : IsSmoothVector G v)
    {K : Set G} (hK : IsCompact K) : Set.Finite ((· • v) '' K) := by
  set U := MulAction.stabilizer G v
  have hUo : IsOpen (U : Set G) := hv

  have hcov : K ⊆ ⋃ k ∈ K, (fun g => k * g) '' (U : Set G) := by
    intro k hk
    simp only [Set.mem_iUnion]
    exact ⟨k, hk, 1, Subgroup.one_mem U, mul_one k⟩
  have hopen : ∀ k ∈ K, IsOpen ((fun g => k * g) '' (U : Set G)) := by
    intro k _
    exact (Homeomorph.mulLeft k).isOpenMap _ hUo
  obtain ⟨t, _htK, htF, htcov⟩ := hK.elim_finite_subcover_image hopen hcov
  refine (htF.image (· • v)).subset (fun w hw => ?_)
  simp only [Set.mem_image] at hw ⊢
  obtain ⟨k, hkK, rfl⟩ := hw
  have hk := htcov hkK
  simp only [Set.mem_iUnion, Set.mem_image] at hk
  obtain ⟨j, hjT, u, huU, hju⟩ := hk
  exact ⟨j, hjT, by rw [← hju, mul_smul, MulAction.mem_stabilizer_iff.mp huU]⟩

end Rho7aSol

theorem solution {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) {K : Set ↥(finiteAdelicGL2Subgroup F)} (hK : IsCompact K) :
    Set.Finite ((· • (RightTranslationFn.mk φ :
      RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) '' K) :=
  Rho7aSol.IsSmoothVector.finite_smul_image_of_isCompact hφ hK

#print axioms solution

end S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact (solution)
