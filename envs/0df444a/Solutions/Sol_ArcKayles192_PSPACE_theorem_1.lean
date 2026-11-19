-- Prove2me | solution 1 for ArcKayles192.PSPACE.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:20:42.435256+00:00
-- url     : https://prove2.me/submissions/ed1590f0-2fcd-4e24-a38d-d8bf48129439
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Theorems.Thm_ArcKayles192_PSPACE_theorem_1_membership
import Theorems.Thm_ArcKayles192_PSPACE_posCNF_pspaceHard
import Theorems.Thm_ArcKayles192_PSPACE_theorem_1_reduction
import Theorems.Thm_Turing_TM2ComputableInPolyTime_comp_of_polytime

open ArcKayles192.PSPACE OptimalQueuingComplexity.Restless

theorem solution : PSPACEComplete GraphInstance.enc arcKayles := by
  refine ⟨theorem_1_membership, fun L hL => ?_⟩
  obtain ⟨f₁, ⟨h₁⟩, e₁⟩ := posCNF_pspaceHard L hL
  obtain ⟨f₂, ⟨h₂⟩, e₂⟩ := theorem_1_reduction
  exact ⟨f₂ ∘ f₁, Turing.TM2ComputableInPolyTime.comp_of_polytime h₁ h₂,
    fun w => (e₁ w).trans (e₂ (f₁ w))⟩
