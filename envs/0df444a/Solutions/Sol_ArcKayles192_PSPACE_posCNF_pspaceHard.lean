-- Prove2me | solution 1 for ArcKayles192.PSPACE.posCNF_pspaceHard
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:14.53081+00:00
-- url     : https://prove2.me/submissions/34af3de6-061a-44fc-999b-d5c11d950840
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Theorems.Thm_Turing_TM2ComputableInPolyTime_comp_of_polytime
import Theorems.Thm_ArcKayles192_PSPACE_qbf_pspaceHard
import Theorems.Thm_ArcKayles192_PSPACE_schaefer_qbf_to_posCNF

open ArcKayles192.PSPACE OptimalQueuingComplexity.Restless

/-- Schaefer's reduction, composed with PSPACE-hardness of QBF. -/
theorem solution : PSPACEHard PosCNF.enc posCNF := by
  intro L hL
  obtain ⟨f, hf, hfs⟩ := qbf_pspaceHard L hL
  obtain ⟨g, hg, hgs⟩ := schaefer_qbf_to_posCNF
  refine ⟨g ∘ f, ?_, ?_⟩
  · rcases hf with ⟨hf⟩
    rcases hg with ⟨hg⟩
    exact Turing.TM2ComputableInPolyTime.comp_of_polytime hf hg
  · intro w
    exact (hfs w).trans (hgs (f w))
