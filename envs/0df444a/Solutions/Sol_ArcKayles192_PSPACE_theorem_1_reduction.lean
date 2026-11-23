-- Prove2me | solution 1 for ArcKayles192.PSPACE.theorem_1_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:33:14.051571+00:00
-- url     : https://prove2.me/submissions/da697844-aae0-43a2-9c95-ef035b3980ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_ArcKayles192_PSPACE_ReductionInstance
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Theorems.Thm_ArcKayles192_PSPACE_reductionInstance_correct
import Theorems.Thm_ArcKayles192_PSPACE_reductionInstance_polytime

open ArcKayles192.PSPACE
open OptimalQueuingComplexity.Restless

theorem solution : PolyReduces PosCNF.enc posCNF GraphInstance.enc arcKayles := by
  exact ⟨reductionInstance, reductionInstance_polytime, reductionInstance_correct⟩
