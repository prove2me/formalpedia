-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordLatticeFullRank
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordLatticeFullRank
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:41.150507+00:00
-- url     : https://prove2.me/theorems/8867d751-3258-4c99-b875-a50e14abe648
-- title:
--   PCoord Lattice Full Rank
-- statement:
--   Definitions and structural lemmas for PCoord Lattice Full Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCoordLatticeFullRank.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordLatticeFullRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module
noncomputable section
variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


