-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:20:59.089487+00:00
-- url     : https://prove2.me/theorems/472f0a94-3746-4ee0-a2b8-b9ef642ccf65
-- title:
--   PHadamard Mean
-- statement:
--   Definitions and structural lemmas for PHadamard Mean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField Matrix GroundTheory.Heights₂.Heights
noncomputable section
section GramHadamard
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
end GramHadamard
end
end GroundTheory.Heights₂.Heights.LatticeLemmas


