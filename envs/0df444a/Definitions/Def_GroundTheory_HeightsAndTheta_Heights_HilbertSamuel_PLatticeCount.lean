-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PLatticeCount
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PLatticeCount
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:25:02.975917+00:00
-- url     : https://prove2.me/theorems/775e7d8a-a54b-5a99-b72e-c1358ff694b6
-- title:
--   PLattice Count
-- statement:
--   Definitions and structural lemmas for PLattice Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PLatticeCount.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Metric Module ZSpan
noncomputable section
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (La : Submodule ℤ V) {c : ℝ}
end
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


