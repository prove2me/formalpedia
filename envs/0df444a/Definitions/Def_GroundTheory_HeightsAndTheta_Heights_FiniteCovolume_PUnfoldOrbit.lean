-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldOrbit
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldOrbit
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:18.801727+00:00
-- url     : https://prove2.me/theorems/08bf1c84-ca1a-4b9a-b0e8-39002c622616
-- title:
--   PUnfold Orbit
-- statement:
--   Definitions and structural lemmas for PUnfold Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldOrbit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal Pointwise
variable (G : Type*) [Group G]
end GroundTheory.Heights₂.Heights.FiniteCovolume


