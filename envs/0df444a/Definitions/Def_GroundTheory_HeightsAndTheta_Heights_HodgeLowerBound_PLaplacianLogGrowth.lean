-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PLaplacianLogGrowth
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PLaplacianLogGrowth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:38.739709+00:00
-- url     : https://prove2.me/theorems/3f9ce333-0c59-467d-944e-bcc1ca333a68
-- title:
--   PLaplacian Log Growth
-- statement:
--   Definitions and structural lemmas for PLaplacian Log Growth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PLaplacianLogGrowth.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianLogGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsInvDerivDecay
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianDecayZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real
end GroundTheory.Heights₂.Heights.LowerBoundFree


