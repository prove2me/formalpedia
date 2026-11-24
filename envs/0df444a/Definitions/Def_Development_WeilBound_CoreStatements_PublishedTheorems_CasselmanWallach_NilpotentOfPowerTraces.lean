-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_NilpotentOfPowerTraces
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_NilpotentOfPowerTraces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:13.737225+00:00
-- url     : https://prove2.me/theorems/6ed8ee54-c1df-4110-a91e-bf78bc12f6ea
-- title:
--   Nilpotent Of Power Traces
-- statement:
--   Definitions and structural lemmas for Nilpotent Of Power Traces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/NilpotentOfPowerTraces.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CW
namespace CharpolyPowerTraces
open Polynomial
end CharpolyPowerTraces
end PositivityTheory.CW
end


