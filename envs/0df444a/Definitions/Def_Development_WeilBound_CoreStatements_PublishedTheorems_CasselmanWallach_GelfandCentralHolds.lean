-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GelfandCentralHolds
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GelfandCentralHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:11.304286+00:00
-- url     : https://prove2.me/theorems/213ce442-35db-4ff2-b80c-c00d5214ef59
-- title:
--   Gelfand Central Holds
-- statement:
--   Definitions and structural lemmas for Gelfand Central Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GelfandCentralHolds.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
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
namespace CasimirPowerCommute
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
end CasimirPowerCommute
end PositivityTheory.CW
end


