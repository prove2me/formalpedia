-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:31.558242+00:00
-- url     : https://prove2.me/theorems/3231d3c3-494a-4e22-ad19-bc56d568e1e5
-- title:
--   Shift FE
-- statement:
--   Definitions and structural lemmas for Shift FE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean

import Definitions.Def_Formalism_FormalGroupWitt_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace Formalism.FG
namespace ShiftFEAux
open MvPowerSeries
variable {K : Type*} [Field K] {l m : ℕ}
end ShiftFEAux
end Formalism.FG


