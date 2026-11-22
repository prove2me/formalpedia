-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftAsm
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftAsm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:28.016912+00:00
-- url     : https://prove2.me/theorems/90e099c2-eafe-48ad-bae8-bc0063e2613e
-- title:
--   Shift Asm
-- statement:
--   Definitions and structural lemmas for Shift Asm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftAsm.lean

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.FG.FormalGroupLawMap
open MvPowerSeries
variable {R S : Type*} [CommRing R] [CommRing S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Formalism.FG.FormalGroupLawMap
namespace Formalism.FG
open Formalism.G Formalism.FG.FormalGroupLawMap
end Formalism.FG


