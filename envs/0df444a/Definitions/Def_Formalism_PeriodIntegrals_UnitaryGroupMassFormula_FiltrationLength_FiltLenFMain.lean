-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_FiltLenFMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_FiltLenFMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:42.888294+00:00
-- url     : https://prove2.me/theorems/1b758024-4403-40af-a019-7487932b6355
-- title:
--   Filt Len FMain
-- statement:
--   Definitions and structural lemmas for Filt Len FMain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiltrationLength/FiltLenFMain.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
import Definitions.Def_Formalism_PeriodIntegrals_FiltLenF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.FiltrationLength
open Submodule
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
end PI.FiltrationLength


