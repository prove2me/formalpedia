-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Central
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Central
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:34.060304+00:00
-- url     : https://prove2.me/theorems/318444b8-7b23-4a6f-91d5-d4bbf5966839
-- title:
--   Central
-- statement:
--   Definitions and structural lemmas for Central, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Central.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
namespace PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
end PI.CharIdemW


