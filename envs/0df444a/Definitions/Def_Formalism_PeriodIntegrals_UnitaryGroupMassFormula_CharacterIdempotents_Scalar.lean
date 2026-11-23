-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:33.766039+00:00
-- url     : https://prove2.me/theorems/e6a03f42-d0a5-46b3-8979-990457fe45c4
-- title:
--   Scalar
-- statement:
--   Definitions and structural lemmas for Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CharacterIdempotents/Scalar.lean

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
section General
variable {G : Type} [Group G] [Fintype G]
end General
end PI.CharIdemW


