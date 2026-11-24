-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:55:05.687543+00:00
-- url     : https://prove2.me/theorems/f57504ef-0035-4007-9821-73573b2cc189
-- title:
--   Index Of
-- statement:
--   Definitions and structural lemmas for Index Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.UnitaryGroupMassFormula.LCG
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [StarRing E] {n : ℕ}
def sv (w : Fin n → E) : Fin n → E := fun i => starRingEnd E (w i)
end SlopeTestRemainingChoices
section Aux2
variable {E : Type} [Field E] [NumberField E]
end Aux2
end PI.UnitaryGroupMassFormula.LCG


