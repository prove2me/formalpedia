-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:07.363339+00:00
-- url     : https://prove2.me/theorems/4c9a8dc0-7fd4-4e21-bf0a-f9eb0531eaed
-- title:
--   Choose
-- statement:
--   Definitions and structural lemmas for Choose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
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
namespace ChooseW
section Gen
variable {K : Type*} [Field K] {n : ℕ}
end Gen
section Star
variable {E : Type*} [Field E] [StarRing E] {n : ℕ}
def sv (w : Fin n → E) : Fin n → E := fun i => starRingEnd E (w i)
end Star
end ChooseW
end PI.UnitaryGroupMassFormula.LCG


