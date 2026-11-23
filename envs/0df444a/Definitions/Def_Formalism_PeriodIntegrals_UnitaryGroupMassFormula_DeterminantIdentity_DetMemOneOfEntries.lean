-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_DetMemOneOfEntries
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_DetMemOneOfEntries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:11.617218+00:00
-- url     : https://prove2.me/theorems/37a699d8-9a24-45f2-a39f-e68893c47c94
-- title:
--   Det Mem One Of Entries
-- statement:
--   Definitions and structural lemmas for Det Mem One Of Entries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/DetMemOneOfEntries.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.DIP
variable {E : Type} [Field E] [NumberField E] {N : ℕ}
end PI.DIP


