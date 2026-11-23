-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramUnitMultiplication_BeMulByZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramUnitMultiplication_BeMulByZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:27.175785+00:00
-- url     : https://prove2.me/theorems/766d372a-b375-4073-965a-762b568c4dfa
-- title:
--   Be Mul By Zero
-- statement:
--   Definitions and structural lemmas for Be Mul By Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramUnitMultiplication/BeMulByZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace PI.UnitaryGroupMassFormula.GramUnit
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
end PI.UnitaryGroupMassFormula.GramUnit


