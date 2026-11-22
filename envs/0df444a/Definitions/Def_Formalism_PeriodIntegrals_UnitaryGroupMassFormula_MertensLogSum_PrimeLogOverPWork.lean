-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:08.013125+00:00
-- url     : https://prove2.me/theorems/4f7bb5b8-ae15-4968-9211-d56e25119260
-- title:
--   Prime Log Over PWork
-- statement:
--   Definitions and structural lemmas for Prime Log Over PWork, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
def E : Finset ℕ := {4, 8, 16, 9, 27, 25}
end PI.PrimeLogOverPWork


