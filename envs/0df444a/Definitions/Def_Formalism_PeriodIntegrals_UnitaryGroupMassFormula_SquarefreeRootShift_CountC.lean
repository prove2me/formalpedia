-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:55.819568+00:00
-- url     : https://prove2.me/theorems/e44082fd-9d06-4efd-954d-9856f5f1daf4
-- title:
--   Count C
-- statement:
--   Definitions and structural lemmas for Count C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
end PI.SqfRootShift.W


