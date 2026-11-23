-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:29.084053+00:00
-- url     : https://prove2.me/theorems/7c7eacb4-49b4-4da7-b97e-19a3e58c958a
-- title:
--   Norm Add Le One
-- statement:
--   Definitions and structural lemmas for Norm Add Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubicExponentialFactor/NormAddLeOne.lean

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor
variable {p : ℕ} [Fact p.Prime]
end PI.CubicExponentialFactor.Wk
end


