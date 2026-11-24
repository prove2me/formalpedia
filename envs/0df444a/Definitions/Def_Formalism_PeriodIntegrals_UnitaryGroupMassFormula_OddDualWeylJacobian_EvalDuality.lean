-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_EvalDuality
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_EvalDuality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:10.638172+00:00
-- url     : https://prove2.me/theorems/5b3eacf6-e36d-4578-ad88-f692841c5c58
-- title:
--   Eval Duality
-- statement:
--   Definitions and structural lemmas for Eval Duality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/EvalDuality.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl.EvA
open Red
variable {K : Type} [Field K]
end PI.OddDualWeyl.EvA
namespace PI.OddDualWeyl
open Red EvA
end PI.OddDualWeyl


