-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:33.8048+00:00
-- url     : https://prove2.me/theorems/ade8dd7d-9517-48c0-b3f4-b2c1561f527d
-- title:
--   Exists Eq Mul Of Column Span Le
-- statement:
--   Definitions and structural lemmas for Exists Eq Mul Of Column Span Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/ExistsEqMulOfColumnSpanLe.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
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
namespace PI.OddDualWeyl
namespace Misc
variable {O K : Type} [CommRing O] [Field K] [Algebra O K]
end Misc
end PI.OddDualWeyl


