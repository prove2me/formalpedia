-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinimalLatticeNorm_NormTwoEqOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinimalLatticeNorm_NormTwoEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:06.204703+00:00
-- url     : https://prove2.me/theorems/8fdbb79d-e00d-4861-86d7-12c7384d940b
-- title:
--   Norm Two Eq One
-- statement:
--   Definitions and structural lemmas for Norm Two Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinimalLatticeNorm/NormTwoEqOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.LatMinWork
variable {p : ℕ} [hp : Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]
end PI.LatMinWork
namespace PI
end PI


