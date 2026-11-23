-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensQ
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensQ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:23.110236+00:00
-- url     : https://prove2.me/theorems/c15f6105-a5b3-489c-83c6-3898ac86a1c1
-- title:
--   Loc Dens Q
-- statement:
--   Definitions and structural lemmas for Loc Dens Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensQ.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors
namespace LocalCountingSum
variable (K : Type) [Field K] [NumberField K]
def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)
end LocalCountingSum
end PI.VolStabW


