-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:32:32.632963+00:00
-- url     : https://prove2.me/theorems/eb17a705-22d1-42c2-902f-1f052144ad7e
-- title:
--   Power Sum
-- statement:
--   Definitions and structural lemmas for Power Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/PowerSum.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.Mk
open Matrix Finset
def kron {n : Type*} (k : ℕ) (M : Matrix n n ℤ) : Matrix (Fin k → n) (Fin k → n) ℤ :=
  fun i j => ∏ t, M (i t) (j t)
end PI.Mk


