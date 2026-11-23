-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:44.245773+00:00
-- url     : https://prove2.me/theorems/cadca4b5-2c66-4bd5-a389-23d5455c3c56
-- title:
--   Small Natural Numbers Bound
-- statement:
--   Definitions and structural lemmas for Small Natural Numbers Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/SmallNaturalNumbersBound.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.PrimesDyadicRS.K
open Real
def D (h : ℕ) : ℕ := Nat.primeCounting h - Nat.primeCounting (h / 2)
end PI.PrimesDyadicRS.K


