-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:03.070479+00:00
-- url     : https://prove2.me/theorems/f50b1294-b2a9-4a3d-b7bb-541f5ca6e2c4
-- title:
--   CFrob
-- statement:
--   Definitions and structural lemmas for CFrob, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/CFrob.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFixRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
end PI.OkpW


