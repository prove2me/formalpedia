-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:10.460209+00:00
-- url     : https://prove2.me/theorems/a772e05a-8cf1-4ef1-b003-da22544e889a
-- title:
--   Norm Le One Of Integral Int
-- statement:
--   Definitions and structural lemmas for Norm Le One Of Integral Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
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
variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
end PI.OkpW


