-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:06.932793+00:00
-- url     : https://prove2.me/theorems/b32c322b-7167-4390-9f35-bb5ab6b8f925
-- title:
--   Red Ops
-- statement:
--   Definitions and structural lemmas for Red Ops, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/RedOps.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
namespace PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}
end PI.FockOneDegW.RedOps
namespace PI.FockOneDegW
open PI.FockOneDegW.RedOps
end PI.FockOneDegW


