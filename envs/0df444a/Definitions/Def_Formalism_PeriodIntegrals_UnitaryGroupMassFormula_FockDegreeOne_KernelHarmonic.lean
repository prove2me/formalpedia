-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KernelHarmonic
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KernelHarmonic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:26.078809+00:00
-- url     : https://prove2.me/theorems/9c1a512b-66c6-4588-a2a7-890c5d21c2c0
-- title:
--   Kernel Harmonic
-- statement:
--   Definitions and structural lemmas for Kernel Harmonic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KernelHarmonic.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
namespace PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}
end PI.FockOneDegW.RedOps
namespace PI.FockOneDegW
open PI.FockOneDegW.RedOps
end PI.FockOneDegW


