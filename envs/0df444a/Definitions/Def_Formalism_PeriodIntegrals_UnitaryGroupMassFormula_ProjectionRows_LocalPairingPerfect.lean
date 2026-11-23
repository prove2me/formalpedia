-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocalPairingPerfect
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocalPairingPerfect
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:46.921119+00:00
-- url     : https://prove2.me/theorems/dd8ff5d1-ecb8-4076-9e41-917ff5bcb6dd
-- title:
--   Local Pairing Perfect
-- statement:
--   Definitions and structural lemmas for Local Pairing Perfect, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LocalPairingPerfect.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.HermitianLatticesTheory
end PI.DvRows


