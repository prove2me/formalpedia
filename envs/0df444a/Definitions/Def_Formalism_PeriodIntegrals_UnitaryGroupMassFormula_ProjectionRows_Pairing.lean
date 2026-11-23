-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pairing
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:14:27.62102+00:00
-- url     : https://prove2.me/theorems/ab6f5b11-9054-4c65-813f-2d694f30bc84
-- title:
--   Pairing
-- statement:
--   Definitions and structural lemmas for Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/Pairing.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Adapted
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
section Gen
variable {K : Type} [Field K] [NumberField K]
end Gen
end PI.DvRows


