-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFIn
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFIn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:30.702811+00:00
-- url     : https://prove2.me/theorems/0a2bcdfc-7fda-4090-b11c-a07272b9f86d
-- title:
--   Loc Dens FFIn
-- statement:
--   Definitions and structural lemmas for Loc Dens FFIn, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFIn.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabS.FFHS
open Module Polynomial
section matrix
variable {K : Type} [Field K] {σ : K →+* K}
end matrix
section field
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
end field
end PI.VolStabS.FFHS


