-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:16.147804+00:00
-- url     : https://prove2.me/theorems/51a9ed04-290b-42e6-bc81-9061d5c748b2
-- title:
--   Loc Dens FFCnt
-- statement:
--   Definitions and structural lemmas for Loc Dens FFCnt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFCnt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
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
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
end PI.VolStabS.FFHS


