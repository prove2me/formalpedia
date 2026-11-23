-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensChLift
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensChLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:01.459471+00:00
-- url     : https://prove2.me/theorems/b999effd-8c0d-49d0-8cea-04e3e5c78cd3
-- title:
--   Loc Dens Ch Lift
-- statement:
--   Definitions and structural lemmas for Loc Dens Ch Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensChLift.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
namespace PI.VolStabW
namespace ChLiftW
end ChLiftW
open Classical in

def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t
end PI.VolStabW


