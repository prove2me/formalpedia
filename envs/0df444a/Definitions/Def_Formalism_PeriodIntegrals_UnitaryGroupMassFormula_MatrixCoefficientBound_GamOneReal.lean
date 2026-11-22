-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GamOneReal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GamOneReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:51:42.052105+00:00
-- url     : https://prove2.me/theorems/047117ca-c3ba-4561-8e4c-4b2847b7f0e0
-- title:
--   Gam One Real
-- statement:
--   Definitions and structural lemmas for Gam One Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/GamOneReal.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
namespace PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
end PI.GGMatBoundW


