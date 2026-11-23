-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:19.215612+00:00
-- url     : https://prove2.me/theorems/cc3a47b4-a9eb-412f-9bec-a6cb595b720c
-- title:
--   Reflection Fixes Normal
-- statement:
--   Definitions and structural lemmas for Reflection Fixes Normal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
variable {D : Dat A n r}
end Dat
end PI.VolSemiDirect.W.PG


