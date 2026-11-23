-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:49.817265+00:00
-- url     : https://prove2.me/theorems/e9407075-952e-4f1a-a558-fe318f247112
-- title:
--   Smul Mem Ideal Smul
-- statement:
--   Definitions and structural lemmas for Smul Mem Ideal Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W]
end PI.LocGlobInclWork


