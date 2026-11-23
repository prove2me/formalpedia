-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:47.558282+00:00
-- url     : https://prove2.me/theorems/be4dda75-05e3-4116-abe3-7bfeecaa7629
-- title:
--   Right One
-- statement:
--   Definitions and structural lemmas for Right One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightOne.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex Filter Topology
namespace PI.ZW
abbrev zeta1 : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ 1
end PI.ZW


