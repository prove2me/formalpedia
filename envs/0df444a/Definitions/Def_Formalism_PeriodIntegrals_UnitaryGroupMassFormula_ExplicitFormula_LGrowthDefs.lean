-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:24.978807+00:00
-- url     : https://prove2.me/theorems/cb984a8a-74e5-421d-8bf4-ffeed2a56e1e
-- title:
--   LGrowth Defs
-- statement:
--   Definitions and structural lemmas for LGrowth Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EF
def ZetaGrowth (C : ℝ) : Prop :=
  ∀ s : ℂ, -4 ≤ s.re → s.re ≤ 8 → ‖(s - 1) * riemannZeta s‖ ≤ C * (|s.im| + 2) ^ 7
end PI.EF


