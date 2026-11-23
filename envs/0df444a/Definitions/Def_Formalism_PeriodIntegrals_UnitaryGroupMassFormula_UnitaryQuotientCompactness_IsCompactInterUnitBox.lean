-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:21:31.122107+00:00
-- url     : https://prove2.me/theorems/9039347f-b31f-449e-8f41-4a6d346d3f1c
-- title:
--   Is Compact Inter Unit Box
-- statement:
--   Definitions and structural lemmas for Is Compact Inter Unit Box, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/IsCompactInterUnitBox.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {D : Matrix (Fin m) (Fin m) ℂ → ℝ}
def box1 (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) := {x | ∀ i j, ‖(x - 1) i j‖ ≤ 1}
end PI.QuotSetU.UnitaryGroupMassFormula.SW


