-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsFSDensity
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsFSDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:55.479843+00:00
-- url     : https://prove2.me/theorems/dfff65f8-f547-4519-aaab-8b0a485cadad
-- title:
--   Statements FSDensity
-- statement:
--   Definitions and structural lemmas for Statements FSDensity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/StatementsFSDensity.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm
def FubiniStudyChartDensity.Statement : Prop :=
  ∀ (N : ℕ) (z w : Fin N → ℂ),
    0 ≤ levi (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z w ∧
      maDens (fun _ y => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z =
        (N.factorial : ℝ) / (Real.pi ^ N * (1 + ∑ i, ‖z i‖ ^ 2) ^ (N + 1))
end GroundTheory.Heights₂.Heights.FourB


