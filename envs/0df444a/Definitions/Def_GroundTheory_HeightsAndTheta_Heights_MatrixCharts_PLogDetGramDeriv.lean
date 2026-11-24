-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramDeriv
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:28.645009+00:00
-- url     : https://prove2.me/theorems/541c3e02-3131-4186-b89b-c166f9b038d4
-- title:
--   PLog Det Gram Deriv
-- statement:
--   Definitions and structural lemmas for PLog Det Gram Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramDeriv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
namespace MCLogDetGramDeriv
def constK (g k : ℕ) : ℝ := (k.factorial : ℝ) * k * ((g : ℝ) ^ 2) ^ k * ((g : ℝ) ^ 2 + 2) + 1
end MCLogDetGramDeriv
end
end GroundTheory.Heights₂.Heights


