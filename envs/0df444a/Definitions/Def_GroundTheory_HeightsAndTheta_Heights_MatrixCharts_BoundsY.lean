-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:24.433723+00:00
-- url     : https://prove2.me/theorems/91a54cf4-6977-4fbb-a0e2-1ad020d980f4
-- title:
--   Bounds Y
-- statement:
--   Definitions and structural lemmas for Bounds Y, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section
def entrySum {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ := ∑ j, ∑ k, |A j k|
end
end GroundTheory.Heights₂.Heights.MCBounds


