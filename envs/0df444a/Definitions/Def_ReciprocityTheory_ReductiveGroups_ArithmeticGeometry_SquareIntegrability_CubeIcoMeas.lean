-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:33.307428+00:00
-- url     : https://prove2.me/theorems/bc758448-5fdd-4c26-8a06-2da77a823aee
-- title:
--   Cube Ico Meas
-- statement:
--   Definitions and structural lemmas for Cube Ico Meas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CubeIcoMeas.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
def cubeIco (κ : Type) : Set (κ → ℝ) := {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}
end
end ReciprocityTheory.ChartRestriction.G.I2


