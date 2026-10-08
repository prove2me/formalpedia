-- Prove2me | Definitions.Def_keyholeBoundaryPath
-- name    : keyholeBoundaryPath
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T11:30:42.393909+00:00
-- url     : https://prove2.me/theorems/f459c686-1447-4348-8a65-5562909b96e7
-- title:
--   Piecewise keyhole boundary path
-- statement:
--   A piecewise path on the unit interval assembled from the upper bank, outer arc, lower bank, and inner arc in the standard positively oriented keyhole order.
-- source:
--   Standard positively oriented keyhole contour parametrization.

import Mathlib
import Definitions.Def_keyholeInnerArc
import Definitions.Def_keyholeOuterArc
import Definitions.Def_keyholeUpperBank
import Definitions.Def_keyholeLowerBank

noncomputable def keyholeBoundaryPath (a₀ a₁ r R : ℝ) : ℝ → ℂ := fun t =>
  if t < 1 / 4 then keyholeUpperBank (a₀ + 4 * t * (a₁ - a₀))
  else if t < 1 / 2 then keyholeOuterArc R (4 * t - 1)
  else if t < 3 / 4 then keyholeLowerBank (a₁ + (4 * t - 2) * (a₀ - a₁))
  else keyholeInnerArc r (4 * t - 3)


