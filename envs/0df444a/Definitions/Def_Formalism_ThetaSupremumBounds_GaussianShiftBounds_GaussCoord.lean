-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord
-- name    : Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:38.229155+00:00
-- url     : https://prove2.me/theorems/db2e9d6b-268b-4660-80d5-2301462bffd0
-- title:
--   Gauss Coord
-- statement:
--   Definitions and structural lemmas for Gauss Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/GaussCoord.lean

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory
open scoped ComplexConjugate Real
namespace Formalism.DimensionVariation
end Formalism.DimensionVariation


