-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf
-- name    : Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:55.137506+00:00
-- url     : https://prove2.me/theorems/23d8dd1a-070d-46f8-8d7c-ff12fa62cf11
-- title:
--   Heightsound Of
-- statement:
--   Definitions and structural lemmas for Heightsound Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/HeightsoundOf.lean

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
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
open Formalism.LatticeIndexTer (ph)
end Formalism.DimensionVariation


