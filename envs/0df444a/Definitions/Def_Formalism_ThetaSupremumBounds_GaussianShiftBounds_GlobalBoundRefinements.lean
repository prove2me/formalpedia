-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
-- name    : Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:22:03.490713+00:00
-- url     : https://prove2.me/theorems/582247a7-a71b-4ba7-9457-603486d05048
-- title:
--   Global Bound Refinements
-- statement:
--   Definitions and structural lemmas for Global Bound Refinements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/GlobalBoundRefinements.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
end Formalism.DimensionVariation


