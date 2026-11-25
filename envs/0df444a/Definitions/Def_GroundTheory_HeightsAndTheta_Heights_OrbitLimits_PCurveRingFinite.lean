-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveRingFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveRingFinite
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:23:01.588945+00:00
-- url     : https://prove2.me/theorems/e8fc5834-8b8b-541f-b0aa-57b749418161
-- title:
--   PCurve Ring Finite
-- statement:
--   Definitions and structural lemmas for PCurve Ring Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveRingFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
namespace CurveRingFiniteAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end CurveRingFiniteAlt
end
end GroundTheory.Heights₂.Heights.Targets


