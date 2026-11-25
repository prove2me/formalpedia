-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointInj
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointInj
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:23:02.193772+00:00
-- url     : https://prove2.me/theorems/f2068088-58ca-5a20-8020-e7742b8bdb53
-- title:
--   PCurve Vert Point Inj
-- statement:
--   Definitions and structural lemmas for PCurve Vert Point Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointInj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointLengthSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace CurveVerticalPointInjective
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
end CurveVerticalPointInjective
end GroundTheory.Heights₂.Heights.Targets


