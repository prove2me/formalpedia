-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartDehomIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartDehomIdeal
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:25:07.574555+00:00
-- url     : https://prove2.me/theorems/9dfe9db8-e4b8-4248-8a8c-cdb7a67204a2
-- title:
--   PChart Dehom Ideal
-- statement:
--   Definitions and structural lemmas for PChart Dehom Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDehomIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartSet chartLift segre_chartLift chartLift_segre_apply)
end GroundTheory.Heights₂.Heights.Targets


