-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterChart
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterChart
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:13:14.058514+00:00
-- url     : https://prove2.me/theorems/2cc3aece-f7c4-565d-856c-c2649b79a34a
-- title:
--   POrbit Center Chart
-- statement:
--   Definitions and structural lemmas for POrbit Center Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G OrbitChartMax
end GroundTheory.Heights₂.Heights


