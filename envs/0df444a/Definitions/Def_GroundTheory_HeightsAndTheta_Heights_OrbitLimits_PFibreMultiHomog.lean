-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFibreMultiHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFibreMultiHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:54.943914+00:00
-- url     : https://prove2.me/theorems/40c2744a-c1de-4770-b94b-0d645961127c
-- title:
--   PFibre Multi Homog
-- statement:
--   Definitions and structural lemmas for PFibre Multi Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFibreMultiHomog.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LiftZComponent
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
  GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end GroundTheory.Heights₂.Heights.Targets


