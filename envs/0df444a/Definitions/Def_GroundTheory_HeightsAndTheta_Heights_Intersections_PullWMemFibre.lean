-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:23:19.401633+00:00
-- url     : https://prove2.me/theorems/abcc170a-8e5a-523c-a5b0-73996a3fe6ba
-- title:
--   Pull WMem Fibre
-- statement:
--   Definitions and structural lemmas for Pull WMem Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PullWMemFibre.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsIntegralLogNormRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherExtra
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
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
namespace IntersectionWithSection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
end IntersectionWithSection
end GroundTheory.Heights₂.Heights.Inter


