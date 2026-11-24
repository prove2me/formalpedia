-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIUnique
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:27.249918+00:00
-- url     : https://prove2.me/theorems/3e5a7090-a3b1-45c6-94be-12b9e2ce2c07
-- title:
--   PThm IUnique
-- statement:
--   Definitions and structural lemmas for PThm IUnique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
namespace ThmIUnique
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end ThmIUnique
end
end GroundTheory.Heights₂.Heights.Inter


