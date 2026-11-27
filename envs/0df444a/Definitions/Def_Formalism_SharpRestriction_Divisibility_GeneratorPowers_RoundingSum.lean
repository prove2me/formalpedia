-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_RoundingSum
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_RoundingSum
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-27T06:31:26.690238+00:00
-- url     : https://prove2.me/theorems/de772e14-009f-52f1-ada8-f1d84c91d646
-- title:
--   Rounding Sum
-- statement:
--   Definitions and structural lemmas for Rounding Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/RoundingSum.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FramedFamilyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_BOfNsmulLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}
end Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt


