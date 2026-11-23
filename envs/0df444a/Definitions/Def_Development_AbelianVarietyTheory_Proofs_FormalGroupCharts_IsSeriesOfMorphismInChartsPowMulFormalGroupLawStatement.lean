-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:09.221102+00:00
-- url     : https://prove2.me/theorems/28f03bbc-9dd1-45a0-860d-d22accee0f54
-- title:
--   Is Series Of Morphism In Charts Pow Mul Formal Group Law Statement
-- statement:
--   Definitions and structural lemmas for Is Series Of Morphism In Charts Pow Mul Formal Group Law Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsSeriesOfMorphismInChartsPowMulFormalGroupLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


