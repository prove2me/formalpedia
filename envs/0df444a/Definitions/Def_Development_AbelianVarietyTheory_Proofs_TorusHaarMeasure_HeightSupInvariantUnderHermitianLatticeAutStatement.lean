-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightSupInvariantUnderHermitianLatticeAutStatement
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightSupInvariantUnderHermitianLatticeAutStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:00.18615+00:00
-- url     : https://prove2.me/theorems/9a772653-ddb0-4a97-9228-41cfa06c24e7
-- title:
--   Height Sup Invariant Under Hermitian Lattice Aut Statement
-- statement:
--   Definitions and structural lemmas for Height Sup Invariant Under Hermitian Lattice Aut Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/HeightSupInvariantUnderHermitianLatticeAutStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightSupInvariantUnderHermitianLatticeAut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]


