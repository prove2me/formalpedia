-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:33.658038+00:00
-- url     : https://prove2.me/theorems/b44406d2-c3cd-4356-8988-4098627943f2
-- title:
--   Packing Separation
-- statement:
--   Definitions and structural lemmas for Packing Separation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PackingSeparation.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation


