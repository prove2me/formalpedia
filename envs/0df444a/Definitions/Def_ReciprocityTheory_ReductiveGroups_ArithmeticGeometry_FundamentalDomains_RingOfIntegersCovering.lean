-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RingOfIntegersCovering
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RingOfIntegersCovering
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:34.1498+00:00
-- url     : https://prove2.me/theorems/653f5274-3075-4372-a074-f21ee96e3092
-- title:
--   Ring Of Integers Covering
-- statement:
--   Definitions and structural lemmas for Ring Of Integers Covering, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RingOfIntegersCovering.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
open NumberField InfinitePlace Module Submodule TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering


