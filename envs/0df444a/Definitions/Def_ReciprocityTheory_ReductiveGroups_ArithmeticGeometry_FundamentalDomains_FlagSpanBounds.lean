-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlagSpanBounds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlagSpanBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:45.629382+00:00
-- url     : https://prove2.me/theorems/80bd4a3c-36cd-43c7-b92b-aa534992d9f2
-- title:
--   Flag Span Bounds
-- statement:
--   Definitions and structural lemmas for Flag Span Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlagSpanBounds.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximumHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
end
end ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
namespace ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD


