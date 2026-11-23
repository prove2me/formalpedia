-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:30.357609+00:00
-- url     : https://prove2.me/theorems/9e5bbb95-c23a-46d1-abd7-b47029390cf4
-- title:
--   Two Sided Boost Bounds
-- statement:
--   Definitions and structural lemmas for Two Sided Boost Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TwoSidedBoostBounds.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMinimumLowerBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds ImaginaryMajorants
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace TwoSidedBoostBounds
variable {r : ℕ} (X : Data E r)
end TwoSidedBoostBounds
end ReciprocityTheory.ChartRestriction.G.FD


