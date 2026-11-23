-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:46:13.624564+00:00
-- url     : https://prove2.me/theorems/bddacda8-0d5b-4a90-b4ff-ad81a1264feb
-- title:
--   Minimum Growth Bounds
-- statement:
--   Definitions and structural lemmas for Minimum Growth Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MinimumGrowthBounds.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace MinimumGrowthBounds
variable {r : ℕ} (X : Data E r)
end MinimumGrowthBounds
end ReciprocityTheory.ChartRestriction.G.FD


