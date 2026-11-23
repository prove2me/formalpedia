-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:22.140524+00:00
-- url     : https://prove2.me/theorems/9beec338-3267-4f53-97b1-583073366c73
-- title:
--   Exponential Growth Exclusion
-- statement:
--   Definitions and structural lemmas for Exponential Growth Exclusion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ExponentialGrowthExclusion.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion


