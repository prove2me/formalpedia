-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_Inputs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_Inputs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:41.539555+00:00
-- url     : https://prove2.me/theorems/0b3dd2e9-ffa2-4741-bf65-41ee83bd6650
-- title:
--   Inputs
-- statement:
--   Definitions and structural lemmas for Inputs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/Inputs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end PI.FdFjNearSup.W


