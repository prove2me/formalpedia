-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:10.967899+00:00
-- url     : https://prove2.me/theorems/c2b16349-9e0d-48e5-b785-2533e2dbb63c
-- title:
--   Holomorphic Periodicity Extension
-- statement:
--   Definitions and structural lemmas for Holomorphic Periodicity Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HolomorphicPeriodicityExtension.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD


