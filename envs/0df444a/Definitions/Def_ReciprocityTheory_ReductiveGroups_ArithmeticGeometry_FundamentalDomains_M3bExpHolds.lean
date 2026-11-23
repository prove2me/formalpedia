-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:13.175101+00:00
-- url     : https://prove2.me/theorems/d81e065b-a94c-4a77-877e-e612ba40f818
-- title:
--   M3b Exp Holds
-- statement:
--   Definitions and structural lemmas for M3b Exp Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/M3bExpHolds.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrequencyIndexing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
  ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD


