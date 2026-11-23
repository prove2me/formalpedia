-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SublatticeCoefficients
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SublatticeCoefficients
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:49.748578+00:00
-- url     : https://prove2.me/theorems/ba659d27-8953-475a-a2dd-1fcfa25a76ac
-- title:
--   Sublattice Coefficients
-- statement:
--   Definitions and structural lemmas for Sublattice Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SublatticeCoefficients.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
open NumberField Complex MeasureTheory ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
  ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients


