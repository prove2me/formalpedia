-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:08.321884+00:00
-- url     : https://prove2.me/theorems/55fd5fcc-7c54-4eaa-8a93-54a0af509f35
-- title:
--   Fj Flow
-- statement:
--   Definitions and structural lemmas for Fj Flow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FjFlow.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodLatticeCountable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
end ReciprocityTheory.ChartRestriction.G.FD


