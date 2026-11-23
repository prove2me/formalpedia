-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:57.410839+00:00
-- url     : https://prove2.me/theorems/de69b56c-6ace-474e-81f9-e1ea13326b17
-- title:
--   Discriminant Trace Bounds
-- statement:
--   Definitions and structural lemmas for Discriminant Trace Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscriminantTraceBounds.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace DiscriminantTraceBounds
open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
section data
variable [IsCMField E] {r : ℕ} (X : DataX E r)
end data
end DiscriminantTraceBounds
end ReciprocityTheory.ChartRestriction.G.FD


