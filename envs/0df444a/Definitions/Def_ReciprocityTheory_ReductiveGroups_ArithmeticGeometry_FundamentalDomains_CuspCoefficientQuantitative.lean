-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientQuantitative
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientQuantitative
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:32.99761+00:00
-- url     : https://prove2.me/theorems/4459c26f-d2d9-4ac8-9224-5fd05a5417e9
-- title:
--   Cusp Coefficient Quantitative
-- statement:
--   Definitions and structural lemmas for Cusp Coefficient Quantitative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientQuantitative.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative


