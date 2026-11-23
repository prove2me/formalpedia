-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeBoundAtMaximumOfTransference
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeBoundAtMaximumOfTransference
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:11.471082+00:00
-- url     : https://prove2.me/theorems/b6a88f40-8455-4f6f-9da0-c5e0ac1c7a81
-- title:
--   Lattice Bound At Maximum Of Transference
-- statement:
--   Definitions and structural lemmas for Lattice Bound At Maximum Of Transference, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeBoundAtMaximumOfTransference.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SmallOperatorExistence
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD


