-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SmallOperatorExistence
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SmallOperatorExistence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:00.153001+00:00
-- url     : https://prove2.me/theorems/547006a3-1298-4472-bfd8-c57d2a577796
-- title:
--   Small Operator Existence
-- statement:
--   Definitions and structural lemmas for Small Operator Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SmallOperatorExistence.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence


