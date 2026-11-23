-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ReducedLatticeShortBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ReducedLatticeShortBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:12.699176+00:00
-- url     : https://prove2.me/theorems/4067c427-00ed-4d3d-85ef-6c6366250661
-- title:
--   Reduced Lattice Short Bound
-- statement:
--   Definitions and structural lemmas for Reduced Lattice Short Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ReducedLatticeShortBound.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCombinations
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
end
end ReciprocityTheory.ChartRestriction.G.FD


