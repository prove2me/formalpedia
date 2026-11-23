-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientHeightBoundOfLiftSupportPositivity
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientHeightBoundOfLiftSupportPositivity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:28.048106+00:00
-- url     : https://prove2.me/theorems/c362bdc7-7f57-482a-9506-fac582ed5caf
-- title:
--   Coefficient Height Bound Of Lift Support Positivity
-- statement:
--   Definitions and structural lemmas for Coefficient Height Bound Of Lift Support Positivity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientHeightBoundOfLiftSupportPositivity.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticOffDiagonalBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD


