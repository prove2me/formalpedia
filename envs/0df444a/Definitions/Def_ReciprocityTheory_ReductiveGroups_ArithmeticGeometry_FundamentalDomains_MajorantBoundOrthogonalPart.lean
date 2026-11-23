-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:37.393485+00:00
-- url     : https://prove2.me/theorems/c5ddc7fa-f55e-4520-8a40-b1bc281cb65c
-- title:
--   Majorant Bound Orthogonal Part
-- statement:
--   Definitions and structural lemmas for Majorant Bound Orthogonal Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantBoundOrthogonalPart.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
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
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
end Data
end ReciprocityTheory.ChartRestriction.G.FD


