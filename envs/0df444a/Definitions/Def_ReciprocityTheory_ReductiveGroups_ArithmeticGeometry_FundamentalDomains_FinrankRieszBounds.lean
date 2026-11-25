-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankRieszBounds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankRieszBounds
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:41.796263+00:00
-- url     : https://prove2.me/theorems/d3dc9ac0-444f-4aee-83fd-2b3035eef7a5
-- title:
--   Finrank Riesz Bounds
-- statement:
--   Definitions and structural lemmas for Finrank Riesz Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankRieszBounds.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace FinrankRieszBounds
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ X.dom)]
end FinrankRieszBounds
end ReciprocityTheory.ChartRestriction.G.FD


