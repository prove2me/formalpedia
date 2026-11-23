-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsSmulOfPreservesFrameOrbits
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsSmulOfPreservesFrameOrbits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:47.99121+00:00
-- url     : https://prove2.me/theorems/f1c54c71-4afd-464a-9aa6-97570cd21bed
-- title:
--   Exists Smul Of Preserves Frame Orbits
-- statement:
--   Definitions and structural lemmas for Exists Smul Of Preserves Frame Orbits, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsSmulOfPreservesFrameOrbits.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
namespace GlobalTheory.OrbitScalar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end GlobalTheory.OrbitScalar


