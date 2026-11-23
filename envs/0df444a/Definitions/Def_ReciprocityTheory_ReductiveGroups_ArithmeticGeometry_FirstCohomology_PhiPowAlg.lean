-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:15.103794+00:00
-- url     : https://prove2.me/theorems/874dd26d-f158-4ef7-906e-dbd03a7ab651
-- title:
--   Phi Pow Alg
-- statement:
--   Definitions and structural lemmas for Phi Pow Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPowAlg.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
def hv (θ : A → A → A → U) (k : ℕ) (a B x : A) : U := cubN θ k a B x * (θ a x B)⁻¹
end ReciprocityTheory.ChartRestriction.G.H1


