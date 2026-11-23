-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:40.757032+00:00
-- url     : https://prove2.me/theorems/d2a1f46d-467d-4914-8f46-e6c9e64dc63e
-- title:
--   Integral Statement Pf A
-- statement:
--   Definitions and structural lemmas for Integral Statement Pf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
noncomputable section
section Cone
open MvPolynomial
variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}
def cone (a : ι → E) : MvPolynomial ι R →ₐ[R] Polynomial E :=
  aeval fun i => Polynomial.C (a i) * Polynomial.X
end Cone
section Int
open MvPolynomial
variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}
end Int
section Homog
open Polynomial
end Homog
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf


