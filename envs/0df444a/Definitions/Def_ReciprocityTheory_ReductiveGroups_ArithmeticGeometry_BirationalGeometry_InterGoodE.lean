-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodE
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:18.989361+00:00
-- url     : https://prove2.me/theorems/0b210ce8-d5b8-4bd6-9622-3692861f1150
-- title:
--   Inter Good E
-- statement:
--   Definitions and structural lemmas for Inter Good E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodE.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]
def forms {R : Type*} [CommRing R] [Algebra k R] {τ : Type*} [Fintype τ] (v : τ → R) {r : ℕ}
    (L : Fin r → τ → k) : Fin r → R :=
  fun j => ∑ t, L j t • v t
end
end ReciprocityTheory.ChartRestriction.G.Geo


