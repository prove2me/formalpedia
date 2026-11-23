-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:10:54.395843+00:00
-- url     : https://prove2.me/theorems/0c37e46e-341d-4819-b2bc-60a8e0f0c09c
-- title:
--   Infinitely Many Primes In Ray Class
-- statement:
--   Definitions and structural lemmas for Infinitely Many Primes In Ray Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InfinitelyManyPrimesInRayClass.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set
namespace GlobalTheory.Mem.RayPrimes
section series
variable {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (a : ι → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
include hn ha
end series
section orth
variable {G : Type} [CommGroup G] [Fintype G]
end orth
section field
variable {K : Type} [Field K] [NumberField K]
end field
end GlobalTheory.Mem.RayPrimes


