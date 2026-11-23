-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
-- name    : ReciprocityTheory_GroupCohomology_RankLenA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:44.115667+00:00
-- url     : https://prove2.me/theorems/bc735c26-9c56-4f83-b9e3-f1eb0f740ffa
-- title:
--   Rank Len A
-- statement:
--   Definitions and structural lemmas for Rank Len A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLenA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.TorsionRankLength
universe u
open Module Submodule Function
open scoped Pointwise TensorProduct
section General
variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
abbrev K (M : Type u) [AddCommGroup M] [Module R M] (r : R) : Submodule R M :=
  LinearMap.ker (r • LinearMap.id : M →ₗ[R] M)
end General
section DVR
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (H : Type u) [AddCommGroup H] [Module R H] [Module.Finite R H]
end DVR
section Main
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
end Main
end ReciprocityTheory.Coh.TorsionRankLength


