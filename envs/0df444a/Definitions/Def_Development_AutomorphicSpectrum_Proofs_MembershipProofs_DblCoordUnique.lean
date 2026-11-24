-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DblCoordUnique
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_DblCoordUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:17.378799+00:00
-- url     : https://prove2.me/theorems/c2860942-10b8-4637-9756-636518bc9a66
-- title:
--   Dbl Coord Unique
-- statement:
--   Definitions and structural lemmas for Dbl Coord Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DblCoordUnique.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
namespace GlobalTheory.CompanionTheory.WeilOneMember
section Alg
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
end Alg
end GlobalTheory.CompanionTheory.WeilOneMember


