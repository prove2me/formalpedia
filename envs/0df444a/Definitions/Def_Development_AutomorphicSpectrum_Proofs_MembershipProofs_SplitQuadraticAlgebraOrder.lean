-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:20.421107+00:00
-- url     : https://prove2.me/theorems/77f556c7-98a2-4749-862d-f6784ec34a2e
-- title:
--   Split Quadratic Algebra Order
-- statement:
--   Definitions and structural lemmas for Split Quadratic Algebra Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/SplitQuadraticAlgebraOrder.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
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
namespace GlobalTheory.CompanionTheory.SiegelChar
section Abstract
variable {E : Type} [CommRing E] {R : Type} [Ring R] [Algebra E R] {c : E → E} {σ : R →+ R}
  {G : Type} [Group G] {φ : G →* R} {e f : R}
end Abstract
end GlobalTheory.CompanionTheory.SiegelChar


