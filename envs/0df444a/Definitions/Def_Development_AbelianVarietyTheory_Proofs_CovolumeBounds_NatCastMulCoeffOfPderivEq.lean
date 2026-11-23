-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:16.639923+00:00
-- url     : https://prove2.me/theorems/1a3a77e8-9229-4eea-bd3a-ccd61d79bf4d
-- title:
--   Nat Cast Mul Coeff Of Pderiv Eq
-- statement:
--   Definitions and structural lemmas for Nat Cast Mul Coeff Of Pderiv Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
section Chain
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
end Chain
section Poincare
variable {σ ι A : Type*} [CommRing A]
variable [Algebra ℚ A]
end Poincare
end GlobalTheory.FormalCalc


