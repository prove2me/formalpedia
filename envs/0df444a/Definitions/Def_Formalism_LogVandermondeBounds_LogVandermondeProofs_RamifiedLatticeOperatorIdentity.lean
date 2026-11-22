-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
-- name    : Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:41.762235+00:00
-- url     : https://prove2.me/theorems/8172c120-d626-4bff-aa74-e14498d39d5e
-- title:
--   Ramified Lattice Operator Identity
-- statement:
--   Definitions and structural lemmas for Ramified Lattice Operator Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/RamifiedLatticeOperatorIdentity.lean

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
section SlopeTestRemainingChoices
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
lemma pair_add_left (f g x : Fin r → k) : pair (f + g) x = pair f x + pair g x := by
  simp [pair, add_mul, Finset.sum_add_distrib]
def pairL (x : Fin r → k) : (Fin r → k) →+ k where
  toFun f := pair f x
  map_zero' := by simp [pair]
  map_add' f g := pair_add_left f g x
def pairTwoLinear (x y : Fin r → k) : (Fin r → k) →+ k × k where
  toFun f := (pair f x, pair f y)
  map_zero' := by simp [pair]
  map_add' f g := by simp [pair_add_left]
end SlopeTestRemainingChoices
end Formalism.LogVandermondeBounds.product_first_zeroth_parts


