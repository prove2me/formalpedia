-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryOverlapCore_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13OrdinaryOverlapCore_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:31:02.491607+00:00
-- url     : https://prove2.me/theorems/3eca44be-4d19-4a80-a16a-ff0c584f34ba
-- title:
--   FLT.Assumptions.MazurProof.N13OrdinaryOverlapCore source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13OrdinaryOverlapCore

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13OrdinaryOverlapCore
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.Tactic.Ring

set_option autoImplicit false




/-!
# Coordinate identities on the ordinary N13 overlap

The two algebraic charts are related on their principal opens by

`x = t⁻¹`, `y = t⁻³v`.

This file proves both directions of the coordinate change over an arbitrary
commutative ring.  No cancellation or domain hypothesis is used: the only
input is the explicit inverse relation on the principal open.
-/

namespace MazurProof.N13OrdinaryOverlapCore

/-- The infinity equation implies the affine equation after substituting
`x = t⁻¹` and `y = t⁻³v`. -/
theorem affineEquation_of_infinityEquation
    {S : Type*} [CommRing S]
    (t x v : S)
    (htx : t * x = 1)
    (hInfinity :
      v ^ 2 + (1 + t ^ 2 + t ^ 3) * v = t + t ^ 2) :
    (x ^ 3 * v) ^ 2 +
        (x ^ 3 + x + 1) * (x ^ 3 * v) =
      x ^ 5 + x ^ 4 := by
  have hxt : x * t = 1 := by
    simpa [mul_comm] using htx
  have hx6t : x ^ 6 * t = x ^ 5 := by
    calc
      x ^ 6 * t = x ^ 5 * (x * t) := by ring
      _ = x ^ 5 := by rw [hxt]; ring
  have hx6t2 : x ^ 6 * t ^ 2 = x ^ 4 := by
    calc
      x ^ 6 * t ^ 2 = x ^ 4 * (x * t) ^ 2 := by ring
      _ = x ^ 4 := by rw [hxt]; ring
  have hx6t3 : x ^ 6 * t ^ 3 = x ^ 3 := by
    calc
      x ^ 6 * t ^ 3 = x ^ 3 * (x * t) ^ 3 := by ring
      _ = x ^ 3 := by rw [hxt]; ring
  calc
    (x ^ 3 * v) ^ 2 +
          (x ^ 3 + x + 1) * (x ^ 3 * v) =
        x ^ 6 * v ^ 2 + (x ^ 6 + x ^ 4 + x ^ 3) * v := by
          ring
    _ = x ^ 6 * v ^ 2 +
          (x ^ 6 + x ^ 6 * t ^ 2 + x ^ 6 * t ^ 3) * v := by
          rw [hx6t2, hx6t3]
    _ = x ^ 6 *
          (v ^ 2 + (1 + t ^ 2 + t ^ 3) * v) := by
          ring
    _ = x ^ 6 * (t + t ^ 2) := by rw [hInfinity]
    _ = x ^ 5 + x ^ 4 := by
          rw [mul_add, hx6t, hx6t2]

/-- The affine equation implies the infinity equation after substituting
`t = x⁻¹` and `v = t³y`. -/
theorem infinityEquation_of_affineEquation
    {S : Type*} [CommRing S]
    (x t y : S)
    (hxt : x * t = 1)
    (hAffine :
      y ^ 2 + (x ^ 3 + x + 1) * y = x ^ 5 + x ^ 4) :
    (t ^ 3 * y) ^ 2 +
        (1 + t ^ 2 + t ^ 3) * (t ^ 3 * y) =
      t + t ^ 2 := by
  have htx : t * x = 1 := by
    simpa [mul_comm] using hxt
  have ht6x : t ^ 6 * x = t ^ 5 := by
    calc
      t ^ 6 * x = t ^ 5 * (t * x) := by ring
      _ = t ^ 5 := by rw [htx]; ring
  have ht6x3 : t ^ 6 * x ^ 3 = t ^ 3 := by
    calc
      t ^ 6 * x ^ 3 = t ^ 3 * (t * x) ^ 3 := by ring
      _ = t ^ 3 := by rw [htx]; ring
  have ht6x4 : t ^ 6 * x ^ 4 = t ^ 2 := by
    calc
      t ^ 6 * x ^ 4 = t ^ 2 * (t * x) ^ 4 := by ring
      _ = t ^ 2 := by rw [htx]; ring
  have ht6x5 : t ^ 6 * x ^ 5 = t := by
    calc
      t ^ 6 * x ^ 5 = t * (t * x) ^ 5 := by ring
      _ = t := by rw [htx]; ring
  calc
    (t ^ 3 * y) ^ 2 +
          (1 + t ^ 2 + t ^ 3) * (t ^ 3 * y) =
        t ^ 6 * y ^ 2 + (t ^ 3 + t ^ 5 + t ^ 6) * y := by
          ring
    _ = t ^ 6 * y ^ 2 +
          (t ^ 6 * x ^ 3 + t ^ 6 * x + t ^ 6) * y := by
          rw [ht6x, ht6x3]
    _ = t ^ 6 *
          (y ^ 2 + (x ^ 3 + x + 1) * y) := by
          ring
    _ = t ^ 6 * (x ^ 5 + x ^ 4) := by rw [hAffine]
    _ = t + t ^ 2 := by
          rw [mul_add, ht6x5, ht6x4]

end MazurProof.N13OrdinaryOverlapCore


