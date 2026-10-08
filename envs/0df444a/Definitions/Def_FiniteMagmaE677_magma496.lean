-- Prove2me | Definitions.Def_FiniteMagmaE677_magma496
-- name    : FiniteMagmaE677_magma496
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T23:45:19.822398+00:00
-- url     : https://prove2.me/theorems/d394be6a-aecc-4392-9527-e96442310e14
-- title:
--   The 496-element construction: quadratic-character fibered magma on Z/31 × M

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# The 496-element construction (blueprint Chapter 13)

The fiber operation of the blueprint's finite non-right-cancellative E677
magma: the base ring is `ZMod 31` with the affine operation `3x - 2y`, and the
fiber is selected by the quadratic character of `y - x` (Euler's criterion
`z ^ 15 = 1` for squares modulo 31): the diagonal uses a fifth root of unity
`ζ`, square differences project to the second argument, and non-square
differences use a cube root of unity `ω`.
-/

namespace FiniteMagmaE677

universe v

/-- Fiber operation selected by the quadratic character of `y - x` in `ZMod 31`. -/
def fiber496 {M : Type v} [CommRing M] (ζ ω : M) (x y : ZMod 31) (s t : M) : M :=
  if y - x = 0 then (1 + ζ) * s + ζ * t
  else if (y - x) ^ 15 = 1 then t
  else (1 + ω) * s + ω * t

/-- The blueprint's magma on `ZMod 31 × M` with base operation `3x - 2y`. -/
def magma496 {M : Type v} [CommRing M] (ζ ω : M) (p q : ZMod 31 × M) : ZMod 31 × M :=
  (3 * p.1 - 2 * q.1, fiber496 ζ ω p.1 q.1 p.2 q.2)

end FiniteMagmaE677


