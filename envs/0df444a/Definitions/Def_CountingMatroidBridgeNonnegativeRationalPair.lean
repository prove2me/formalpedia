-- Prove2me | Definitions.Def_CountingMatroidBridgeNonnegativeRationalPair
-- name    : CountingMatroidBridgeNonnegativeRationalPair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T21:31:12.249991+00:00
-- url     : https://prove2.me/theorems/9733eee2-3af8-4493-8ec0-b49491dceed7
-- title:
--   Unreduced nonnegative rational pairs
-- statement:
--   Represent a nonnegative rational by a natural numerator and a positive natural denominator. Pair addition, multiplication, division, and comparison are given by cross-products, so arithmetic can preserve exact rational values without reducing each intermediate fraction by a greatest common divisor.
-- source:
--   A local Lean 4.33.1 bridge for the fixed-machine implementation of the common-bases estimator.

import Mathlib

set_option autoImplicit false

namespace CountingMatroid.Bridge.RationalPair

/-- An unreduced representation of a nonnegative rational. Keeping the pair
unreduced lets a machine implement arithmetic with natural addition and
multiplication, without a gcd-normalization pass after every operation. -/
abbrev Pair := ℕ × ℕ

/-- Interpret the first component as numerator and the second as denominator. -/
def value (p : Pair) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

/-- Pair addition uses the cross-sum numerator and product denominator. -/
def add (x y : Pair) : Pair := (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

/-- Pair multiplication uses componentwise products. -/
def mul (x y : Pair) : Pair := (x.1 * y.1, x.2 * y.2)

/-- Rational division swaps the second pair and multiplies. -/
def div (x y : Pair) : Pair := (x.1 * y.2, x.2 * y.1)

end CountingMatroid.Bridge.RationalPair


