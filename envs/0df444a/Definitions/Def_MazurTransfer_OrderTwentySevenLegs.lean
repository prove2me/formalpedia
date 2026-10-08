-- Prove2me | Definitions.Def_MazurTransfer_OrderTwentySevenLegs
-- name    : MazurTransfer_OrderTwentySevenLegs
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T11:56:33.80248+00:00
-- url     : https://prove2.me/theorems/f0099bc1-cc74-412f-b184-e04ff14dc5c4
-- title:
--   The first two rational legs of the order-27 tower
-- statement:
--   This module defines the Fricke-twisted $X_0(9)$ correspondence polynomial and the numerators and denominators of the first two hauptmodul legs on the $X_1(9)$ family. It contains only five polynomial functions over $\mathbb Q$. The named consumers are the impossibility of a third rational leg and the order-27 trisection transfer. It asserts no classification theorem.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, MazurTorsion/Kubert/OrderTwentySevenLegs.lean: orderNineG9F, a1legN, a1legD, a2legN, a2legD. Original Apache-2.0 headers retained; five complete declarations selected from Lean AST ranges.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib

/-! Structural boundary: the Fricke-twisted X0(9) polynomial and the first
two rational functions on the X1(9) family. Named downstream consumer:
MazurTransfer.order_twenty_seven_legs_chain_impossible and the order-27
trisection transfer. No arithmetic classification is asserted here.
Source: user WIP commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. -/

namespace MazurTorsion.Kubert

/-- The Fricke-twisted `X₀(9)` correspondence polynomial. -/
def orderNineG9F (s B : ℚ) : ℚ :=
  s ^ 2 * B ^ 3 + 36 * s ^ 2 * B ^ 2 + 270 * s ^ 2 * B - s ^ 3 +
    729 * s * B ^ 2 + 26244 * s * B + 531441 * B

/-- Numerator of the first hauptmodul leg. -/
def a1legN (f : ℚ) : ℚ :=
  (f ^ 2 - f + 1) ^ 3 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1)

/-- Denominator of the first hauptmodul leg. -/
def a1legD (f : ℚ) : ℚ := f ^ 3 * (f - 1) ^ 3

/-- Numerator of the second hauptmodul leg. -/
def a2legN (f : ℚ) : ℚ := (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3

/-- Denominator of the second hauptmodul leg. -/
def a2legD (f : ℚ) : ℚ := f * (f - 1) * (f ^ 2 - f + 1) ^ 3

end MazurTorsion.Kubert


