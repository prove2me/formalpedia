-- Prove2me | Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
-- name    : MazurTransfer_OrderTwentySevenTrisectionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T12:42:50.229019+00:00
-- url     : https://prove2.me/theorems/060d3820-56d2-4a2d-b20f-a8163b430a0e
-- title:
--   Polynomial data for the order-27 trisection
-- statement:
--   This module defines the two-division value and the trisection polynomial of the marked $X_1(9)$ family over $\mathbb Q$, as literal ordinary Lean polynomial functions. It asserts no vanishing or classification result. Named consumer: constructing the third rational hauptmodul leg from a trisection point.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/Kubert/OrderTwentySevenTrisectionData.lean, unchanged complete source with original Apache-2.0 header. The unused macro registration is omitted from this platform interface; both polynomial definitions are retained as exact whole Lean AST commands.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib

namespace MazurTorsion.Kubert

/-- The two-division value `4ξ³ + b₂ξ² + 2b₄ξ + b₆` of the family. -/
def famTwoDivision (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f - 4) + 2 * ξ + 8) - 6 * ξ - 10) + ξ * (ξ + 8) + 8)
    + ξ * (-6 * ξ - 8) - 4) + ξ * (9 * ξ + 6) + 1) + ξ * (-10 * ξ - 4)) + ξ * (6 * ξ + 2))
    + ξ ^ 2 * (4 * ξ + 1)

/-- The trisection polynomial of the family: a point triples to an
abscissa-zero point only if this vanishes. -/
def trisectionPoly (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (
    f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 13) + 3 * ξ + 84) - 39 * ξ
    - 358) + ξ * (3 * ξ + 249) + 1126) + ξ * (-45 * ξ - 1044) - 2772) + ξ * (ξ * (ξ + 309) + 3231)
    + 5531) + ξ * (ξ * (-18 * ξ - 1341) - 7851) - 9143) + ξ * (ξ * (144 * ξ + 4200) + 15543) + 12696
    ) + ξ * (ξ * (-702 * ξ - 10182) - 25668) - 14932) + ξ * (ξ * (2426 * ξ + 19929) + 35898) + 14932
    ) + ξ * (ξ * (-6435 * ξ - 32373) - 42912) - 12696) + ξ * (ξ * (ξ * (12 * ξ + 13688) + 44478)
    + 44046) + 9143) + ξ * (ξ * (ξ * (-144 * ξ - 23955) - 52374) - 38838) - 5531) + ξ * (ξ * (ξ * (
    756 * ξ + 35022) + 53328) + 29313) + 2772) + ξ * (ξ * (ξ * (-2487 * ξ - 43163) - 47184) - 18783)
    - 1126) + ξ * (ξ * (ξ * (5853 * ξ + 45091) + 36297) + 10077) + 358) + ξ * (ξ * (ξ * (ξ * (-6 * ξ
    - 10476) - 40068) - 24159) - 4428) - 84) + ξ * (ξ * (ξ * (ξ * (90 * ξ + 14730) + 30372) + 13749)
    + 1539) + 13) + ξ * (ξ * (ξ * (ξ * (ξ * (-ξ - 426) - 16539) - 19699) - 6549) - 399) - 1) + ξ * (
    ξ * (ξ * (ξ * (ξ * (9 * ξ + 1164) + 14922) + 10962) + 2520) + 69)) + ξ * (ξ * (ξ * (ξ * (ξ * (
    -31 * ξ - 2166) - 10818) - 5227) - 738) - 6)) + ξ ^ 2 * (ξ * (ξ * (ξ * (65 * ξ + 2916) + 6279)
    + 2103) + 147)) + ξ ^ 2 * (ξ * (ξ * (ξ * (-123 * ξ - 2916) - 2916) - 681) - 15)) + ξ ^ 3 * (
    ξ * (ξ * (210 * ξ + 2166) + 1098) + 159)) + ξ ^ 3 * (ξ * (ξ * (ξ * (-6 * ξ - 297) - 1170) - 345)
    - 20)) + ξ ^ 4 * (ξ * (ξ * (18 * ξ + 321) + 444) + 90)) + ξ ^ 4 * (ξ * (ξ * (-24 * ξ - 243)
    - 114) - 15)) + ξ ^ 5 * (ξ * (24 * ξ + 122) + 24)) + ξ ^ 5 * (ξ * (-18 * ξ - 33) - 6))
    + ξ ^ 6 * (12 * ξ + 2)) + ξ ^ 6 * (-6 * ξ - 1)) + ξ ^ 9

end MazurTorsion.Kubert


