-- Prove2me | Definitions.Def_MazurTransfer_OrderFortyNinePlaneTransferData
-- name    : MazurTransfer_OrderFortyNinePlaneTransferData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T14:36:13.226782+00:00
-- url     : https://prove2.me/theorems/c3582735-44a6-422c-a698-04734e066738
-- title:
--   Literal polynomial data for the order-49 plane-curve transfer
-- statement:
--   The fixed symmetric level-seven polynomial $G(s,B)$, together with the transfer coordinate polynomials $D(s,B),N_x(s,B),N_y(s,B)$ from the original rational map. The associated coordinates are $x=N_x/D$ and $y=N_y/D$. This module contains only literal rational polynomial functions. Nonvanishing of $D$ and $N_x$, the target curve equation, and the absence of noncuspidal rational solutions are separate theorem obligations. Named downstream consumer: the complete rational plane-curve obstruction.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: OrderSevenCorrespondence.lean and XZeroFortyNineTransfer.lean. Four complete pure data commands selected from Lean AST ranges. Private map helpers promoted by removing only their AST modifier token; signatures and values retained.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib

namespace MazurTorsion.Kubert

/-- The Fricke-twisted level-seven correspondence polynomial. -/
def orderSevenG7F (s B : ℚ) : ℚ :=
  -678223072849 * B ^ 6 - 678223072849 * s * B ^ 5 - 387556041628 * s * B ^ 6
  - 678223072849 * s ^ 2 * B ^ 4 - 387556041628 * s ^ 2 * B ^ 5 - 90957030178 * s ^ 2 * B ^ 6
  - 678223072849 * s ^ 3 * B ^ 3 - 387556041628 * s ^ 3 * B ^ 4 - 90957030178 * s ^ 3 * B ^ 5
  - 10976181104 * s ^ 3 * B ^ 6 - 678223072849 * s ^ 4 * B ^ 2 - 387556041628 * s ^ 4 * B ^ 3
  - 90957030178 * s ^ 4 * B ^ 4 - 10976181104 * s ^ 4 * B ^ 5 - 695893835 * s ^ 4 * B ^ 6
  - 678223072849 * s ^ 5 * B - 387556041628 * s ^ 5 * B ^ 2 - 90957030178 * s ^ 5 * B ^ 3
  - 10976181104 * s ^ 5 * B ^ 4 - 695893835 * s ^ 5 * B ^ 5 - 20706224 * s ^ 5 * B ^ 6
  - 678223072849 * s ^ 6 - 387556041628 * s ^ 6 * B - 90957030178 * s ^ 6 * B ^ 2
  - 10976181104 * s ^ 6 * B ^ 3 - 695893835 * s ^ 6 * B ^ 4 - 20706224 * s ^ 6 * B ^ 5
  - 196882 * s ^ 6 * B ^ 6 + s ^ 7 * B ^ 7

end MazurTorsion.Kubert

namespace MazurTorsion.XZeroFortyNine

/-- Numerator of the transfer ordinate. -/
 def mNY (s B : ℚ) : ℚ :=
  18990246039772 * B ^ 5 + 113941476238632 * s * B ^ 4 + 14727129581864 * s * B ^ 5
  + 18990246039772 * s ^ 2 * B ^ 3 + 49607173328384 * s ^ 2 * B ^ 4
  + 4318481606712 * s ^ 2 * B ^ 5 + 6976008749304 * s ^ 3 * B ^ 3
  + 8304772320600 * s ^ 3 * B ^ 4 + 619185745808 * s ^ 3 * B ^ 5 + 56970738119316 * s ^ 4 * B
  + 17052465831632 * s ^ 4 * B ^ 2 + 2657527142592 * s ^ 4 * B ^ 3
  + 686979805568 * s ^ 4 * B ^ 4 + 44527322924 * s ^ 4 * B ^ 5 + 941192 * s ^ 4 * B ^ 6
  + 56970738119316 * s ^ 5 + 28291591038844 * s ^ 5 * B + 5204323987576 * s ^ 5 * B ^ 2
  + 471168715332 * s ^ 5 * B ^ 3 + 32467359232 * s ^ 5 * B ^ 4 + 1399081908 * s ^ 5 * B ^ 5
  + 201684 * s ^ 5 * B ^ 6 + 5425784582792 * s ^ 6 + 2269971100964 * s ^ 6 * B
  + 369477625692 * s ^ 6 * B ^ 2 + 28224465696 * s ^ 6 * B ^ 3 + 966133588 * s ^ 6 * B ^ 4
  + 11025392 * s ^ 6 * B ^ 5 + 12348 * s ^ 6 * B ^ 6

/-- Numerator of the transfer abscissa. -/
 def mNX (s B : ℚ) : ℚ :=
  18990246039772 * B ^ 5 + 10076457082328 * s * B ^ 5 + 18990246039772 * s ^ 2 * B ^ 3
  + 3100448333024 * s ^ 2 * B ^ 4 + 2182968724272 * s ^ 2 * B ^ 5
  + 6976008749304 * s ^ 3 * B ^ 3 + 1138940203968 * s ^ 3 * B ^ 4 + 239539011152 * s ^ 3 * B ^ 5
  - 18990246039772 * s ^ 4 * B - 3875560416280 * s ^ 4 * B ^ 2 + 696019013536 * s ^ 4 * B ^ 3
  + 146887129480 * s ^ 4 * B ^ 4 + 13397397524 * s ^ 4 * B ^ 5 - 18990246039772 * s ^ 5
  - 8138676874188 * s ^ 5 * B - 1028209906360 * s ^ 5 * B ^ 2 + 3389702988 * s ^ 5 * B ^ 3
  + 7056116424 * s ^ 5 * B ^ 4 + 325181836 * s ^ 5 * B ^ 5 + 9604 * s ^ 5 * B ^ 6
  + 55365148804 * s ^ 6 * B + 19208316932 * s ^ 6 * B ^ 2 + 2398157216 * s ^ 6 * B ^ 3
  + 120001980 * s ^ 6 * B ^ 4 + 1824760 * s ^ 6 * B ^ 5 + 1372 * s ^ 6 * B ^ 6

/-- Its partial derivative in the second variable. -/
 def mGB (s B : ℚ) : ℚ :=
  -4069338437094 * B ^ 5 - 3391115364245 * s * B ^ 4 - 2325336249768 * s * B ^ 5
  - 2712892291396 * s ^ 2 * B ^ 3 - 1937780208140 * s ^ 2 * B ^ 4 - 545742181068 * s ^ 2 * B ^ 5
  - 2034669218547 * s ^ 3 * B ^ 2 - 1550224166512 * s ^ 3 * B ^ 3 - 454785150890 * s ^ 3 * B ^ 4
  - 65857086624 * s ^ 3 * B ^ 5 - 1356446145698 * s ^ 4 * B - 1162668124884 * s ^ 4 * B ^ 2
  - 363828120712 * s ^ 4 * B ^ 3 - 54880905520 * s ^ 4 * B ^ 4 - 4175363010 * s ^ 4 * B ^ 5
  - 678223072849 * s ^ 5 - 775112083256 * s ^ 5 * B - 272871090534 * s ^ 5 * B ^ 2
  - 43904724416 * s ^ 5 * B ^ 3 - 3479469175 * s ^ 5 * B ^ 4 - 124237344 * s ^ 5 * B ^ 5
  - 387556041628 * s ^ 6 - 181914060356 * s ^ 6 * B - 32928543312 * s ^ 6 * B ^ 2
  - 2783575340 * s ^ 6 * B ^ 3 - 103531120 * s ^ 6 * B ^ 4 - 1181292 * s ^ 6 * B ^ 5
  + 7 * s ^ 7 * B ^ 6

end MazurTorsion.XZeroFortyNine


