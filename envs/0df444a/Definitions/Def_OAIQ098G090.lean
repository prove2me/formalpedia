-- Prove2me | Definitions.Def_OAIQ098G090
-- name    : OAIQ098G090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T09:00:52.385723+00:00
-- url     : https://prove2.me/theorems/9b435c8d-f73a-4bab-bea7-8f06664961dc
-- title:
--   Definitions bundle OAIQ098G090 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 definition and 1 instance. The definitions and types are `OAI.SharpPlanar.IntegerIntervals.PointBox.Check`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Intervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G021`, `OAIQ098G079`, `OAIQ098G088` and `OAIQ098G089` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.atomPoint0_contains_g`, `OAI.SharpPlanar.CachedData.atomPoint1_contains_g`, `OAI.SharpPlanar.CachedData.atomPoint2_contains_g`, `OAI.SharpPlanar.CachedData.atomPoint3_contains_g`, `OAI.SharpPlanar.CachedData.atomPoint4_contains_g`, `OAI.SharpPlanar.CachedData.atomPoint5_contains_g`, `OAI.SharpPlanar.CachedData.atomPoint6_contains_g`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_contains_g` and `OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G021
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G088
import Definitions.Def_OAIQ098G089

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

def PointBox.Check (a : RBox) : Prop :=
  (denBox a).GoodInv ∧ (lamDenBox a).GoodInv ∧
  ((directArgBox a).scale 1 8).NormCheck 1 ∧
  ((quarterArgBox a).scale 1 8).NormCheck 1
instance instDecidableCheck (a : RBox) : Decidable (PointBox.Check a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end SharpPlanar.IntegerIntervals

end OAI
end


