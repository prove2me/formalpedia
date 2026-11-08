-- Prove2me | Definitions.Def_OAIQ098G264
-- name    : OAIQ098G264
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:02:52.285208+00:00
-- url     : https://prove2.me/theorems/62de895e-b4fa-48f1-b23a-b20b93bc6e68
-- title:
--   Definitions bundle OAIQ098G264 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power48`, `OAI.SharpPlanar.CachedData.power48_r4`, `OAI.SharpPlanar.CachedData.power49Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers50`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers50.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G258` and `OAIQ098G263` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G265`; the proofs of `OAI.SharpPlanar.CachedData.column51_0_contains_g`, `OAI.SharpPlanar.CachedData.column51_1_contains_g`, `OAI.SharpPlanar.CachedData.column52_0_contains_g`, `OAI.SharpPlanar.CachedData.column52_1_contains_g`, `OAI.SharpPlanar.CachedData.power54_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm49_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U49.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G258
import Definitions.Def_OAIQ098G263

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def power48_r4 : Fin 16 → Fin 16 → CBox := ![power48_r4_0,power48_r4_1,power48_r4_2,power48_r4_3,power48_r4_4,power48_r4_5,power48_r4_6,power48_r4_7,power48_r4_8,power48_r4_9,power48_r4_10,power48_r4_11,power48_r4_12,power48_r4_13,power48_r4_14,power48_r4_15]
noncomputable def power48 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power48_r0,power48_r1,power48_r2,power48_r3,power48_r4,power48_r5]
noncomputable def power49Expr (j : Fin 6) (i k : Fin 16) : CBox := (power48 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


