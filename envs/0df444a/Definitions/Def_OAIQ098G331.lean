-- Prove2me | Definitions.Def_OAIQ098G331
-- name    : OAIQ098G331
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:10:10.251208+00:00
-- url     : https://prove2.me/theorems/907533f0-5f5f-44a7-90b9-bff89be0a805
-- title:
--   Definitions bundle OAIQ098G331 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power54`, `OAI.SharpPlanar.CachedData.power54_r4`, `OAI.SharpPlanar.CachedData.power55Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers60.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G328` and `OAIQ098G330` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.SharpPlanar.CachedData.power54_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.column60_0_contains_g`, `OAI.SharpPlanar.CachedData.column60_1_contains_g`, `OAI.SharpPlanar.CachedData.power54_contains_g`, `OAI.SharpPlanar.CachedData.power61_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm55_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm57_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U55.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U57.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.wuminus_contains_g` and `OAI.SharpPlanar.Numerical.U57.wuplus_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G328
import Definitions.Def_OAIQ098G330

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers60
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
noncomputable def power54_r4 : Fin 16 → Fin 16 → CBox := ![power54_r4_0,power54_r4_1,power54_r4_2,power54_r4_3,power54_r4_4,power54_r4_5,power54_r4_6,power54_r4_7,power54_r4_8,power54_r4_9,power54_r4_10,power54_r4_11,power54_r4_12,power54_r4_13,power54_r4_14,power54_r4_15]
noncomputable def power54 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power54_r0,power54_r1,power54_r2,power54_r3,power54_r4,power54_r5]
noncomputable def power55Expr (j : Fin 6) (i k : Fin 16) : CBox := (power54 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


