-- Prove2me | Definitions.Def_OAIQ098G300
-- name    : OAIQ098G300
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:06:48.976215+00:00
-- url     : https://prove2.me/theorems/073e1ddd-fe21-4c03-b35c-7c1ae2e56d9f
-- title:
--   Definitions bundle OAIQ098G300 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power96`, `OAI.SharpPlanar.CachedData.power96_r4`, `OAI.SharpPlanar.CachedData.power97Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G294` and `OAIQ098G299` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G301`; the proofs of `OAI.SharpPlanar.CachedData.column100_0_contains_g`, `OAI.SharpPlanar.CachedData.column100_1_contains_g`, `OAI.SharpPlanar.CachedData.column99_0_contains_g`, `OAI.SharpPlanar.CachedData.column99_1_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm97_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U97.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U97.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G294
import Definitions.Def_OAIQ098G299

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers100
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
noncomputable def power96_r4 : Fin 16 → Fin 16 → CBox := ![power96_r4_0,power96_r4_1,power96_r4_2,power96_r4_3,power96_r4_4,power96_r4_5,power96_r4_6,power96_r4_7,power96_r4_8,power96_r4_9,power96_r4_10,power96_r4_11,power96_r4_12,power96_r4_13,power96_r4_14,power96_r4_15]
noncomputable def power96 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power96_r0,power96_r1,power96_r2,power96_r3,power96_r4,power96_r5]
noncomputable def power97Expr (j : Fin 6) (i k : Fin 16) : CBox := (power96 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


