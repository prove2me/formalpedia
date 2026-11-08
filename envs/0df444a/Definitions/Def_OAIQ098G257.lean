-- Prove2me | Definitions.Def_OAIQ098G257
-- name    : OAIQ098G257
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:02:50.638567+00:00
-- url     : https://prove2.me/theorems/019c760f-99ec-4c22-8857-2e9c93925e5b
-- title:
--   Definitions bundle OAIQ098G257 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column37_0Expr`, `OAI.SharpPlanar.CachedData.column37_1Expr`, `OAI.SharpPlanar.CachedData.power37`, `OAI.SharpPlanar.CachedData.power37_r1`, `OAI.SharpPlanar.CachedData.power38Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns40.lean), [`PlanarPacking_Certificate_Powers40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G250` and `OAIQ098G256` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G640`, `OAIQ098G641`, `OAIQ098G642`, `OAIQ098G643`, `OAIQ098G644`, `OAIQ098G645`, `OAIQ098G646` and `OAIQ098G647`; the statement `OAI.SharpPlanar.CachedData.power37_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.power37_contains_g`, `OAI.SharpPlanar.CachedData.power38_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm37_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U37.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U37.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G250
import Definitions.Def_OAIQ098G256

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers40
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
noncomputable def power37_r1 : Fin 16 → Fin 16 → CBox := ![power37_r1_0,power37_r1_1,power37_r1_2,power37_r1_3,power37_r1_4,power37_r1_5,power37_r1_6,power37_r1_7,power37_r1_8,power37_r1_9,power37_r1_10,power37_r1_11,power37_r1_12,power37_r1_13,power37_r1_14,power37_r1_15]
noncomputable def power37 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power37_r0,power37_r1,power37_r2,power37_r3,power37_r4,power37_r5]
noncomputable def power38Expr (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns40
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
noncomputable def column37_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power37 j i k)
noncomputable def column37_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_1 j i k).mul (power37 j i k)
end SharpPlanar.CachedData

end OAI
end


