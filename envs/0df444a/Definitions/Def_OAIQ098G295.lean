-- Prove2me | Definitions.Def_OAIQ098G295
-- name    : OAIQ098G295
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:08:27.524919+00:00
-- url     : https://prove2.me/theorems/9b4cce8b-c1bc-4e24-98da-c8f2140e608a
-- title:
--   Definitions bundle OAIQ098G295 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column88_0Expr`, `OAI.SharpPlanar.CachedData.column88_1Expr`, `OAI.SharpPlanar.CachedData.power88`, `OAI.SharpPlanar.CachedData.power88_r5`, `OAI.SharpPlanar.CachedData.power89Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns90.lean), [`PlanarPacking_Certificate_Powers90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers90.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G292` and `OAIQ098G294` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column91_0_contains_g`, `OAI.SharpPlanar.CachedData.column91_1_contains_g`, `OAI.SharpPlanar.CachedData.power93_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm88_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U88.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U88.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G292
import Definitions.Def_OAIQ098G294

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers90
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
noncomputable def power88_r5 : Fin 16 → Fin 16 → CBox := ![power88_r5_0,power88_r5_1,power88_r5_2,power88_r5_3,power88_r5_4,power88_r5_5,power88_r5_6,power88_r5_7,power88_r5_8,power88_r5_9,power88_r5_10,power88_r5_11,power88_r5_12,power88_r5_13,power88_r5_14,power88_r5_15]
noncomputable def power88 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power88_r0,power88_r1,power88_r2,power88_r3,power88_r4,power88_r5]
noncomputable def power89Expr (j : Fin 6) (i k : Fin 16) : CBox := (power88 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns90
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
noncomputable def column88_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power88 j i k)
noncomputable def column88_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power88 j i k)
end SharpPlanar.CachedData

end OAI
end


