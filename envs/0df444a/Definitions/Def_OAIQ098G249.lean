-- Prove2me | Definitions.Def_OAIQ098G249
-- name    : OAIQ098G249
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:00:44.510182+00:00
-- url     : https://prove2.me/theorems/8a797616-a56a-405b-b10d-1b36b01beabb
-- title:
--   Definitions bundle OAIQ098G249 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column25_0Expr`, `OAI.SharpPlanar.CachedData.column25_1Expr`, `OAI.SharpPlanar.CachedData.power25`, `OAI.SharpPlanar.CachedData.power25_r3`, `OAI.SharpPlanar.CachedData.power26Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns30.lean), [`PlanarPacking_Certificate_Powers30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G242` and `OAIQ098G248` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G592`, `OAIQ098G593`, `OAIQ098G594`, `OAIQ098G595`, `OAIQ098G596`, `OAIQ098G597`, `OAIQ098G598` and `OAIQ098G599`; the proofs of `OAI.SharpPlanar.CachedData.power27_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm25_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U25.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G242
import Definitions.Def_OAIQ098G248

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers30
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
noncomputable def power25_r3 : Fin 16 → Fin 16 → CBox := ![power25_r3_0,power25_r3_1,power25_r3_2,power25_r3_3,power25_r3_4,power25_r3_5,power25_r3_6,power25_r3_7,power25_r3_8,power25_r3_9,power25_r3_10,power25_r3_11,power25_r3_12,power25_r3_13,power25_r3_14,power25_r3_15]
noncomputable def power25 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power25_r0,power25_r1,power25_r2,power25_r3,power25_r4,power25_r5]
noncomputable def power26Expr (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns30
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
noncomputable def column25_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power25 j i k)
noncomputable def column25_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_1 j i k).mul (power25 j i k)
end SharpPlanar.CachedData

end OAI
end


