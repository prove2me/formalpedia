-- Prove2me | Definitions.Def_OAIQ098G293
-- name    : OAIQ098G293
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:06:38.871239+00:00
-- url     : https://prove2.me/theorems/c9f3bc73-624e-44bc-af9d-6f0d17a49370
-- title:
--   Definitions bundle OAIQ098G293 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column85_0Expr`, `OAI.SharpPlanar.CachedData.column85_1Expr`, `OAI.SharpPlanar.CachedData.power85`, `OAI.SharpPlanar.CachedData.power85_r1`, `OAI.SharpPlanar.CachedData.power86Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns90.lean), [`PlanarPacking_Certificate_Powers90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers90.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G286` and `OAIQ098G292` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.SharpPlanar.CachedData.power85_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.power85_contains_g`, `OAI.SharpPlanar.CachedData.power86_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm85_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U85.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U85.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G286
import Definitions.Def_OAIQ098G292

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
noncomputable def power85_r1 : Fin 16 → Fin 16 → CBox := ![power85_r1_0,power85_r1_1,power85_r1_2,power85_r1_3,power85_r1_4,power85_r1_5,power85_r1_6,power85_r1_7,power85_r1_8,power85_r1_9,power85_r1_10,power85_r1_11,power85_r1_12,power85_r1_13,power85_r1_14,power85_r1_15]
noncomputable def power85 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power85_r0,power85_r1,power85_r2,power85_r3,power85_r4,power85_r5]
noncomputable def power86Expr (j : Fin 6) (i k : Fin 16) : CBox := (power85 j i k).mul (gridRows j i k).direct
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
noncomputable def column85_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power85 j i k)
noncomputable def column85_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_1 j i k).mul (power85 j i k)
end SharpPlanar.CachedData

end OAI
end


