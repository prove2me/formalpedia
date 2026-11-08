-- Prove2me | Definitions.Def_OAIQ098G270
-- name    : OAIQ098G270
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:04:17.219211+00:00
-- url     : https://prove2.me/theorems/1ba472c7-3f4e-44be-a90f-758cd3604f48
-- title:
--   Definitions bundle OAIQ098G270 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column57_0Expr`, `OAI.SharpPlanar.CachedData.column57_1Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns60.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G104` and `OAIQ098G266` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.tableTerm57_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.wuminus_contains_g` and `OAI.SharpPlanar.Numerical.U57.wuplus_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G104
import Definitions.Def_OAIQ098G266

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns60
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
noncomputable def column57_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power57 j i k)
noncomputable def column57_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power57 j i k)
end SharpPlanar.CachedData

end OAI
end


