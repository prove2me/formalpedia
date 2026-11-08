-- Prove2me | Definitions.Def_OAIQ098G255
-- name    : OAIQ098G255
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:03:00.540224+00:00
-- url     : https://prove2.me/theorems/8d633c24-cc8a-4351-adb8-42c833c33633
-- title:
--   Definitions bundle OAIQ098G255 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column36_0Expr`, `OAI.SharpPlanar.CachedData.column36_1Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns40.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G103` and `OAIQ098G250` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column36_0_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm36_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry4_1_contains_g` and `OAI.SharpPlanar.Numerical.U36.entry5_1_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G103
import Definitions.Def_OAIQ098G250

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
noncomputable def column36_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power36 j i k)
noncomputable def column36_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power36 j i k)
end SharpPlanar.CachedData

end OAI
end


