-- Prove2me | Definitions.Def_OAIQ098G252
-- name    : OAIQ098G252
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:10:29.391203+00:00
-- url     : https://prove2.me/theorems/b1d7ad4b-38c0-4707-ba0a-712127dcea01
-- title:
--   Definitions bundle OAIQ098G252 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.column31_0Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns40.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G103` and `OAIQ098G251` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.tableTerm31_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U31.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U31.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G103
import Definitions.Def_OAIQ098G251

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
noncomputable def column31_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_0 j i k).mul (power31 j i k)
end SharpPlanar.CachedData

end OAI
end


