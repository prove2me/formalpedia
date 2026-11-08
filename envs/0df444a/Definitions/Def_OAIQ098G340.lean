-- Prove2me | Definitions.Def_OAIQ098G340
-- name    : OAIQ098G340
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:43:40.093027+00:00
-- url     : https://prove2.me/theorems/c6606c92-426d-4bed-94c4-9832b1520ed6
-- title:
--   Definitions bundle OAIQ098G340 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power73Expr`, `OAI.SharpPlanar.CachedData.power74Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020` and `OAIQ098G278` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column75_0_contains_g`, `OAI.SharpPlanar.CachedData.column75_1_contains_g`, `OAI.SharpPlanar.CachedData.column76_0_contains_g`, `OAI.SharpPlanar.CachedData.column76_1_contains_g`, `OAI.SharpPlanar.CachedData.power78_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm73_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U73.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U73.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G278

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers80
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
noncomputable def power73Expr (j : Fin 6) (i k : Fin 16) : CBox := (power72 j i k).mul (gridRows j i k).direct
noncomputable def power74Expr (j : Fin 6) (i k : Fin 16) : CBox := (power73 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


