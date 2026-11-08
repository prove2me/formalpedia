-- Prove2me | Definitions.Def_OAIQ098G335
-- name    : OAIQ098G335
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:11:18.094751+00:00
-- url     : https://prove2.me/theorems/0f5d982e-ddc3-4389-b61b-5d63a8ba2412
-- title:
--   Definitions bundle OAIQ098G335 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power62Expr`, `OAI.SharpPlanar.CachedData.power64Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers70.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020` and `OAIQ098G271` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.column67_0_contains_g`, `OAI.SharpPlanar.CachedData.column67_1_contains_g`, `OAI.SharpPlanar.CachedData.power62_contains_g`, `OAI.SharpPlanar.CachedData.power69_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm64_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U64.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U64.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G271

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers70
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
noncomputable def power62Expr (j : Fin 6) (i k : Fin 16) : CBox := (power61 j i k).mul (gridRows j i k).direct
noncomputable def power64Expr (j : Fin 6) (i k : Fin 16) : CBox := (power63 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


