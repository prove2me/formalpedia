-- Prove2me | Definitions.Def_OAIQ098G298
-- name    : OAIQ098G298
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:06:50.44534+00:00
-- url     : https://prove2.me/theorems/40e9ca19-9c0d-4836-a77b-29359bda748f
-- title:
--   Definitions bundle OAIQ098G298 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column93_0Expr`, `OAI.SharpPlanar.CachedData.column93_1Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G104` and `OAIQ098G294` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.tableTerm93_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U93.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U93.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U93.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G104
import Definitions.Def_OAIQ098G294

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns100
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
noncomputable def column93_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power93 j i k)
noncomputable def column93_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power93 j i k)
end SharpPlanar.CachedData

end OAI
end


