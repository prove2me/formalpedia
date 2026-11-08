-- Prove2me | Definitions.Def_OAIQ098G280
-- name    : OAIQ098G280
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:13:39.740601+00:00
-- url     : https://prove2.me/theorems/44fa27f1-7674-4c50-b244-ed1db4f173e1
-- title:
--   Definitions bundle OAIQ098G280 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column69_0Expr`, `OAI.SharpPlanar.CachedData.column69_1Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns70.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G104` and `OAIQ098G279` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.tableTerm69_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U69.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U69.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U69.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G104
import Definitions.Def_OAIQ098G279

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns70
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
noncomputable def column69_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_0 j i k).mul (power69 j i k)
noncomputable def column69_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp9_1 j i k).mul (power69 j i k)
end SharpPlanar.CachedData

end OAI
end


