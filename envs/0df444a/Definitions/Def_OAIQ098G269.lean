-- Prove2me | Definitions.Def_OAIQ098G269
-- name    : OAIQ098G269
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:12:11.295892+00:00
-- url     : https://prove2.me/theorems/9c5706c7-7921-46bb-b710-17a7d00d4bd8
-- title:
--   Definitions bundle OAIQ098G269 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.column55_1Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns60.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G105` and `OAIQ098G266` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.tableTerm55_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry4_1_contains_g` and `OAI.SharpPlanar.Numerical.U55.entry5_1_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G105
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
noncomputable def column55_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp7_1 j i k).mul (power55 j i k)
end SharpPlanar.CachedData

end OAI
end


