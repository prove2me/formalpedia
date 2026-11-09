-- Prove2me | Definitions.Def_OAIQ098G368
-- name    : OAIQ098G368
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T03:47:54.789386+00:00
-- url     : https://prove2.me/theorems/36fb4f42-6266-4f64-beb0-2894fabb8710
-- title:
--   Definitions bundle OAIQ098G368 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.U100.entries`, `OAI.SharpPlanar.Numerical.U100.wuminusBox`, `OAI.SharpPlanar.Numerical.U100.wuplusBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_WUCert100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G076`, `OAIQ098G102`, `OAIQ098G274`, `OAIQ098G292`, `OAIQ098G319`, `OAIQ098G322`, `OAIQ098G336` and `OAIQ098G347` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Numerical.U100.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U100.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G102
import Definitions.Def_OAIQ098G274
import Definitions.Def_OAIQ098G292
import Definitions.Def_OAIQ098G319
import Definitions.Def_OAIQ098G322
import Definitions.Def_OAIQ098G336
import Definitions.Def_OAIQ098G347

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert100
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

namespace SharpPlanar.Numerical.U100
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
end SharpPlanar.Numerical.U100

end OAI
end


