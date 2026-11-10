-- Prove2me | Definitions.Def_OAIQ098G369
-- name    : OAIQ098G369
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T19:21:19.823621+00:00
-- url     : https://prove2.me/theorems/f0c0b9da-3111-4db0-9c4c-52e72fada646
-- title:
--   Definitions bundle OAIQ098G369 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.U12.entries`, `OAI.SharpPlanar.Numerical.U12.wuminusBox`, `OAI.SharpPlanar.Numerical.U12.wuplusBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_WUCert12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert12.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G258`, `OAIQ098G263`, `OAIQ098G286`, `OAIQ098G326`, `OAIQ098G341` and `OAIQ098G362` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Numerical.U12.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U12.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G258
import Definitions.Def_OAIQ098G263
import Definitions.Def_OAIQ098G286
import Definitions.Def_OAIQ098G326
import Definitions.Def_OAIQ098G341
import Definitions.Def_OAIQ098G362

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert12
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

namespace SharpPlanar.Numerical.U12
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
noncomputable def wuplusBox := matrixMulBox WplusBox entries
noncomputable def wuminusBox := matrixMulBox WminusBox entries
end SharpPlanar.Numerical.U12

end OAI
end


