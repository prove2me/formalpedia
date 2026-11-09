-- Prove2me | Definitions.Def_OAIQ098G102
-- name    : OAIQ098G102
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:59:02.651959+00:00
-- url     : https://prove2.me/theorems/88cdf94a-5fcf-4cc8-ae2e-6baeed50f0ae
-- title:
--   Definitions bundle OAIQ098G102 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.AplusBox`, `OAI.SharpPlanar.Numerical.WplusBox`, `OAI.SharpPlanar.Numerical.defectplusBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_WCertificates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WCertificates.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G005`, `OAIQ098G047` and `OAIQ098G083` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G362` and `OAIQ098G368`; the proof of `OAI.SharpPlanar.Numerical.defectplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G005
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G083

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
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

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
noncomputable def WplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => RBox.rat (WplusInt i j) 10000
noncomputable def AplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((dEntries i j).neg)
noncomputable def defectplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((matrixMulBox WplusBox AplusBox i j).neg)
end SharpPlanar.Numerical

end OAI
end


