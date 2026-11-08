-- Prove2me | Definitions.Def_OAIQ098G1667
-- name    : OAIQ098G1667
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:50:54.70328+00:00
-- url     : https://prove2.me/theorems/2fc8b442-6fa5-47b0-a8bb-87688fd51903
-- title:
--   Definitions bundle OAIQ098G1667 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.Residual85.box0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Residual85`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Residual85.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G100`, `OAIQ098G1570` and `OAIQ098G1588` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SharpPlanar.Residual85.bound0_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G100
import Definitions.Def_OAIQ098G1570
import Definitions.Def_OAIQ098G1588

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual85
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

namespace SharpPlanar.Residual85
open IntegerIntervals IntegerBasis Numerical CachedData
noncomputable def box0_1 : RBox := (RBox.rat (-87) 10000000000).add ((tm1_85_1.realAnswer.add (((dBox 85).mul tm1_85_0.realAnswer).neg)).mul (qiBox 85))
end SharpPlanar.Residual85

end OAI
end


