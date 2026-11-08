-- Prove2me | Definitions.Def_OAIQ098G016
-- name    : OAIQ098G016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:28:38.822333+00:00
-- url     : https://prove2.me/theorems/280ff004-a148-446f-b09f-dc4487aa0887
-- title:
--   Definitions bundle OAIQ098G016 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.transformedJets`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_ContactData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ContactData.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1648`; the statement `OAI.SharpPlanar.transformedJets_summable_g`; the proof of `OAI.SharpPlanar.transformedJets_summable_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G001

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ContactData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contact data for cardinal interpolation

The prescribed contacts and their Gaussian transforms give summable right hand sides for the interpolation equations.
-/

namespace SharpPlanar
noncomputable def transformedJets (p : CardinalData) (ni : Node×Bool) : ℝ :=
  if ni.2 then (D ni.1.val*K p 0 ni.1.val-K p 1 ni.1.val)/Q ni.1.val
  else -K p 0 ni.1.val/Q ni.1.val

end SharpPlanar

end OAI
end


