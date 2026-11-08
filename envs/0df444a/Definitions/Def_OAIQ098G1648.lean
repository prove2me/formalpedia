-- Prove2me | Definitions.Def_OAIQ098G1648
-- name    : OAIQ098G1648
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T23:32:03.323955+00:00
-- url     : https://prove2.me/theorems/948a18b5-bc5f-44af-8266-25b58408f587
-- title:
--   Definitions bundle OAIQ098G1648 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.transformedJetList`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_ContactData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ContactData.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G016` of this split; the published statement `OAI.SharpPlanar.transformedJets_summable_g`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1649` and `OAIQ098G1650`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G016
import Theorems.Thm_OAI_SharpPlanar_transformedJets_summable_g

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
noncomputable def transformedJetList (p : CardinalData) : X :=
  ⟨transformedJets p,memℓp_gen (by simpa using transformedJets_summable_g p)⟩

end SharpPlanar

end OAI
end


