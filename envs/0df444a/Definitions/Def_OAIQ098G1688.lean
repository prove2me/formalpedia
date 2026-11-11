-- Prove2me | Definitions.Def_OAIQ098G1688
-- name    : OAIQ098G1688
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T09:00:23.732232+00:00
-- url     : https://prove2.me/theorems/10bcb689-d2e6-40dd-8151-2e3adbd0eb78
-- title:
--   Definitions bundle OAIQ098G1688 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.normalizedCandidate`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_NormalizedCandidate`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/NormalizedCandidate.lean).
--
--   **Imports.** It imports the published bundle `Def_PlanarPacking`; the bundles `OAIQ098G014` and `OAIQ098G1679` of this split; the published statement `OAI.SharpPlanar.scaleFactor_pos_g`.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.normalizedCandidate_fourier_g` and `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g`; the proofs of `OAI.SharpPlanar.normalizedCandidate_fourier_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g` and `OAI.sharp_fourier_certificate`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_PlanarPacking
import Definitions.Def_OAIQ098G014
import Definitions.Def_OAIQ098G1679
import Theorems.Thm_OAI_SharpPlanar_scaleFactor_pos_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NormalizedCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization of the radial Schwartz Fourier pair -/

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def normalizedCandidate : SchwartzMap Plane ℝ :=
  normalizationConstant • dilateSchwartz exactLeft scaleFactor scaleFactor_pos_g.ne'
end SharpPlanar

end OAI
end


