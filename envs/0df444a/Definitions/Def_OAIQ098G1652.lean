-- Prove2me | Definitions.Def_OAIQ098G1652
-- name    : OAIQ098G1652
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T08:57:32.741305+00:00
-- url     : https://prove2.me/theorems/10841733-211c-4431-874e-b333796b563f
-- title:
--   Definitions bundle OAIQ098G1652 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.H₁`, `OAI.SharpPlanar.H₂`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_ExactJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ExactJets.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1644` and `OAIQ098G1651` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.exactLeft_origin_positive_g`, `OAI.SharpPlanar.exact_sign_tail_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g` and `OAI.sharp_fourier_certificate`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1644
import Definitions.Def_OAIQ098G1651

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Jets of the exact cardinal interpolants

The exact interpolation equations give value and derivative contacts on the triangular shell radii.
-/

namespace SharpPlanar
noncomputable def H₁ (s : ℝ) : ℝ := cardinal exactData₁ s+K exactData₂ 0 s
noncomputable def H₂ (s : ℝ) : ℝ := cardinal exactData₂ s+K exactData₁ 0 s
end SharpPlanar

end OAI
end


