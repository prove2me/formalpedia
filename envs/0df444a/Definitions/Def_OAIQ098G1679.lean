-- Prove2me | Definitions.Def_OAIQ098G1679
-- name    : OAIQ098G1679
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T08:58:49.269184+00:00
-- url     : https://prove2.me/theorems/d8148128-290c-4953-bcaa-69c99d86379b
-- title:
--   Definitions bundle OAIQ098G1679 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.exactLeft`, `OAI.SharpPlanar.exactRight`, `OAI.SharpPlanar.normalizationConstant`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_NormalizedCandidate`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/NormalizedCandidate.lean), [`PlanarPacking_OriginIdentity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/OriginIdentity.lean).
--
--   **Imports.** It imports the published bundle `Def_PlanarPacking`; the bundles `OAIQ098G1651` and `OAIQ098G1678` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1688`; the statement `OAI.SharpPlanar.exactLeft_origin_positive_g`; the proof of `OAI.SharpPlanar.exactLeft_origin_positive_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_PlanarPacking
import Definitions.Def_OAIQ098G1651
import Definitions.Def_OAIQ098G1678

section
-- module Solutions.OAIQ098_PP.PlanarPacking_OriginIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality at the origin from triangular lattice contacts and Poisson summation -/

namespace SharpPlanar
noncomputable def exactLeft : SchwartzMap Plane ℝ := pairLeft exactData₁ exactData₂
noncomputable def exactRight : SchwartzMap Plane ℝ := pairRight exactData₁ exactData₂
end SharpPlanar

end OAI
end

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
noncomputable def normalizationConstant : ℝ := (b*exactLeft 0)⁻¹
end SharpPlanar

end OAI
end


