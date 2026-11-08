-- Prove2me | Definitions.Def_OAIQ098G1692
-- name    : OAIQ098G1692
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T23:21:00.182131+00:00
-- url     : https://prove2.me/theorems/c050cb91-5c73-42d9-9f4e-66ae40f10779
-- title:
--   Definitions bundle OAIQ098G1692 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.signedHeadC`, `OAI.SharpPlanar.signedHeadD`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_TailHeadBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailHeadBounds.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1685` and `OAIQ098G1691` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SharpPlanar.exact_head_lower_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1685
import Definitions.Def_OAIQ098G1691

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailHeadBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def signedHeadC (a : Bool) (i : HeadNodeIndex) : ℝ :=
  (if a then 1 else -1)*headC (tableData a) i
noncomputable def signedHeadD (a : Bool) (i : HeadNodeIndex) : ℝ :=
  (if a then 1 else -1)*headD (tableData a) i
end SharpPlanar

end OAI
end


