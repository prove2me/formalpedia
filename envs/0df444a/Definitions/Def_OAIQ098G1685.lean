-- Prove2me | Definitions.Def_OAIQ098G1685
-- name    : OAIQ098G1685
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:31:24.072223+00:00
-- url     : https://prove2.me/theorems/82c5ff88-2ebf-439e-9dc2-b6db9dd1deb7
-- title:
--   Definitions bundle OAIQ098G1685 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.headC`, `OAI.SharpPlanar.headD`, `OAI.SharpPlanar.headRational`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_TailHead`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailHead.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G001` and `OAIQ098G1684` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1692`; the statement `OAI.SharpPlanar.exact_head_lower_g`; the proof of `OAI.SharpPlanar.exact_sign_tail_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G1684

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def headC (p : CardinalData) : HeadNodeIndex → ℝ
  | none => p.c₀
  | some i => p.x (shortNode i,false)
noncomputable def headD (p : CardinalData) : HeadNodeIndex → ℝ
  | none => p.d₀
  | some i => p.x (shortNode i,true)
noncomputable def headRational (p : CardinalData) (s : ℝ) : ℝ :=
  p.C+∑ i,(headC p i/(s-headNodeNat i)^2+headD p i/(s-headNodeNat i))
end SharpPlanar

end OAI
end


