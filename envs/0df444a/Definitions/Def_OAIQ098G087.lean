-- Prove2me | Definitions.Def_OAIQ098G087
-- name    : OAIQ098G087
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:30.318503+00:00
-- url     : https://prove2.me/theorems/aa6a8dfb-5a9e-44d2-863a-351328bf4c7c
-- title:
--   Definitions bundle OAIQ098G087 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 2 definitions and 1 instance. The definitions and types are `OAI.SharpPlanar.IntegerIntervals.CBox.GoodInv`, `OAI.SharpPlanar.IntegerIntervals.CBox.inv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Intervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G031` and `OAIQ098G083` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G089` and `OAIQ098G092`; the statement `OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_g`; the proof of `OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G031
import Definitions.Def_OAIQ098G083

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

def CBox.inv (a : CBox) : CBox :=
  let d := (a.re.mul a.re).add (a.im.mul a.im)
  let di := d.inv
  ⟨a.re.mul di,a.im.neg.mul di⟩

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

def CBox.GoodInv (a : CBox) : Prop :=
  ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
    ((a.re.mul a.re).add (a.im.mul a.im)).inv
instance instDecidableGoodInv (a : CBox) : Decidable a.GoodInv := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end SharpPlanar.IntegerIntervals

end OAI
end


