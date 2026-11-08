-- Prove2me | Definitions.Def_OAIQ098G071
-- name    : OAIQ098G071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:03:58.136508+00:00
-- url     : https://prove2.me/theorems/d99076c0-a830-43ff-b5d4-98c1e704d70d
-- title:
--   Definitions bundle OAIQ098G071 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.IntegerBasis.coefficientBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_BasisIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G047` and `OAIQ098G059` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G078` and `OAIQ098G1693`; the statement `OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_g`; the proof of `OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G059

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def coefficientBox : ℕ → CBox
  | 0 => CBox.rat 5 1 0 1
  | 1 => ⟨RBox.rat (-1) 1,bBounds.scale 2 1⟩
  | 2 => ⟨RBox.rat 1 1,bBounds.scale 2 1⟩
  | 3 => CBox.rat (-2) 1 0 1
  | 4 => ⟨RBox.rat (-1) 2,bBounds⟩
  | 5 => ⟨RBox.rat (-1) 1,bBounds.scale (-2) 1⟩
  | 6 => CBox.rat 1 1 0 1
  | _ => CBox.rat 0 1 0 1

end SharpPlanar.IntegerBasis

end OAI
end


