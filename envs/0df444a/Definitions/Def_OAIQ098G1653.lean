-- Prove2me | Definitions.Def_OAIQ098G1653
-- name    : OAIQ098G1653
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:35:55.088886+00:00
-- url     : https://prove2.me/theorems/c0987037-74ba-4cfc-bf9c-aa04f5d10dd0
-- title:
--   Definitions bundle OAIQ098G1653 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 definition and 1 instance. The definitions and types are `OAI.SharpPlanar.bernsteinBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_BernsteinBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BernsteinBoxes.lean), [`PlanarPacking_Intervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G083` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.SharpPlanar.bernsteinBox_contains_g`; the proofs of `OAI.SharpPlanar.Bernstein12.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein13.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein13.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein13.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein13.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein15.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein15.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein15.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein15.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein16.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein16.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein16.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein16.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein19.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein19.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein19.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein19.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein1.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein1.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein1.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein21.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein21.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein21.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein21.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein24.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein24.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein24.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein24.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein25.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein25.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein25.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein25.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein27.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein27.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein27.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein27.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein28.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein28.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein28.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein28.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein31.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein31.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein31.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein31.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein33.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein33.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein33.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein33.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein36.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein36.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein37.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein37.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein37.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein37.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein39.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein39.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein39.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein39.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein3.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein40.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein40.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein40.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein40.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein4.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein4.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein4.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein4.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein7.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein7.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein7.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein7.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein9.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein9.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein9.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein9.N1_right.bound_g`, `OAI.SharpPlanar.bernsteinBox_contains_g`, `OAI.SharpPlanar.halfSign_0_N1_right_g` and `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
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

namespace SharpPlanar
namespace IntegerIntervals

instance instDecidableMulCheck (a b c : RBox) : Decidable (a.MulCheck b c) := inferInstanceAs (Decidable (_ ∧ _))

end IntegerIntervals
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BernsteinBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
open scoped BigOperators
def bernsteinBox (T : Fin 29 → RBox) (k : Fin 29) : RBox :=
  sumBox (fun r : Fin (k.val+1) => (T ⟨r.val,by omega⟩).scale (k.val.choose r.val) ((28).choose r.val))
end SharpPlanar

end OAI
end


