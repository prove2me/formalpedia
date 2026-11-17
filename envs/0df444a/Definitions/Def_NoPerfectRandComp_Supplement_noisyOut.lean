-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_noisyOut
-- name    : NoPerfectRandComp_Supplement_noisyOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:18:05.044357+00:00
-- url     : https://prove2.me/theorems/f9b06399-3203-4486-8a15-44bf96957745
-- title:
--   Output probability of a noisy algorithm
-- statement:
--   For a noisy algorithm $A$, input $x$ and bit $b$, the probability that $A$ halts on $x$ with output $b$: the sum, over all histories at which $A$ stops with output $b$, of the probability of reaching that history.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4, p.11

import Mathlib
import Definitions.Def_NoPerfectRandComp_Supplement_reachProb
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- The probability that the noisy algorithm `A` halts on input `x` with output `b`
(Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4, p.11): the total probability of the histories at which `A` stops with `b`. -/
noncomputable def noisyOut {ι : Type} (A : NoisyAlg ι) (x : ι → Bool) (b : Bool) : ℝ≥0∞ :=
  ∑' s : List Bool, match A s with
    | NoisyAct.stop b' => if b' = b then reachProb A x [] s else 0
    | _ => 0

end Supplement

end NoPerfectRandComp


