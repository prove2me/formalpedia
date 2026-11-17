-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_reachProb
-- name    : NoPerfectRandComp_Supplement_reachProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:17:21.082476+00:00
-- url     : https://prove2.me/theorems/53f6517b-edc1-401b-bc18-8ee04976d975
-- title:
--   Reach probability of a node of a noisy algorithm
-- statement:
--   For a noisy algorithm $A$ run on input $x$, the probability of passing from the node with history $p$ to the node with history $p\,s$: each step along the way must be a query or a coin (a stop ends the run); a coin gives each outcome with probability $1/2$, and a query to $x_i$ with correlation $\gamma$ returns $x_i$ with probability $(1+\gamma)/2$ and $\neg x_i$ with probability $(1-\gamma)/2$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4, p.11

import Mathlib
import Definitions.Def_NoPerfectRandComp_Supplement_NoisyAlg
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- The probability that the noisy algorithm `A`, run on input `x` and currently at the node with
history `p`, goes on to the node with history `p ++ s` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4, p.11): each further
step must be a query or a coin (a stop ends the run); a coin gives each outcome with probability
`1/2`, and a query to `x_i` with correlation `γ` returns `x_i` with probability `(1 + γ)/2` and
`¬x_i` with probability `(1 − γ)/2`, independently of everything else. -/
noncomputable def reachProb {ι : Type} (A : NoisyAlg ι) (x : ι → Bool) :
    List Bool → List Bool → ℝ≥0∞
  | _, [] => 1
  | p, a :: s =>
      (match A p with
        | NoisyAct.stop _ => 0
        | NoisyAct.coin => 2⁻¹
        | NoisyAct.query i γ =>
            ENNReal.ofReal (if a = x i then (1 + (γ : ℝ)) / 2 else (1 - (γ : ℝ)) / 2)) *
      reachProb A x (p ++ [a]) s

end Supplement

end NoPerfectRandComp


