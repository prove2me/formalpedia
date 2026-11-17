-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_noisyCost
-- name    : NoPerfectRandComp_Supplement_noisyCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:18:45.253981+00:00
-- url     : https://prove2.me/theorems/77478f3b-ea4a-4f66-9ee0-dda2708a27cb
-- title:
--   Expected cost of a noisy algorithm
-- statement:
--   For a noisy algorithm $A$ and input $x$, the expected total cost: a noisy query of correlation $\gamma$ costs $\gamma^2$, and
--   $$
--   \mathbb E[\mathrm{cost}(A,x)] = \sum_{v}\Pr[v\text{ reached}]\cdot\mathrm{cost}(v),
--   $$
--   the sum over all nodes $v$ of $A$. Valued in $[0,\infty]$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4, p.11

import Mathlib
import Definitions.Def_NoPerfectRandComp_Supplement_reachProb
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- The expected total cost of the noisy algorithm `A` on input `x` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4, p.11):
a noisy query of correlation `γ` costs `γ²` (coins and stops cost nothing), and the expected total
is `Σ_v Pr[v reached] · cost(v)` over all nodes `v`. Valued in `ℝ≥0∞`. -/
noncomputable def noisyCost {ι : Type} (A : NoisyAlg ι) (x : ι → Bool) : ℝ≥0∞ :=
  ∑' s : List Bool, reachProb A x [] s * match A s with
    | NoisyAct.query _ γ => ENNReal.ofReal ((γ : ℝ) ^ 2)
    | _ => 0

end Supplement

end NoPerfectRandComp


