-- Prove2me | Definitions.Def_NisanRonen_Rounding_utility
-- name    : NisanRonen_Rounding_utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:19:46.994214+00:00
-- url     : https://prove2.me/theorems/601c540e-6900-4aae-8a9a-ac7d62190a93
-- title:
--   Utility of an agent under the rounding mechanism
-- statement:
--   Fix an allocation algorithm $f$ on rounded instances and a grid step $\delta$. Under a strategy profile with declarations $d$, allocation $x = x_f(d)$ and actual times $\tilde t$, the **rounding mechanism** pays agent $i$
--
--   $$
--   p^i(d, \tilde t) = c^i(d, \tilde t) + b^i(d, \tilde t), \qquad
--   c^i(d, \tilde t) = \sum_{j \in x^i} \tilde t_j, \qquad
--   b^i(d, \tilde t) = -\hat g\big(x(\hat d), \mathrm{corr}^i(x(d), d, \tilde t)\big),
--   $$
--
--   and agent $i$'s utility is quasi-linear, payment plus valuation:
--
--   $$
--   u^i = c^i(d, \tilde t) + b^i(d, \tilde t) + v^i(x, \tilde t), \qquad v^i(x, \tilde t) = -\sum_{j \in x^i} \tilde t_j .
--   $$
--
--   The compensation pays for the actual work; the bonus is computed from the rounded declarations of the others and the rounded actual times of agent $i$.
--
--   **Formalization Note** The three terms are kept separate. The allocations $x(\hat d)$ and $x(d)$ coincide because the algorithm reads only the rounded instance.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 34, p. 193 (PDF p. 28); Definitions 1 (quasi-linear utility, p. 171) and 20 (valuation, p. 187)

import Mathlib
import Definitions.Def_NisanRonen_Rounding_load
import Definitions.Def_NisanRonen_Rounding_roundedMakespan
import Definitions.Def_NisanRonen_Rounding_corr
import Definitions.Def_NisanRonen_Rounding_actualTimes

namespace NisanRonen.Rounding

/-- **Utility of agent `i` under the rounding mechanism** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 34,
p. 193, with the quasi-linear utility of Definition 1 and the valuation of Definition 20).
With declarations `d = (s l).decl`, allocation `x = allocOf f δ d` and actual times
`t̃ = actualTimes f δ s`, the utility is `c^i + b^i + v^i`, where

* the compensation is `c^i(d, t̃) = Σ_{j ∈ x^i} t̃_j`,
* the bonus is `b^i(d, t̃) = −ĝ(x(d̂), corr^i(x(d), d, t̃))` (rounded make-span of the corrected
  time vector),
* the valuation is `v^i(x, t̃) = −Σ_{j ∈ x^i} t̃_j`.

**Formalization Note** `x(d̂) = x(d)` because the allocation rule reads only the δ-unit
instance (`units`). The three terms are kept separate so the payment `c^i + b^i` of
Definition 34 is visible. -/
noncomputable def utility {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n)) (δ : ℝ)
    (s : Fin n → Strategy n k) (i : Fin n) : ℝ :=
  let d : Fin n → Fin k → ℝ := fun l => (s l).decl
  let x := allocOf f δ d
  let tt := actualTimes f δ s
  load x tt i + (- roundedMakespan δ x (corr i x d tt)) + (- load x tt i)

end NisanRonen.Rounding


