-- Prove2me | Definitions.Def_AndOrSched_key
-- name    : AndOrSched_key
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:50.047207+00:00
-- url     : https://prove2.me/theorems/13608aa3-e0ef-465a-a3de-ca24e1234279
-- title:
--   Sort keys of the $\beta$-schedule
-- statement:
--   For $0<\beta\le1$ and $\alpha=\beta/\Delta$, the sort key of $a\in A$ is its $\alpha$-point $t^\alpha_a$ and the sort key of $b\in B$ is its $\beta$-point $t^\beta_b$ (for LP (1); for LP (5) the $\alpha$- and $\beta$-intervals).
--
--   Using different values of $\alpha$ on $A$ and $B$ is what makes the resulting order feasible.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, "draw β … set α = β/∆ … compute tαa and tβb"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_alphaPoint
open scoped Classical NNReal

namespace AndOrSched

/-- The sort key of a job in the `β`-schedule (Happach, Schulz, arXiv:2001.07011v1, §2, p.7 and p.9): with `α = β/Δ`, the key of
`a ∈ A` is its `α`-point `t_a^α` and the key of `b ∈ B` is its `β`-point `t_b^β` (for LP (1)); for
LP (5) the same formula gives the `α`- and `β`-intervals `l_a^α`, `l_b^β`. -/
noncomputable def key (I : Instance) (x : I.N → ℕ → ℝ) (β : ℝ) : I.N → ℕ
  | Sum.inl a => alphaPoint x (Sum.inl a) (β / (delta I : ℝ))
  | Sum.inr b => alphaPoint x (Sum.inr b) β

end AndOrSched


