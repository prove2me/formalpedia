-- Prove2me | Definitions.Def_DilatableEntropy_maxLogActions
-- name    : DilatableEntropy_maxLogActions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:49.155728+00:00
-- url     : https://prove2.me/theorems/ee00d097-f498-42d1-8644-aca15b1f111a
-- title:
--   $\max_{j\in J}\log|A_j|$
-- statement:
--   The quantity
--   $$
--   \max_{j\in J}\log|A_j|
--   $$
--   from the range bound of Theorem 6, the logarithm of the largest number of actions at a decision point.
--
--   **Formalization Note** Written as $\log\big(\max_{j}|A_j|\big)$; since $\log$ is increasing on $[1,\infty)$ and every $|A_j|\ge1$, this is $\max_j\log|A_j|$ whenever $J\neq\varnothing$. For $J=\varnothing$ (where the paper's maximum is over the empty set) the value is $\log 0=0$; then $Q=\{e_\varnothing\}$ and $\tilde\varphi\equiv0$ on $Q$.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Theorem 6, p.13

import Mathlib
import Definitions.Def_DilatableEntropy_SeqDecisionProblem

namespace DilatableEntropy

/-- `max_{j ∈ J} log |A_j|` (Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Theorem 6, p.13), written as the logarithm of the largest
action-set size.

**Formalization Note** Since `log` is monotone on `[1, ∞)` and every `|A_j| ≥ 1`, this equals
`max_j log |A_j|` whenever `J` is nonempty. For `J = ∅` the paper's maximum is over the empty
set; here the value is `log 0 = 0` (then `Q = {e_∅}` and every bound involving it is `0`). -/
noncomputable def maxLogActions (P : SeqDecisionProblem) : ℝ :=
  Real.log ((Finset.univ.sup fun j : P.J => Fintype.card (P.A j) : ℕ) : ℝ)

end DilatableEntropy


