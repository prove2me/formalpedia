-- Prove2me | Definitions.Def_TightQLearning_window
-- name    : TightQLearning_window
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:25.638995+00:00
-- url     : https://prove2.me/theorems/0285cdbc-1134-4f88-b900-4566e4f0377f
-- title:
--   the index window $t/2\le i<t$
-- statement:
--   The set of natural numbers $i$ with $t/2\le i<t$, the range of the maxima in Lemmas 1, 2, 5 and (95). It is nonempty exactly when $t\ge2$.
--
--   **Formalization Note** The comparison $t/2\le i$ is written $t\le 2i$, so no truncated division occurs.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), Lemma 1, p.14

import Mathlib

namespace TightQLearning

/-- The index window `{i ∈ ℕ | t/2 ≤ i < t}` under the maxima of Lemmas 1, 2, 5 and (95)
(arXiv:2102.06548v4, pp.14, 25, 28). The comparison `t/2 ≤ i` is the real one, written `t ≤ 2 * i`
to avoid truncated division. The window is nonempty exactly when `t ≥ 2`. -/
def window (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun i => t ≤ 2 * i)

end TightQLearning


