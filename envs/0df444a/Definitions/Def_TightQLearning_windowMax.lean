-- Prove2me | Definitions.Def_TightQLearning_windowMax
-- name    : TightQLearning_windowMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:13.628093+00:00
-- url     : https://prove2.me/theorems/e458416b-f4e0-4be8-9499-1f7c427e2dc5
-- title:
--   $\max_{t/2\le i<t}$ — the maximum over the window
-- statement:
--   For $t\ge2$ and a real sequence $f$, this is $\max_{t/2\le i<t}f(i)$, a genuine maximum over a finite nonempty set.
--
--   **Formalization Note** The assumption $t\ge2$ is an argument of the definition. For $t=1$ the window is empty and the printed maximum is undefined, so no default value can enter a statement.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), Lemma 1, p.14; (95), p.28

import Mathlib
import Definitions.Def_TightQLearning_window

namespace TightQLearning

/-- `max_{t/2 ≤ i < t} f(i)` (arXiv:2102.06548v4, Lemmas 1, 2, 5 and (95)), a genuine maximum over
the finite nonempty window.

**Formalization Note.** The argument `2 ≤ t` is what makes the window nonempty: for `t = 1` the
window is empty and the page's maximum is undefined. -/
noncomputable def windowMax (t : ℕ) (ht : 2 ≤ t) (f : ℕ → ℝ) : ℝ :=
  (window t).sup' ⟨t - 1, by
    simp only [window, Finset.mem_filter, Finset.mem_range]
    omega⟩ f

end TightQLearning


