-- Prove2me | Definitions.Def_DelayedGamesMAO_Supplement_IsUndelayedRun
-- name    : DelayedGamesMAO_Supplement_IsUndelayedRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:53:38.373918+00:00
-- url     : https://prove2.me/theorems/620315db-f6a8-487f-b674-50fa84f13697
-- title:
--   An undelayed run $w_j=B[g_1,\dots,g_{j-1}]$ of a base learner
-- statement:
--   Let $B$ be a deterministic online learner that maps the list of gradients it has been fed to its next action. A sequence $(w_j)$ is an **undelayed run** of $B$ for $n$ rounds with gradients $(g_j)$ when, for every $j\in[n]$,
--
--   $$
--   w_j=B\big[g_1,\dots,g_{j-1}\big].
--   $$
--
--   Each gradient is fed back before the next action is chosen. The base-learner guarantees assumed in Theorem 4 are about such runs.
--
--   **Formalization Note** The gradient $g_j$ may depend on the actions (for example $g_j=\nabla f_j(w_j)$, or a player's loss gradient in self-play), so the run is a property of the action sequence.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §4, p.7 and App. B.2–B.3, pp.33–34

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO.Supplement

/-- **An undelayed run of a base learner `B` for `n` rounds**: `w_j = B[g_1, …, g_{j−1}]` for
`j ∈ [n]`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §4, p.7 and App. B.2–B.3, pp.33–34 (the undelayed online learner `B` of the BOLD reduction,
which receives the feedback of each round before choosing its next action).

**Formalization Note.** `B : List (E →L[ℝ] ℝ) → E` maps the gradients fed so far, in order, to
the next action; `g j` is the gradient of round `j` and may depend on `w` (e.g. `g_j = ∇f_j(w_j)`,
or a player's loss gradient in self-play), so the run is a predicate on `w`.
`List.range' 1 (j - 1) = [1, …, j − 1]`. -/
def IsUndelayedRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : List (E →L[ℝ] ℝ) → E) (g : ℕ → E →L[ℝ] ℝ) (n : ℕ) (w : ℕ → E) : Prop :=
  ∀ j ∈ Finset.Icc 1 n, w j = B ((List.range' 1 (j - 1)).map g)

end DelayedGamesMAO.Supplement


