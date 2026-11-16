-- Prove2me | Definitions.Def_DelayedGamesMAO_Supplement_IsBoldRun
-- name    : DelayedGamesMAO_Supplement_IsBoldRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:53:20.45976+00:00
-- url     : https://prove2.me/theorems/a1075160-eeff-4214-8b7e-0aa5a4c77fa6
-- title:
--   A run of the refined BOLD reduction (Algorithm 2)
-- statement:
--   Let $B$ be a deterministic undelayed online learner on a domain: given the gradients it has been fed so far, in order, it returns its next action. The refined BOLD reduction runs a fresh copy of $B$ for every instance index. A sequence of actions $(w_t)$ is a **run of the reduction** over rounds $1,\dots,T$ under delays $(d_s)$ with gradients $(g_t)$ when, for every $t\in[T]$,
--
--   $$
--   w_t=B\big[g_{s_1},\dots,g_{s_m}\big],\qquad s_1<\dots<s_m \text{ the rounds } s\in[t-1] \text{ with } i_s=i_t .
--   $$
--
--   Round $t$ is thus played by instance $B_{i_t}$ with its own local history.
--
--   **Formalization Note** The gradient $g_t$ may depend on the actions (in Theorem 4(i) $g_t=\nabla f_t(w_t)$; in a game it is a player's loss gradient at the current pair of actions), so a run is a property of the action sequence, which it determines on $[T]$ round by round.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), App. B.1, Algorithm 2, p.33

import Mathlib
import Definitions.Def_DelayedGamesMAO_Supplement_boldRounds

set_option autoImplicit false

namespace DelayedGamesMAO.Supplement

/-- **A run of the refined BOLD reduction (Algorithm 2) with base learner `B`** over rounds
`1, …, T` under delays `d`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), App. B.1, Algorithm 2, p.33.

`B : List (E →L[ℝ] ℝ) → E` is a deterministic undelayed online learner: `B ℓ` is its action
after it has been fed the gradients `ℓ` (in feeding order; its local round counter is the length
of `ℓ`). Each instance is a fresh copy of `B`. Round `t` plays `w_t` = the action of instance
`B_{i_t}` given its local history, the gradients `g_s` of the earlier rounds `s` with
`i_s = i_t`, in increasing order of `s` (`boldRounds`).

**Formalization Note.** `g t` is the gradient of round `t` (in Theorem 4(i) `g_t = ∇f_t(w_t)`,
in Theorem 4(ii) a player's loss gradient at `(x_t, y_t)`); it may depend on `w`, so the run is a
predicate on the action sequence `w`, which it determines on `[T]` by induction. -/
def IsBoldRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : List (E →L[ℝ] ℝ) → E) (d : ℕ → ℕ) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) (w : ℕ → E) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, w t = B ((boldRounds d t).map g)

end DelayedGamesMAO.Supplement


