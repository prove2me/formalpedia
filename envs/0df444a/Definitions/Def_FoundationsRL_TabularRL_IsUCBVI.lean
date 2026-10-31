-- Prove2me | Definitions.Def_FoundationsRL_TabularRL_IsUCBVI
-- name    : FoundationsRL_TabularRL_IsUCBVI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:18.515098+00:00
-- url     : https://prove2.me/theorems/daf351fe-5e5b-4b3c-b318-21b82b266ce2
-- title:
--   The UCB-VI learner with bonus (5.27), any tie-breaking rule
-- statement:
--   **UCB-VI** (Upper Confidence Bound Value Iteration) is the following learner for $T$ episodes in an unknown tabular MDP with known rewards $r$. In episode $t$, with $n^t_h(s,a)$ and $n^t_h(s,a,s')$ the numbers of earlier episodes whose layer-$h$ state-action pair was $(s,a)$ (and whose next state was $s'$), and $\widehat P^t_h(s'\mid s,a)=n^t_h(s,a,s')/n^t_h(s,a)$, it computes by backward induction, from $\bar Q^t_{H+1}\equiv0$,
--
--   $$
--   \bar Q^t_h(s,a)=\Big\{r_h(s,a)+\mathbb E_{s'\sim\widehat P^t_h(\cdot\mid s,a)}\bar V^t_{h+1}(s')+b^t_{h,\delta}(s,a)\Big\}\wedge1,\qquad \bar V^t_h(s)=\max_a\bar Q^t_h(s,a),
--   $$
--
--   with the bonus
--
--   $$
--   b^t_{h,\delta}(s,a)=2\sqrt{\frac{\log(2SAHT/\delta)}{n^t_h(s,a)}},
--   $$
--
--   and plays the deterministic policy $\widehat\pi^t_h(s)\in\arg\max_a\bar Q^t_h(s,a)$. The predicate says that a history-dependent learner is UCB-VI for some tie-breaking rule in the $\arg\max$.
--
--   This is the algorithm of Theorem 1; its optimism comes from the bonus and its consistency from the empirical model.
--
--   **Formalization Note** The value iteration is the published `ucbQ` of `FoundationsRL_RLBasics_UCBVI_v2`, which takes the MDP as an argument but never reads it (only the known rewards and the history). An unvisited pair ($n^t_h(s,a)=0$, bonus $+\infty$) gets the clipped value $1$. The terminal value is $\bar Q^t_{H+1}\equiv0$ as in (5.29), not the algorithm box's misprinted $\bar V^t_{H+1}\equiv1$. The tie-breaking selector is arbitrary and may depend on the history.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, algorithm box UCB-VI and Eqs. (5.25)–(5.26), p. 89; Eq. (5.27), p. 90

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI_v2

namespace FoundationsRL.TabularRL

open FoundationsRL.RLBasics

/-- `learner` is UCB-VI (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, algorithm box "UCB-VI", p. 89, with the bonus (5.27),
p. 90) with known rewards `r`, confidence parameter `δ` and horizon `T` episodes: in every
episode, given the list `hist` of the trajectories collected so far, it plays the deterministic
policy `π̂^t_h(s) ∈ arg max_a Q̄^t_h(s,a)`, where `Q̄^t = ucbQ M r δ T hist` is the optimistic
value iteration (5.26) on the empirical transitions (5.25) with bonus
`b^t_{h,δ}(s,a) = 2√(log(2SAHT/δ)/n^t_h(s,a))`.

**Formalization Note.** `ucbQ`, `countSA`, `estExp`, `bonus`, `Learner`, `detPolicy` are the
published definitions of `FoundationsRL_RLBasics_UCBVI_v2` and `FoundationsRL_RLBasics_Core`.
`ucbQ` takes the MDP `M` as an argument but its body never reads it: the algorithm uses only the
known rewards `r` and the history. An unvisited pair (`n^t_h(s,a) = 0`, bonus `+∞` in the book)
gets the clipped value `1`; `Q̄^t_{H+1} ≡ 0` (the analysis' (5.29), not the box's misprinted
`V̄^t_{H+1} ≡ 1`). Ties in the `arg max` are broken by an arbitrary, possibly history-dependent,
selector `sel`: every tie-breaking rule is UCB-VI. -/
def IsUCBVI {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    {H : ℕ} (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ) (δ : ℝ) (T : ℕ)
    (learner : Learner S A H) : Prop :=
  ∃ sel : List (Trajectory S A H) → ℕ → S → A,
    (∀ hist h s, IsArgmax (ucbQ M r δ T hist h s) (sel hist h s)) ∧
    ∀ hist, learner hist = detPolicy (sel hist)

end FoundationsRL.TabularRL


