-- Prove2me | Definitions.Def_FocusSetRB_SingleArmMDP
-- name    : FocusSetRB_SingleArmMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:26.35399+00:00
-- url     : https://prove2.me/theorems/c8a6fbfe-f3c2-4e86-8c06-5aecdf246cb7
-- title:
--   Single-armed MDP $(\mathbb S,\mathbb A,P,r)$, $r_{\max}$ and $\beta=\min\{\alpha,1-\alpha\}$
-- statement:
--   An $N$-armed restless bandit consists of $N$ identical arms, each an MDP called the **single-armed MDP** $(\mathbb S,\mathbb A,P,r)$:
--
--   1. $\mathbb S$ is a finite state space;
--   2. $\mathbb A=\{0,1\}$ is the action space, action $1$ meaning that the arm is pulled;
--   3. $P(s,a,s')$ is the probability of moving from $s$ to $s'$ when action $a$ is taken in $s$, so $P(s,a,\cdot)$ is a probability vector on $\mathbb S$;
--   4. $r(s,a)$ is the expected reward for taking action $a$ in state $s$.
--
--   Two constants derived from the data appear in every bound of the paper:
--
--   $$
--   r_{\max}=\max_{s\in\mathbb S,\,a\in\mathbb A}|r(s,a)|,\qquad \beta=\min\{\alpha,1-\alpha\},
--   $$
--
--   where $\alpha\in(0,1)$ is the fraction of arms that must be pulled at every step.
--
--   **Formalization Note** Actions are booleans, `true` standing for $1$. $r_{\max}$ is a supremum over the finite set $\mathbb S\times\mathbb A$, hence a maximum.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, §3.1, p.5; β: §4.2, p.8 and Theorem 1, p.10

import Mathlib

namespace FocusSetRB

/-- The **single-armed MDP** `(𝕊, 𝔸, P, r)` of an `N`-armed restless bandit (Hong, Xie, Chen,
Wang, *Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward
Restless Bandits*, arXiv:2402.05689v4, §3.1, p.5): a finite state space `𝕊`, the action space
`𝔸 = {0, 1}` (action `1` = pull the arm), a transition kernel `P(s, a, s')` and a reward
function `r(s, a)`.

**Formalization Note.** The state space is the type parameter `S` (a `Fintype`); actions are
`Bool` with `true` = `1` (pull) and `false` = `0`. `P s a s'` is the probability of moving from
`s` to `s'` under action `a`, so it is nonnegative and sums to one over `s'` (the source writes
`P : 𝕊 × 𝔸 × 𝕊 → [0, 1]`, a transition kernel). -/
structure SingleArmMDP (S : Type*) [Fintype S] where
  /-- Transition probabilities `P(s, a, s')`. -/
  P : S → Bool → S → ℝ
  /-- Expected one-step reward `r(s, a)`. -/
  r : S → Bool → ℝ
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  P_sum_one : ∀ s a, ∑ s', P s a s' = 1

/-- `r_max = max_{s ∈ 𝕊, a ∈ 𝔸} |r(s, a)|` (arXiv:2402.05689v4, §3.1, p.5).

**Formalization Note.** Written as a real `⨆` over the finite type `S × Bool`; the family is
finite, hence bounded, so this is the maximum (and `0` if `S` is empty, which no theorem of the
mission allows). -/
noncomputable def rmax {S : Type*} [Fintype S] (M : SingleArmMDP S) : ℝ :=
  ⨆ p : S × Bool, |M.r p.1 p.2|

/-- `β = min{α, 1 − α}` (arXiv:2402.05689v4, §4.2, below (6), p.8, and Theorem 1, p.10). -/
noncomputable def beta (α : ℝ) : ℝ := min α (1 - α)

end FocusSetRB


