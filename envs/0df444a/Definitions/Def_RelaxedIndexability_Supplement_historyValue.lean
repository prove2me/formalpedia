-- Prove2me | Definitions.Def_RelaxedIndexability_Supplement_historyValue
-- name    : RelaxedIndexability_Supplement_historyValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:00:21.948361+00:00
-- url     : https://prove2.me/theorems/7a045590-2528-4498-a7bb-6a7f55520827
-- title:
--   Value of a history-dependent single-arm policy on the belief process
-- statement:
--   Fix one arm with states $0,\dots,K-1$, transition matrix $\mathbf P$ with rows $p_0,\dots,p_{K-1}$, a discount factor $\beta$, an **active reward** $r_1(x)$ and a **passive reward** $r_0(x)$ that depend on the current belief $x$.
--
--   A **single-arm policy** $\pi$ chooses the action of each slot (active or passive) from the history of the slots so far: for each past slot, either the state that was observed (an active slot) or the fact that nothing was observed (a passive slot). It may therefore depend on time and on all past observations.
--
--   The belief evolves as in (4): after an active slot in which state $k$ was observed (which happens with probability $x_k$), the next belief is $p_k$; after a passive slot it is $\mathcal T^1(x)=x\mathbf P$. The $n$-horizon value is defined recursively, with value $0$ at horizon $0$:
--
--   $$
--   V^\pi_{n+1}(x)=\begin{cases} r_1(x)+\beta\sum_{k}x_k\,V^{\pi_k}_n(p_k), & \pi \text{ active now},\\ r_0(x)+\beta\,V^{\pi_\emptyset}_n(x\mathbf P), & \pi \text{ passive now},\end{cases}
--   $$
--
--   where $\pi_k$ (respectively $\pi_\emptyset$) is the continuation of $\pi$ after a first slot in which $k$ was observed (respectively nothing was observed). The **value** of $\pi$ from $x$ is $\lim_{n\to\infty}V^\pi_n(x)$, the expected total discounted reward $\mathbb E_\pi[\sum_{t\ge1}\beta^{t-1}r_t\mid\omega(1)=x]$.
--
--   This is the policy-evaluation object of the single-armed bandit with subsidy; the optimal value, the passive times and the passive sets of the companion theorems are built from it.
--
--   **Formalization Note** A policy is a function `List (Option (Fin K)) → Bool` on histories listed oldest first (`some k`: active and $k$ observed; `none`: passive; `true`: active). Policies are deterministic and are chosen for a given initial belief. The limit is `limUnder`, which is unspecified for a divergent sequence; for $0<\beta<1$, a row-stochastic $\mathbf P$, beliefs in the simplex and bounded rewards the sequence converges.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (4), p.7; (11), p.9; single-arm policies, p.ec1

import Mathlib

open Filter Matrix

namespace RelaxedIndexability.Supplement

variable {K : ℕ}

/-- **A single-arm policy** (Liu, *Relaxed Indexability and Index Policy for Partially Observable
Restless Bandits*, arXiv:2107.11939v4, §2.2, pp.8–10, and the set of single-arm policies on p.ec1):
a rule choosing the action of the current slot (`true` = active, `false` = passive) from everything
known so far.

**Formalization Note.** A history lists the past slots oldest first: `some k` is an active slot in
which state `k` was observed, `none` a passive slot. Its length gives the current time, so the rule
may depend on time. The policy is chosen for a given initial belief, so it may depend on that belief
as well. Policies are deterministic. -/
abbrev Policy (K : ℕ) := List (Option (Fin K)) → Bool

/-- **The `n`-horizon value of a history-dependent policy on the belief process (4)**
(Liu, arXiv:2107.11939v4, (4), p.7, and (11), p.9): the expected discounted sum of the rewards of
the first `n` slots, started at belief `x`.

* If the policy is active now, the expected reward is `rAct x`, state `k` is observed with
  probability `x k`, the next belief is `p_k = P k` and the history gains `some k`.
* If it is passive now, the reward is `rPas x`, the next belief is `T¹(x) = x P` and the history
  gains `none`.

**Formalization Note.** `π []` is the first action and `fun h => π (o :: h)` is the rest of the
policy after a first slot recorded as `o`. The one step is that of `RelaxedIndexability.beliefStep`,
whose continuation cannot depend on the history and which is therefore not called here. -/
noncomputable def historyHorizonValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (rAct rPas : (Fin K → ℝ) → ℝ) : ℕ → Policy K → (Fin K → ℝ) → ℝ
  | 0, _, _ => 0
  | n + 1, π, x =>
      if π [] then
        rAct x + β * ∑ k, x k * historyHorizonValue β P rAct rPas n (fun h => π (some k :: h)) (P k)
      else
        rPas x + β * historyHorizonValue β P rAct rPas n (fun h => π (none :: h)) (x ᵥ* P)

/-- **The value of a history-dependent policy**: the expected total discounted reward
`𝔼_π[∑_{t=1}^{∞} β^{t−1} r_t | ω(1) = x]` (Liu, arXiv:2107.11939v4, (11), p.9), as the limit of the
`n`-horizon values.

**Formalization Note.** `limUnder` returns an unspecified value for a divergent sequence; for
`0 < β < 1`, a row-stochastic `P`, `x` in the simplex and rewards bounded on the simplex the
sequence converges. -/
noncomputable def historyValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : Policy K) (x : Fin K → ℝ) : ℝ :=
  limUnder atTop fun n => historyHorizonValue β P rAct rPas n π x

end RelaxedIndexability.Supplement


