-- Prove2me | Definitions.Def_FocusSetRB_HRPolicy
-- name    : FocusSetRB_HRPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:35.744967+00:00
-- url     : https://prove2.me/theorems/bb9c2169-0699-4169-a4de-7ebb0850597c
-- title:
--   History-dependent randomized policies, $R^-(\pi,S_0)$ and the optimal reward $R^*(N,S_0)$
-- statement:
--   In the $N$-armed problem exactly $\alpha N=k$ arms are pulled at every step (budget constraint (1a)). A **history-dependent randomized policy** chooses, at every time $t$ and after every history $(S_0,A_0,\dots,A_{t-1},S_t)$, a probability distribution over action vectors, every one of which pulls exactly $k$ arms. Given the actions, the arms move independently according to $P$, which together with the initial state vector $S_0$ determines the law of the whole trajectory.
--
--   The **liminf average reward** of $\pi$ is
--
--   $$
--   R^-(\pi,S_0)=\liminf_{T\to\infty}\frac{1}{NT}\sum_{t=0}^{T-1}\sum_{i\in[N]}\mathbb E\big[r(S^\pi_t(i),A^\pi_t(i))\big],
--   $$
--
--   and the **optimal reward** is $R^*(N,S_0)=\sup_\pi R^-(\pi,S_0)$, the supremum over all such policies. The optimality gap of a policy $\pi$ is $R^*(N,S_0)-R^-(\pi,S_0)$.
--
--   **Formalization Note** Distributions on finite sets are real probability vectors. The history law is defined recursively in $t$. $k=\alpha N$ is a natural number. The policy class is nonempty for $k\le N$, and every $R^-$ lies in $[-r_{\max},r_{\max}]$, so $R^*$ is a genuine supremum.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, §3.1, (RB) and (1a), p.5

import Mathlib
import Definitions.Def_FocusSetRB_scaledCount

namespace FocusSetRB

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The **budget constraint** (1a) (arXiv:2402.05689v4, §3.1, p.5): exactly `αN = k` arms are
pulled, `∑_{i ∈ [N]} A(i) = αN`.

**Formalization Note.** `k : ℕ` is the integer `αN` (the source assumes `αN` is an integer);
the theorems tie it to `α` by `(k : ℝ) = α * N`. -/
def IsBudgetFeasible {N : ℕ} (k : ℕ) (a : Fin N → Bool) : Prop :=
  (univ.filter fun i => a i = true).card = k

/-- A **history-dependent randomized policy** for the `N`-armed problem with budget `k`
(arXiv:2402.05689v4, §3.1, p.5: "We allow the policy to be randomized and choose actions based on
the whole history"). At time `t`, given the past state vectors `S₀, …, S_t`
(`xs : Fin (t+1) → Fin N → S`) and past action vectors `A₀, …, A_{t−1}`
(`as : Fin t → Fin N → Bool`), the policy draws the action vector `A_t = a` with probability
`rule t xs as a`; every action vector it can draw satisfies (1a).

**Formalization Note.** Laws on finite types are real-valued probability vectors. -/
structure HRPolicy (S : Type*) (N k : ℕ) where
  /-- `rule t xs as a` = probability of the action vector `a` at time `t` after history
  `(xs, as)`. -/
  rule : (t : ℕ) → (Fin (t + 1) → Fin N → S) → (Fin t → Fin N → Bool) → (Fin N → Bool) → ℝ
  nonneg : ∀ t xs as a, 0 ≤ rule t xs as a
  sum_one : ∀ t xs as, ∑ a, rule t xs as a = 1
  budget : ∀ t xs as a, 0 < rule t xs as a → IsBudgetFeasible k a

variable {N k : ℕ}

/-- The law of the history `(S₀, …, S_t; A₀, …, A_{t−1})` under the policy `π` from the initial
state vector `S₀` (arXiv:2402.05689v4, §3.1, p.5): the actions are drawn by `π`, and given the
actions the arms move independently according to `P` (`stepProb`). -/
noncomputable def histLaw (M : SingleArmMDP S) (π : HRPolicy S N k) (S0 : Fin N → S) :
    (t : ℕ) → (Fin (t + 1) → Fin N → S) → (Fin t → Fin N → Bool) → ℝ
  | 0, xs, _ => if xs 0 = S0 then 1 else 0
  | t + 1, xs, as =>
      histLaw M π S0 t (Fin.init xs) (Fin.init as) *
        π.rule t (Fin.init xs) (Fin.init as) (as (Fin.last t)) *
        stepProb M (xs (Fin.castSucc (Fin.last t))) (as (Fin.last t)) (xs (Fin.last (t + 1)))

/-- The expected reward per arm at time `t`, `(1/N) ∑_{i ∈ [N]} 𝔼[r(S^π_t(i), A^π_t(i))]`
(arXiv:2402.05689v4, §3.1, p.5). -/
noncomputable def hrReward (M : SingleArmMDP S) (π : HRPolicy S N k) (S0 : Fin N → S)
    (t : ℕ) : ℝ :=
  ∑ xs, ∑ as, histLaw M π S0 t xs as *
    ∑ a, π.rule t xs as a * ((1 / (N : ℝ)) * ∑ i, M.r (xs (Fin.last t) i) (a i))

/-- The **liminf Cesàro average** `liminf_{T → ∞} (1/T) ∑_{t=0}^{T−1} g(t)` of a reward
sequence (arXiv:2402.05689v4, §3.1, p.5).

**Formalization Note.** `Filter.liminf` in `ℝ`; for the bounded reward sequences of the
mission (all bounded by `r_max`) it is the genuine liminf. -/
noncomputable def cesaroLiminf (g : ℕ → ℝ) : ℝ :=
  Filter.liminf (fun T : ℕ => (1 / (T : ℝ)) * ∑ t ∈ range T, g t) Filter.atTop

/-- The **liminf average reward** `R⁻(π, S₀) = liminf_{T→∞} (1/(NT)) ∑_{t<T} ∑_i
𝔼[r(S^π_t(i), A^π_t(i))]` of a history-dependent randomized policy (arXiv:2402.05689v4, §3.1,
p.5). -/
noncomputable def Rminus (M : SingleArmMDP S) (π : HRPolicy S N k) (S0 : Fin N → S) : ℝ :=
  cesaroLiminf (hrReward M π S0)

/-- The **optimal reward** `R*(N, S₀)` of the `N`-armed problem (RB) (arXiv:2402.05689v4, §3.1,
p.5): the supremum of `R⁻(π, S₀)` over all history-dependent randomized policies satisfying the
budget constraint (1a) at every step.

**Formalization Note.** A real `⨆` over `HRPolicy S N k`; the family is nonempty for `k ≤ N`
and bounded above by `r_max`, so the supremum is genuine. -/
noncomputable def Rstar (M : SingleArmMDP S) (N k : ℕ) (S0 : Fin N → S) : ℝ :=
  ⨆ π : HRPolicy S N k, Rminus M π S0

end FocusSetRB


