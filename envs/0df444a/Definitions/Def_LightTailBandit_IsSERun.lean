-- Prove2me | Definitions.Def_LightTailBandit_IsSERun
-- name    : LightTailBandit_IsSERun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:05.473551+00:00
-- url     : https://prove2.me/theorems/941dd6ea-6dcf-43c2-b3bb-fca16d41aeb5
-- title:
--   Runs of successive elimination with the bonus (6) (Algorithm 1)
-- statement:
--   Successive elimination proceeds in phases. Phase $1$ starts at round $1$ with all arms active. In phase $n$ each active arm is pulled once; then every active arm $k$ is eliminated for which some active arm $k'$ satisfies
--   $$
--   \hat\theta_{k'}(n)-\mathrm{rad}(n)>\hat\theta_{k}(n)+\mathrm{rad}(n),
--   $$
--   where $\hat\theta_k(n)$ is the mean of the first $n$ rewards of arm $k$, and phase $n+1$ starts with the arms that remain.
--
--   Along one sample path, actions $a_1,\dots,a_T$ are a **run of successive elimination with the bonus (6)** when every round of phase $n$ pulls an arm that is active in phase $n$ and has not been pulled earlier in that phase. The active sets and the phase start times are computed from the path itself.
--
--   **Formalization Note** Phases and rounds are 0-based. The comparison arm $k'$ ranges over the active set, all eliminations of a phase use the same estimates, and the run stops at round $T$ (a last phase may be cut short). The order inside a phase is free. The verification file proves that the active set is never empty, that every active arm has exactly $n$ pulls when phase $n$ starts (so the printed $\mathrm{rad}(n_{t,k})$ is $\mathrm{rad}(n)$), and that a run exists for every noise path.
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Algorithm 1, p.11, with rad from (6), p.19

import Mathlib
import Definitions.Def_LightTailBandit_reward
import Definitions.Def_LightTailBandit_rad

namespace LightTailBandit

/-- **The phase mean `θ̂_{t_k(n),k}`** (arXiv:2206.02969v6, Algorithm 1, p.11): the sum of the
rewards of arm `k` in rounds `u < s`, divided by `n`. Successive elimination reads it at
`s = start n`, when every active arm has been pulled exactly `n` times, so it is the mean of the
first `n` rewards of arm `k`. -/
noncomputable def phaseMean {K : ℕ} (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ) (h : ℕ → Fin K)
    (s n : ℕ) (k : Fin K) : ℝ :=
  (∑ u ∈ (Finset.range s).filter (fun u => h u = k), reward θ e h u) / (n : ℝ)

open Classical in
/-- **The phase state of successive elimination** (arXiv:2206.02969v6, Algorithm 1, p.11, with
`rad` of (6), p.19).

`seState … n = (active set of phase n, first round of phase n)`, computed along one sample path:
* phase `0` starts at round `0` with all arms active;
* phase `n + 1` starts at `start (n+1) = start n + |active n|` (each active arm pulled once in
  phase `n`); its active set keeps the arms `k` of `active n` for which no `k' ∈ active n` has
  `θ̂_{k'} − rad(n+1) > θ̂_k + rad(n+1)`, where `θ̂` is the phase mean after `n + 1` pulls.

**Formalization Note.** Lean phase `n` is the paper's phase `n + 1`. The paper's line 4 compares
`θ̂_{t_{k'}(n),k'} − rad(n_{t,k'}) > θ̂_{t_k(n),k} + rad(n_{t,k})`; every active arm has `n + 1`
pulls at `start (n+1)`, so both radii are `rad(n+1)`. The comparison arm `k'` ranges over the
active set (an eliminated arm has no `(n+1)`-th sample), and all eliminations of one phase use
the same estimates. -/
noncomputable def seState {K : ℕ} (σ η₁ η₂ : ℝ) (T : ℕ) (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ)
    (h : ℕ → Fin K) : ℕ → Finset (Fin K) × ℕ
  | 0 => (Finset.univ, 0)
  | n + 1 =>
    let A := (seState σ η₁ η₂ T θ e h n).1
    let s := (seState σ η₁ η₂ T θ e h n).2 + A.card
    (A.filter (fun k => ¬ ∃ k' ∈ A,
        phaseMean θ e h s (n + 1) k' - rad σ η₁ η₂ T K (n + 1) >
          phaseMean θ e h s (n + 1) k + rad σ η₁ η₂ T K (n + 1)), s)

/-- The active set of (Lean) phase `n` of successive elimination. -/
noncomputable def active {K : ℕ} (σ η₁ η₂ : ℝ) (T : ℕ) (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ)
    (h : ℕ → Fin K) (n : ℕ) : Finset (Fin K) :=
  (seState σ η₁ η₂ T θ e h n).1

/-- The first round of (Lean) phase `n` of successive elimination. -/
noncomputable def start {K : ℕ} (σ η₁ η₂ : ℝ) (T : ℕ) (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ)
    (h : ℕ → Fin K) (n : ℕ) : ℕ :=
  (seState σ η₁ η₂ T θ e h n).2

/-- **A run of successive elimination with the bonus (6)** (arXiv:2206.02969v6, Algorithm 1,
p.11: "while `t < T` do: Pull each arm in `A` once. `t ← t + |A|`. `n ← n + 1`. Eliminate any
`k ∈ A` from `A` if `∃k′: θ̂_{t_{k′}(n),k′} − rad(n_{t,k′}) > θ̂_{t_k(n),k} + rad(n_{t,k})`").

Along one sample path, the actions `h` are a run of SE with horizon `T` when every round `t < T`
of phase `n` (`start n ≤ t < start (n+1)`) pulls an arm of `active n` that has not been pulled
earlier in the same phase.

**Formalization Note.** Rounds and phases are 0-based. The order of the arms inside a phase is
free (any deterministic or randomized order), and the run stops at round `T`, so a last phase may
be cut short; phases starting after `T` are never read. -/
def IsSERun {K : ℕ} (σ η₁ η₂ : ℝ) (T : ℕ) (θ : Fin K → ℝ) (e : ℕ → Fin K → ℝ)
    (h : ℕ → Fin K) : Prop :=
  ∀ n t, start σ η₁ η₂ T θ e h n ≤ t → t < start σ η₁ η₂ T θ e h (n + 1) → t < T →
    h t ∈ active σ η₁ η₂ T θ e h n ∧
      ∀ s, start σ η₁ η₂ T θ e h n ≤ s → s < t → h s ≠ h t

end LightTailBandit


