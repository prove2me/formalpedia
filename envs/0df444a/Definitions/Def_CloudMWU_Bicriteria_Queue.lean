-- Prove2me | Definitions.Def_CloudMWU_Bicriteria_Queue
-- name    : CloudMWU_Bicriteria_Queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:04.823613+00:00
-- url     : https://prove2.me/theorems/f493fd82-8a67-4596-94e3-8f1e2c7dd3a9
-- title:
--   §1.1, p. 3 — the single-user deterministic queue Q_{t+1} = max{0, L_t + Q_t − h_t}, work w_t = min{h_t, L_t + Q_t}, cumulative work and allocation sequences
-- statement:
--   This file fixes the deterministic queueing model of a shared resource (§1.1, p. 3), first for a single user and then summed over $N$ users.
--
--   **Single user.** A user receives at each step $t = 0, 1, 2, \dots$ an allocation $a_t \in \mathbb R$ of the resource and a load $\ell_t \ge 0$ of new work. Its queue $Q_t$ is the work left at the *start* of step $t$. The queue starts empty and evolves by
--   $$Q_0 = 0, \qquad Q_{t+1} = \max\{0,\ \ell_t + Q_t - a_t\}.$$
--   The work completed at step $t$ is
--   $$w_t = \min\{a_t,\ \ell_t + Q_t\},$$
--   that is, the user processes as much of its queue plus the arriving load as its allocation allows. The cumulative work and the cumulative load of the first $t$ steps are
--   $$W_t = \sum_{\tau=0}^{t-1} w_\tau, \qquad \Lambda_t = \sum_{\tau=0}^{t-1} \ell_\tau .$$
--
--   **$N$ users.** For an allocation sequence $h_t = (h_t(1), \dots, h_t(N))$ and loads $L_t = (L_t(1), \dots, L_t(N))$, each user $i$ runs the queue above with $a_\tau = h_\tau(i)$ and $\ell_\tau = L_\tau(i)$. The total work $\mathrm{work}_{h}(t) = \sum_i W_t(i)$ and the total load $\sum_i \Lambda_t(i)$ are summed over users. A sequence $h$ is a sequence of $\kappa$-allocations if at every step $h_t(i) \ge 0$ for all $i$ and $\sum_i h_t(i) \le \kappa$; with $\kappa = 1$ these are the paper's allocations, and with $\kappa = 1 - \varepsilon$ its $(1-\varepsilon)$-allocations (§2.1, p. 8).
--
--   These objects are the common language of the whole mission: the online algorithm, the offline benchmark and the SLA comparator are all allocation sequences fed through the same queues.
--
--   **Formalization Note** Time is 0-based: Lean's step $t$ is the paper's step $t+1$, the queue at Lean time $t$ is the paper's $Q_{t+1}$, and the paper's $\sum_{\tau=1}^{t}$ is a sum over the first $t$ steps (`Finset.range t`). The paper never states $Q_1 = 0$; queues starting empty is an added convention, used implicitly in the proof of Claim 3.1. The horizon $T$ is not a parameter: loads are an infinite sequence, and every statement holds at every time $t$.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 3, §1.1 (The Model); p. 8, §2.1 ((1 − ε)-allocations)

import Mathlib

namespace CloudMWU.Bicriteria

open Finset

/-- Queue of a single user at the *start* of step `t` (0-based), when the user receives the
allocation `a τ` and the load `ℓ τ` at step `τ`. Queues start empty (`queue a ℓ 0 = 0`), and
`Q_{t+1} = max {0, L_t + Q_t − h_t}` (§1.1, p. 3). -/
noncomputable def queue (a ℓ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => max 0 (ℓ t + queue a ℓ t - a t)

/-- Work completed at step `t`: `w_t = min {h_t, L_t + Q_t}` (§1.1, p. 3). -/
noncomputable def work (a ℓ : ℕ → ℝ) (t : ℕ) : ℝ := min (a t) (ℓ t + queue a ℓ t)

/-- Work completed during the first `t` steps (steps `0, …, t-1`; the paper's `Σ_{τ=1}^t w_τ`). -/
noncomputable def cumWork (a ℓ : ℕ → ℝ) (t : ℕ) : ℝ := ∑ τ ∈ range t, work a ℓ τ

/-- Load arrived during the first `t` steps (the paper's `Σ_{τ=1}^t L_τ`). -/
noncomputable def cumLoad (ℓ : ℕ → ℝ) (t : ℕ) : ℝ := ∑ τ ∈ range t, ℓ τ

variable {N : ℕ}

/-- Total work of the `N`-user allocation sequence `h` on the loads `L` during the first `t`
steps (`work_{h_1,…,h_t}` in the paper). -/
noncomputable def totalWork (h L : ℕ → Fin N → ℝ) (t : ℕ) : ℝ :=
  ∑ i, cumWork (fun τ => h τ i) (fun τ => L τ i) t

/-- Total load arrived during the first `t` steps. -/
noncomputable def totalLoad (L : ℕ → Fin N → ℝ) (t : ℕ) : ℝ :=
  ∑ i, cumLoad (fun τ => L τ i) t

/-- `h` is a sequence of `cap`-allocations: at every step it is nonnegative and
`Σ_i h_t(i) ≤ cap` (`cap = 1` for allocations, `cap = 1 − ε` for `(1 − ε)`-allocations, p. 8). -/
def IsAllocSeq (cap : ℝ) (h : ℕ → Fin N → ℝ) : Prop :=
  ∀ t, (∀ i, 0 ≤ h t i) ∧ ∑ i, h t i ≤ cap

end CloudMWU.Bicriteria


