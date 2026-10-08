-- Prove2me | Definitions.Def_ReedGGN_SystemEq_SamplePath
-- name    : ReedGGN_SystemEq_SamplePath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:33.521054+00:00
-- url     : https://prove2.me/theorems/3d393f1d-b02f-4666-af9f-222939ff5c0d
-- title:
--   §2, p. 6 — a sample path of the G/GI/N queue: N, Q₀, residual and service times, arrival times τᵢ, waiting times, and the arrival count A(t)
-- statement:
--   This file fixes the data of one realisation of the $G/GI/N$ queue of §2 of Reed's paper (p. 6).
--
--   1. There are $N$ servers. At time $0-$ there are $Q_0$ customers in the system; the first $\min(Q_0,N)$ are in service and the remaining $(Q_0-N)^+$ wait.
--   2. $\tilde\eta_i$, $i\ge 1$, is the residual service time of the $i$-th initial customer in service at time $0-$.
--   3. $\eta_i$, $i\ge 1$, is the service time of the $i$-th customer to enter service after time $0-$.
--   4. $\tau_i$, $i\ge 1$, is the arrival time of the $i$-th customer to arrive after time $0-$, with the paper's convention $\tau_0=0$. The arrival times are nondecreasing, $0=\tau_0\le\tau_1\le\tau_2\le\cdots$, and only finitely many of them lie in any bounded interval.
--   5. $w_i\ge 0$ is the waiting time of the $i$-th arriving customer, and $\tilde w_i\ge 0$ is the waiting time of the $(N+i)$-th initial customer.
--
--   The **arrival counting process** is
--   $$A(t)=\#\{i\ge 1:\ \tau_i\le t\},\qquad t\in\mathbb R .$$
--   Arrivals at time $0$ are counted in $A(0)$.
--
--   These are the objects in which the queue length (2.2), the decomposition (2.3)–(2.7) and the system equation (2.8) are written.
--
--   **Formalization Note** All sequences are indexed from $1$ as in the paper; the entry at index $0$ is unused except $\tau_0=0$. The paper takes the arrival process $A$ as primary and defines $\tau_i=\inf\{t\ge 0: A(t)\ge i\}$; for a counting process (nondecreasing, right continuous, integer valued, $A(0-)=0$) this gives $A(t)\ge i\iff\tau_i\le t$, so taking the arrival times as primary and $A$ as their counting function is the same data. The encoding has infinitely many arrivals, each at a finite time. The distributional assumptions of the paper (i.i.d. $\tilde\eta_i\sim F_0$, i.i.d. $\eta_i\sim F$ of mean 1) are not part of a sample path: every statement of this mission is a pathwise identity, valid for every realisation.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 6, §2 (Q₀, η̃ᵢ, τᵢ = inf{t ≥ 0 : A(t) ≥ i}, τ₀ = 0, ηᵢ, wᵢ, w̃ᵢ)

import Mathlib

namespace ReedGGN.SystemEq

/-- A sample path of the `G/GI/N` queue of §2 of Reed (2009), pp. 6–7. All sequences are
indexed from `1`, as in the paper; the value at index `0` is unused, except `τ 0 = 0`, which
is the paper's convention `τ_0 = 0` (p. 6).

* `N` is the number of servers and `Q₀` the number of customers present at time `0−`; the
  first `min(Q₀, N)` of them are in service, the other `(Q₀ − N)⁺` wait.
* `ηt i` (the paper's `η̃_i`) is the residual service time of the `i`-th initial customer in
  service at time `0−`.
* `η i` is the service time of the `i`-th customer to enter service after time `0−`.
* `τ i` is the arrival time of the `i`-th customer to arrive after time `0−`; the sequence
  is nondecreasing, starts at `τ 0 = 0`, and only finitely many arrivals occur in any
  bounded time interval.
* `w i` is the waiting time of the `i`-th arriving customer, and `wt i` (the paper's `w̃_i`)
  the waiting time of the `(N + i)`-th initial customer; both are nonnegative. -/
structure SamplePath where
  /-- number of servers -/
  N : ℕ
  /-- number of customers in the system at time `0−` -/
  Q₀ : ℕ
  /-- residual service times `η̃_i` of the initial customers in service -/
  ηt : ℕ → ℝ
  /-- service times `η_i`, in order of entry into service after time `0−` -/
  η : ℕ → ℝ
  /-- arrival times `τ_i` -/
  τ : ℕ → ℝ
  /-- waiting times `w_i` of the arriving customers -/
  w : ℕ → ℝ
  /-- waiting times `w̃_i` of the initial customers `N + 1, …, Q₀` -/
  wt : ℕ → ℝ
  /-- the paper's convention `τ_0 = 0` -/
  τ_zero : τ 0 = 0
  /-- arrival times are in order -/
  τ_mono : Monotone τ
  /-- finitely many arrivals by any time `t` -/
  τ_finite : ∀ t : ℝ, Set.Finite {i : ℕ | 1 ≤ i ∧ τ i ≤ t}
  /-- waiting times are nonnegative -/
  w_nonneg : ∀ i, 0 ≤ w i
  /-- waiting times of the initial customers are nonnegative -/
  wt_nonneg : ∀ i, 0 ≤ wt i

/-- The arrival counting process `A(t)`: the number of customers `i ≥ 1` with `τ_i ≤ t`.
For a counting process `A` with `A(0−) = 0`, the paper's `τ_i = inf{t ≥ 0 : A(t) ≥ i}`
(p. 6) gives `A(t) ≥ i ↔ τ_i ≤ t`, so `A` is recovered from `τ` exactly this way. Arrivals at
time `0` are counted in `A(0)`. -/
noncomputable def SamplePath.A (P : SamplePath) (t : ℝ) : ℕ :=
  Nat.card {i : ℕ // 1 ≤ i ∧ P.τ i ≤ t}

end ReedGGN.SystemEq


