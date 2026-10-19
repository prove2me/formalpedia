-- Prove2me | Definitions.Def_DynFairDiv_Uniform_Model
-- name    : DynFairDiv_Uniform_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:25.030316+00:00
-- url     : https://prove2.me/theorems/ff501a72-cafa-4902-ba8b-3dbc26679fc1
-- title:
--   §2, §2.2, Algorithm 1, pp. 947–950 — control vectors, arrivals-only allocation sequences with a disruption budget, the fairness ratio, and the frugally fair algorithm
-- statement:
--   This file sets up the model of dynamic fair resource division of Vardi, Psomas and Friedman, restricted to arrivals as in §§3–5 of the paper.
--
--   One unit of a homogeneous, divisible resource is shared among users who arrive one at a time. A **control vector** $\psi$ of length $n = |\psi| \in \{1, 2, \dots\} \cup \{\infty\}$ assigns to each arrival $t$ (with $1 \le t \le n$) the number $\psi[t]$ of users already present whose share may be reduced when the $t$-th user arrives. Users are labelled by their order of arrival, and $X^t_k$ denotes the share of the $(k+1)$-th user to arrive when $t$ users are present ($0 \le k < t$).
--
--   1. **Feasible allocation sequence.** A sequence $X = (X^1, X^2, \dots)$ is feasible for $(\psi, n)$ if at every time $1 \le t \le n$ all shares are nonnegative, $\sum_{k<t} X^t_k \le 1$, and, for $t \ge 2$, the number of users $k < t-1$ with $X^t_k < X^{t-1}_k$ (the **disrupted** users) is at most $\psi[t]$. Increasing a share is free; the newcomer is never disrupted.
--   2. **Fairness ratio at least $\sigma$.** A feasible $X$ achieves ratio $\sigma$ if for every $1 \le t \le n$ and every $k < t$,
--   $$X^t_k \ge \frac{\sigma}{t}, \qquad\text{i.e.}\qquad \inf_{1 \le t \le n} \; t \cdot \min_{k<t} X^t_k \ \ge\ \sigma .$$
--   3. **The fairness ratio of a control vector** is $\mathrm{FAIRNESS}(\psi) = \sup\{\sigma : \text{some feasible } X \text{ achieves ratio } \sigma\}$.
--   4. **The frugally fair algorithm** $\mathrm{FFA}(\psi,\sigma)$ (Algorithm 1): when user $t$ arrives, it gives $\sigma/t$ to the newcomer and cuts the $\psi[t]$ largest existing shares (all of them if fewer than $\psi[t]$ users are present) to $\sigma/t$. Its state at time $t$ is the list of its $t$ shares in nonincreasing order; $S^t$ denotes their sum, the total resource FFA allocates. FFA may allocate more than one unit (an infeasible allocation).
--   5. The **$d$-uniform control vector** has $\psi[t] = d$ for every $t$, and $\sigma^*_d = 1/\big((d+1)\ln\frac{d+1}{d}\big)$.
--
--   These objects are shared by every statement of the mission: the main theorem says that $\sigma^*_d$ is the optimal fairness ratio over all $d$-uniform control vectors.
--
--   **Formalization Note.** Departures are not modelled: the paper itself ignores them in §§3–5 (p. 949, "If only arrivals are allowed, every allocation algorithm can be viewed as history independent"), so an allocation algorithm on $\psi$ is exactly an allocation sequence as above. The paper sorts each $X^t$; labelling users by arrival order is equivalent, because feasibility uses only the sum, fairness only the minimum, and a disruption is a decrease of a given user's share. The horizon is $n : \mathbb{N}_\infty$ with $n = \top$ for an infinite control vector, `ψ 0` is unused, and `X t k` for $k \ge t$ is ignored. `fairnessRatio` is a real `sSup`; it is meaningful for $n \ge 1$, where the set contains $0$ (all shares zero) and is bounded above by $1$ (look at $t = 1$). FFA's list is `drop (ψ (t+1))` of the previous list followed by $\min(\psi[t+1], t) + 1$ copies of $\sigma/(t+1)$; for $\sigma \ge 0$ the list has length $t$ and is sorted nonincreasing, so dropping its front removes exactly the largest shares (tie-breaking is irrelevant for the multiset of shares).
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), pp. 947–950: §2 (allocation X^t ∈ [0,1]^t, feasibility), Definitions 2–4, §2.1 (arrivals only, p. 949), §2.2 (FAIRNESS(A,ψ,t), FAIRNESS(ψ), FAIRNESS(d−uniform)), Algorithm 1 (Frugally Fair Algorithm, p. 950); S^t from the proof of Theorem 4, p. 959

import Mathlib

namespace DynFairDiv.Uniform
open Finset

/-- Arrivals-only allocation sequence under control vector `ψ` with horizon `n = |ψ|`
(`n = ⊤` is an infinite control vector). `X t k` (for `k < t`) is the share of the `(k+1)`-th
user to arrive when `t` users are present; entries with `k ≥ t` are ignored. At every time
`1 ≤ t ≤ n` the shares are nonnegative and sum to at most `1`, and when the `t`-th user arrives
(`t ≥ 2`) at most `ψ t` of the `t - 1` users already present have their share strictly reduced
(increases are free; the newcomer is not counted). -/
def IsFeasibleAlloc (ψ : ℕ → ℕ) (n : ℕ∞) (X : ℕ → ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
    (∀ k < t, 0 ≤ X t k) ∧ (∑ k ∈ range t, X t k ≤ 1) ∧
    (2 ≤ t → ((range (t - 1)).filter (fun k => X t k < X (t - 1) k)).card ≤ ψ t)

/-- `X` is a feasible arrivals-only allocation sequence for `(ψ, n)` whose fairness ratio is at
least `σ`: at every time `1 ≤ t ≤ n`, every share is at least `σ / t`, i.e.
`t · min_k X^t_k ≥ σ`. -/
def AchievesRatio (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (X : ℕ → ℕ → ℝ) : Prop :=
  IsFeasibleAlloc ψ n X ∧ ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n → ∀ k < t, σ / (t : ℝ) ≤ X t k

/-- FAIRNESS(ψ): the supremum of the fairness ratios achievable on the control vector `ψ` of
length `n`. (A genuine supremum for `n ≥ 1`: the set contains `0` and is bounded above by `1`.) -/
noncomputable def fairnessRatio (ψ : ℕ → ℕ) (n : ℕ∞) : ℝ :=
  sSup {σ : ℝ | ∃ X, AchievesRatio ψ n σ X}

/-- FFA(ψ, σ), the frugally fair algorithm: the list of its shares when `t` users are present,
kept sorted nonincreasing (for `σ ≥ 0`). When user `t + 1` arrives, the `ψ (t + 1)` largest
shares (the front of the list) are cut to `σ / (t + 1)` and the newcomer gets `σ / (t + 1)`. -/
noncomputable def ffa (ψ : ℕ → ℕ) (σ : ℝ) : ℕ → List ℝ
  | 0 => []
  | t + 1 => (ffa ψ σ t).drop (ψ (t + 1)) ++
      List.replicate (min (ψ (t + 1)) t + 1) (σ / ((t + 1 : ℕ) : ℝ))

/-- `S^t`, the total resource allocated by FFA(ψ, σ) when `t` users are present. -/
noncomputable def ffaTotal (ψ : ℕ → ℕ) (σ : ℝ) (t : ℕ) : ℝ := (ffa ψ σ t).sum

/-- The `d`-uniform control vector, `ψ[t] = d` for every `t` (used with any horizon). -/
def uniformCV (d : ℕ) : ℕ → ℕ := fun _ => d

/-- The value `1 / ((d + 1) ln((d + 1) / d))`. -/
noncomputable def uniformRatio (d : ℕ) : ℝ :=
  1 / (((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d))

end DynFairDiv.Uniform


