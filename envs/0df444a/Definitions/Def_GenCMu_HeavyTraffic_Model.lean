-- Prove2me | Definitions.Def_GenCMu_HeavyTraffic_Model
-- name    : GenCMu_HeavyTraffic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:46.656986+00:00
-- url     : https://prove2.me/theorems/54504de5-6455-4c63-b022-2c9d00d5ae2d
-- title:
--   The multiclass single-server queue of §2: arrival, service, workload, delay and cost processes (1)–(10), and feasible work-conserving policies F1–F4
-- statement:
--   A single server is shared by $d$ job classes. The $i$th class-$k$ job ($i \ge 1$) arrives $u_{k,i} > 0$ time units after the $(i-1)$st one and needs $v_{k,i} \ge 0$ units of service. The partial sums
--   $$U_k(j) = \sum_{i=1}^{\lfloor j\rfloor} u_{k,i}, \qquad V_k(j) = \sum_{i=1}^{\lfloor j\rfloor} v_{k,i}$$
--   are the arrival epoch of the $j$th class-$k$ job and the total service requirement of the first $j$ class-$k$ jobs; the counting processes
--   $$A_k(t) = \max\{j \in \mathbb N : U_k(j) \le t\}, \qquad S_k(x) = \max\{j \in \mathbb N : V_k(j) \le x\}$$
--   count the class-$k$ arrivals during $[0,t]$ and the class-$k$ jobs completed during the first $x$ time units the server devotes to class $k$. Both sequences of partial sums tend to $+\infty$, so these maxima exist. Each class has a delay cost function $C_k : \mathbb R_+ \to \mathbb R_+$, nondecreasing and convex.
--
--   A **scheduling policy** is an allocation process $T = (T_k)$: $T_k(t)$ is the total time during $[0,t]$ that the server gives to class $k$. From it one defines the headcount $N_k(t) = A_k(t) - S_k(T_k(t))$ (5), the idleness $I(t) = t - \sum_k T_k(t)$ (6), the work input $L_k(t) = V_k(A_k(t))$ (7), the class workload $W_k(t) = L_k(t) - T_k(t)$ (8) and the total workload $W_+ = \sum_k W_k$. Under first-in-first-out sequencing inside each class, the delay of the class-$k$ job arriving at $t$ is
--   $$\tau_k(t) = \inf\{s \ge 0 : W_k(t) \le T_k(t+s) - T_k(t)\} \qquad (9),$$
--   and the cumulative delay cost up to $t$ is
--   $$J(t) = \sum_{k=1}^d \sum_{i=1}^{A_k(t)} C_k\big(\tau_k(U_k(i))\big) \qquad (3).$$
--
--   A policy is **feasible** if $T(0) = 0$; each $T_k$ is continuous and nondecreasing; $I$ is nondecreasing; $N_k \ge 0$ and $W_k \ge 0$; the policy is **work conserving** (the idleness $I$ is constant on every interval on which $W_+ > 0$); and every job finishes (the set in (9) is nonempty).
--
--   This file fixes the model shared by every statement of the mission: the heavy-traffic sequence is a sequence of such systems.
--
--   **Formalization Note** Classes are `Fin d` (the paper's $1,\dots,d$ shifted to $0,\dots,d-1$); job indices keep the paper's base $i \ge 1$. The paper states the conditions F1–F4 (p. 814); we state F1 without its adaptedness half (the analysis is sample-path, and dropping it only enlarges the class), F2–F4, and add three readings the paper uses without listing: $W_k \ge 0$ (p. 814: $W_k(t)$ is "the amount of work requested by those class k jobs that are in the system at time t"), work conservation (p. 814; the proof of Proposition 2 uses $W_+ = \varphi(X)$, p. 827), and that every job finishes (so that (9) is not $\inf\emptyset$). Policies are defined on $[0,\infty)$, not only on the horizon $[0,n]$, because (9) looks past $t$. Positive interarrival times encode the paper's "the system is empty at time $t = 0$" and make the arrival epochs distinct, as the paper's $\tau_k(U_k(i)) = \tau_{k,i}$ requires. The delay is the class-FIFO delay (9), so every result of the mission is about class-FIFO policies, as in the paper's proofs.
--
--   **Cost policy class** `IsCostAdmissible` has F1's initial condition, F2–F4, nonnegative workload and finite delays, but permits idleness with work waiting. Proposition 6 uses this broader class.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), DOI 10.1214/aoap/1177004706, §2, pp. 812–815, (1)–(10), conditions F1–F4

import Mathlib

namespace GenCMu.HeavyTraffic

open Filter Topology Finset

/-- (1): the partial sums `U(j) = Σ_{i=1}^{j} u_i`, `U(0) = 0`. The paper's index base `i ≥ 1` is
kept, so `u 0` is never used. -/
def partialSum (u : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 j, u i

/-- (2): the counting process `A(t) = max{j ∈ ℕ : U(j) ≤ t}`. It is a genuine maximum when the
partial sums tend to `∞` (every `System` assumes it); for `t < 0` the set is empty and the value
is `sSup ∅ = 0`. -/
noncomputable def countProc (u : ℕ → ℝ) (t : ℝ) : ℕ := sSup {j : ℕ | partialSum u j ≤ t}

/-- One single-server multiclass system of §2 (Van Mieghem 1995, pp. 812–813) with `d` job classes:
interarrival times `u k i` and service times `v k i` of the `i`th class-`k` job (`i ≥ 1`), and delay
cost functions `C k : ℝ₊ → ℝ₊` (only their values on `[0, ∞)` matter).

* `u_pos`: interarrival times are positive, so arrival epochs are distinct and the system is empty
  at time `0` (p. 813: "we assume that the system is empty at time t = 0"; the continuous-time delay
  process with `τ_k(U_k(i)) = τ_{k,i}` presupposes distinct arrival epochs).
* `U_tendsto`, `V_tendsto`: all interarrival and service times are finite and the arrival and
  service processes are finite at finite times (p. 816).
* `C_nonneg`, `C_mono`, `C_convex`: each `C_k : ℝ₊ → ℝ₊` is nondecreasing and convex (p. 813). -/
structure System (d : ℕ) where
  u : Fin d → ℕ → ℝ
  v : Fin d → ℕ → ℝ
  C : Fin d → ℝ → ℝ
  u_pos : ∀ k i, 1 ≤ i → 0 < u k i
  v_nonneg : ∀ k i, 0 ≤ v k i
  U_tendsto : ∀ k, Tendsto (partialSum (u k)) atTop atTop
  V_tendsto : ∀ k, Tendsto (partialSum (v k)) atTop atTop
  C_nonneg : ∀ k x, 0 ≤ x → 0 ≤ C k x
  C_mono : ∀ k, MonotoneOn (C k) (Set.Ici 0)
  C_convex : ∀ k, ConvexOn ℝ (Set.Ici 0) (C k)

/-- An allocation process (a scheduling policy): `T t k = T_k(t)`, the total time during `[0, t]`
that the server allocates to class `k`. It is defined for all `t ≥ 0`, not only on the horizon
`[0, n]`, because the delay (9) of a job arriving near the horizon looks past it. -/
abbrev Alloc (d : ℕ) := ℝ → Fin d → ℝ

/-- (6): cumulative server idleness `I(t) = t − Σ_k T_k(t)`. -/
def idle {d : ℕ} (T : Alloc d) (t : ℝ) : ℝ := t - ∑ k, T t k

namespace System

variable {d : ℕ} (Q : System d)

/-- `U_k(j)`: arrival epoch of the `j`th class-`k` job, (1). -/
def U (k : Fin d) (j : ℕ) : ℝ := partialSum (Q.u k) j
/-- `V_k(j)`: total service requirement of the first `j` class-`k` jobs. -/
def V (k : Fin d) (j : ℕ) : ℝ := partialSum (Q.v k) j
/-- `A_k(t)`: number of class-`k` arrivals during `[0, t]`, (2). -/
noncomputable def A (k : Fin d) (t : ℝ) : ℕ := countProc (Q.u k) t
/-- `S_k(x)`: number of class-`k` jobs served during the first `x` time units the server devotes to
class `k`. -/
noncomputable def S (k : Fin d) (x : ℝ) : ℕ := countProc (Q.v k) x
/-- (5): headcount `N_k(t) = A_k(t) − S_k(T_k(t))`. -/
noncomputable def N (T : Alloc d) (k : Fin d) (t : ℝ) : ℝ := (Q.A k t : ℝ) - Q.S k (T t k)
/-- (7): work input `L_k(t) = V_k(A_k(t))`. -/
noncomputable def L (k : Fin d) (t : ℝ) : ℝ := Q.V k (Q.A k t)
/-- (8): class workload `W_k(t) = L_k(t) − T_k(t)`. -/
noncomputable def W (T : Alloc d) (k : Fin d) (t : ℝ) : ℝ := Q.L k t - T t k
/-- Total workload `W_+(t) = Σ_k W_k(t)`. -/
noncomputable def Wplus (T : Alloc d) (t : ℝ) : ℝ := ∑ k, Q.W T k t
/-- (9): the class-FIFO delay of the class-`k` job arriving at `t`,
`τ_k(t) = inf{s ∈ ℝ₊ : W_k(t) ≤ T_k(t + s) − T_k(t)}`. -/
noncomputable def delay (T : Alloc d) (k : Fin d) (t : ℝ) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ Q.W T k t ≤ T (t + s) k - T t k}
/-- (3): cumulative delay cost `J(t) = Σ_k Σ_{i=1}^{A_k(t)} C_k(τ_{k,i})`, with
`τ_{k,i} = τ_k(U_k(i))`. -/
noncomputable def cost (T : Alloc d) (t : ℝ) : ℝ :=
  ∑ k, ∑ i ∈ Finset.Icc 1 (Q.A k t), Q.C k (Q.delay T k (Q.U k i))

/-- A feasible, work-conserving policy (p. 814): F1 (`T(0) = 0`), F2 (`T` continuous and
nondecreasing), F3 (idleness nondecreasing), F4 (`N ≥ 0`), together with

* `W_nonneg`: `W_k ≥ 0` — the server never works on class `k` beyond the work present (p. 814:
  `W_k(t)` "is the amount of work requested by those class k jobs that are in the system at time t");
* `work_conserving`: no idleness while there is work in the system (p. 814);
* `finishes`: every job eventually finishes, i.e. the infimum in (9) is over a nonempty set.

The adaptedness half of F1 is not imposed (the analysis is deterministic, sample path by sample
path); this only enlarges the class of policies. -/
structure IsFeasible (T : Alloc d) : Prop where
  zero : ∀ k, T 0 k = 0
  cont : ∀ k, ContinuousOn (fun t => T t k) (Set.Ici 0)
  mono : ∀ k, MonotoneOn (fun t => T t k) (Set.Ici 0)
  idle_mono : MonotoneOn (idle T) (Set.Ici 0)
  N_nonneg : ∀ k t, 0 ≤ t → 0 ≤ Q.N T k t
  W_nonneg : ∀ k t, 0 ≤ t → 0 ≤ Q.W T k t
  work_conserving : ∀ s t, 0 ≤ s → s ≤ t → (∀ r ∈ Set.Icc s t, 0 < Q.Wplus T r) →
    idle T s = idle T t
  finishes : ∀ k t, 0 ≤ t → ∃ s, 0 ≤ s ∧ Q.W T k t ≤ T (t + s) k - T t k

/-- A policy admissible for the cost lower bound. It has F1's initial condition and F2–F4,
nonnegative class workload, and finite FIFO delays. It may idle while work is waiting;
Proposition 6 compares costs over this broader class. -/
structure IsCostAdmissible (T : Alloc d) : Prop where
  zero : ∀ k, T 0 k = 0
  cont : ∀ k, ContinuousOn (fun t => T t k) (Set.Ici 0)
  mono : ∀ k, MonotoneOn (fun t => T t k) (Set.Ici 0)
  idle_mono : MonotoneOn (idle T) (Set.Ici 0)
  N_nonneg : ∀ k t, 0 ≤ t → 0 ≤ Q.N T k t
  W_nonneg : ∀ k t, 0 ≤ t → 0 ≤ Q.W T k t
  finishes : ∀ k t, 0 ≤ t → ∃ s, 0 ≤ s ∧ Q.W T k t ≤ T (t + s) k - T t k

end System

end GenCMu.HeavyTraffic


