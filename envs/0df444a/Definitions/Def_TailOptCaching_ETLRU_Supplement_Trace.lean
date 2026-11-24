-- Prove2me | Definitions.Def_TailOptCaching_ETLRU_Supplement_Trace
-- name    : TailOptCaching_ETLRU_Supplement_Trace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:47:52.816017+00:00
-- url     : https://prove2.me/theorems/5a88a732-7978-4227-8b4e-716eb7c8bd8d
-- title:
--   §3, pp. 5–7 and App. A, pp. 16–17 — deterministic arrival trace, constraints (4)–(6), TEL, the TEL-safe budget (12) and Tail-Optimized Belady
-- statement:
--   This file sets up the deterministic model of §3, which is used to study the hindsight-optimal caching policy.
--
--   **Trace.** Time is discrete, $t=1,\dots,T$, and there are $N$ conversations. Each conversation $i\in[N]$ issues requests at the times of a set $\mathcal T_i\subseteq[T]$, and the sets $\mathcal T_i$ are pairwise disjoint (at most one request per step; a step may have no request). For $t\in\mathcal T_i$, $q_{i,t}$ and $a_{i,t}$ are the lengths, in blocks, of the user prompt and of the model response of that turn; $q_{i,t}=a_{i,t}=0$ for $t\notin\mathcal T_i$. The history of conversation $i$ through $t$ has length $H_i(t)=\sum_{j=1}^{t}(q_{i,j}+a_{i,j})$, and the request of $i$ at $t\in\mathcal T_i$ needs
--   $$B_{i,t}=\sum_{j=1}^{t}q_{i,j}+\sum_{j=1}^{t-1}a_{i,j}$$
--   blocks.
--
--   **Caching state.** $x_{i,t}\in\mathbb N$ is the number of blocks of conversation $i$ in the cache at time $t$, before the request. It is **feasible** for capacity $C$ when the cache is empty at the start, $x_{i,1}=0$, and
--   $$\textstyle\sum_{i}x_{i,t}\le C\ (t\in[T]),\qquad x_{i,t+1}\le H_i(t)\ (t\in\mathcal T_i,\ t<T),\qquad x_{i,t+1}\le x_{i,t}\ (t\notin\mathcal T_i,\ t<T),$$
--   which are constraints (4), (5) and (6).
--
--   **Objective.** For a threshold $\xi$, the **Tail Excess Latency** divided by the TTFT slope $\alpha>0$ is
--   $$\mathrm{TEL}(x)=\sum_{i\in[N]}\sum_{t\in\mathcal T_i}\bigl(B_{i,t}-x_{i,t}-\xi\bigr)^+,$$
--   the value of problem (7) at the optimal slacks, and $\mathrm{hits}(x)=\sum_i\sum_{t\in\mathcal T_i}x_{i,t}$ is the objective of (11). The **TEL-safe budget** of the request of $i$ at $t$ is $(B_{i,t}-\xi)^+$; a state satisfies (12) when $x_{i,t}\le(B_{i,t}-\xi)^+$ at every request. Capping a state means replacing $x_{i,t}$ by $\min(x_{i,t},(B_{i,t}-\xi)^+)$ at every request.
--
--   **Tail-Optimized Belady.** For a time $t$ and conversation $j$, let $\mathrm{nxt}_j(t)$ be the first request time of $j$ after $t$, or $\infty$ if $j$ never requests again. To choose the state at $t+1$, the policy first caps each conversation: $y_j=\min(u_j,c_j)$, where $u_j=H_j(t)$ if $t\in\mathcal T_j$ and $u_j=x_{j,t}$ otherwise, and $c_j$ is the TEL-safe budget of $j$'s next request (and $0$ if there is none). If $\sum_jy_j>C$, it then evicts blocks one at a time from a conversation whose next request is furthest in the future, until the total is $C$, with any tie-breaking. The outcomes of this eviction are exactly the vectors $x_{\cdot,t+1}\le y$ with $\sum_jx_{j,t+1}=\min(C,\sum_jy_j)$ such that whenever some conversation $k$ lost blocks, every conversation whose next request is later than $k$'s holds no block. A run of the policy starts from the empty cache and takes such a step from every $t<T$.
--
--   These objects are the setting of Theorem 1 and of its proof in Appendix A.
--
--   **Formalization Note** Conversations are `Fin N`; times are natural numbers, and only $1\le t\le T$ are used. The trace stores one owner per time step (`Option (Fin N)`), which encodes the disjoint sets $\mathcal T_i$, and one prompt and response length per step. The threshold $\xi$ is a natural number and the positive parts are `Int.toNat`. The constant $\alpha$ is dropped. The next request time is a `WithTop ℕ`, with $\top$ for "never again".
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, p. 5 (§3, deterministic arrival trace, caching state, (4)–(6)), p. 6 (TEL, problem (7), Theorem 1), p. 7 (Tail-Optimized Belady), p. 16 (App. A, Step one, (11)–(12)), p. 17 (Step two, furthest-in-future rule)

import Mathlib

namespace TailOptCaching.ETLRU.Supplement

/-- A deterministic arrival trace (§3, p. 5) with `N` conversations over the horizon
`t = 1, …, T`. `owner t = some i` means conversation `i` issues a request at time `t`;
`owner t = none` means no request at `t`. This encodes the request-time sets
`T_i = {t ∈ [T] : owner t = some i}` and their pairwise disjointness. `q t`, `a t` are the
prompt and response lengths (in blocks) of the turn at time `t`; they are read only at
request times. -/
structure Trace (N : ℕ) where
  T : ℕ
  owner : ℕ → Option (Fin N)
  q : ℕ → ℕ
  a : ℕ → ℕ

variable {N : ℕ}

/-- The request-time set `T_i ⊆ [T] = {1, …, T}` of conversation `i`. -/
def reqTimes (tr : Trace N) (i : Fin N) : Finset ℕ :=
  (Finset.Icc 1 tr.T).filter (fun t => tr.owner t = some i)

/-- `q_{i,t}`: the prompt length of conversation `i` at time `t`, zero for `t ∉ T_i`. -/
def qc (tr : Trace N) (i : Fin N) (t : ℕ) : ℕ :=
  if t ∈ reqTimes tr i then tr.q t else 0

/-- `a_{i,t}`: the response length of conversation `i` at time `t`, zero for `t ∉ T_i`. -/
def ac (tr : Trace N) (i : Fin N) (t : ℕ) : ℕ :=
  if t ∈ reqTimes tr i then tr.a t else 0

/-- The history length `H_i(t) = Σ_{j=1}^{t} (q_{i,j} + a_{i,j})` of conversation `i`
through time `t` (right side of (5)). -/
def hist (tr : Trace N) (i : Fin N) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 t, (qc tr i j + ac tr i j)

/-- The number of blocks of the request of conversation `i` at time `t ≥ 1`:
`Σ_{j=1}^{t} q_{i,j} + Σ_{j=1}^{t-1} a_{i,j}`. -/
def need (tr : Trace N) (i : Fin N) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 t, qc tr i j + ∑ j ∈ Finset.Icc 1 (t - 1), ac tr i j

/-- The TEL-safe budget `(Σ_{j=1}^{t} q_{i,j} + Σ_{j=1}^{t-1} a_{i,j} − ξ)^+` (Theorem 1, (12)),
for an integer threshold `ξ`. -/
def budget (tr : Trace N) (ξ : ℕ) (i : Fin N) (t : ℕ) : ℕ :=
  ((need tr i t : ℤ) - ξ).toNat

/-- A caching state `x_{i,t}` (blocks of conversation `i` cached at time `t`, before the
request) is feasible for capacity `C`: empty initial cache `x_{i,1} = 0`, the capacity
constraint (4) at every `t ∈ [T]`, the history bound (5) for `t ∈ T_i, t < T`, and
no growth off arrivals (6) for `t ∈ [T] \ T_i, t < T`. -/
def Feasible (tr : Trace N) (C : ℕ) (x : Fin N → ℕ → ℕ) : Prop :=
  (∀ i, x i 1 = 0) ∧
  (∀ t, 1 ≤ t → t ≤ tr.T → ∑ i, x i t ≤ C) ∧
  (∀ i t, t ∈ reqTimes tr i → t < tr.T → x i (t + 1) ≤ hist tr i t) ∧
  (∀ i t, 1 ≤ t → t < tr.T → t ∉ reqTimes tr i → x i (t + 1) ≤ x i t)

/-- The TEL-safe cap (12): `x_{i,t} ≤ (Σ_{j≤t} q_{i,j} + Σ_{j<t} a_{i,j} − ξ)^+` at every
request `t ∈ T_i`. -/
def WithinBudget (tr : Trace N) (ξ : ℕ) (x : Fin N → ℕ → ℕ) : Prop :=
  ∀ i t, t ∈ reqTimes tr i → x i t ≤ budget tr ξ i t

/-- The capped caching state of App. A, Step one (p. 16): `x_{i,t}` replaced by
`min(x_{i,t}, (Σ_{j≤t} q_{i,j} + Σ_{j<t} a_{i,j} − ξ)^+)` at every request `t ∈ T_i`,
unchanged elsewhere. -/
def capToBudget (tr : Trace N) (ξ : ℕ) (x : Fin N → ℕ → ℕ) : Fin N → ℕ → ℕ :=
  fun i t => if t ∈ reqTimes tr i then min (x i t) (budget tr ξ i t) else x i t

/-- Tail Excess Latency divided by the slope `α > 0`:
`Σ_{i ∈ [N]} Σ_{t ∈ T_i} (Σ_{j≤t} q_{i,j} + Σ_{j<t} a_{i,j} − x_{i,t} − ξ)^+`
(§3, p. 6; the objective of (7) at its optimal slacks). -/
def tel (tr : Trace N) (ξ : ℕ) (x : Fin N → ℕ → ℕ) : ℕ :=
  ∑ i, ∑ t ∈ reqTimes tr i, ((need tr i t : ℤ) - x i t - ξ).toNat

/-- The total number of reused cached blocks `Σ_{i ∈ [N]} Σ_{t ∈ T_i} x_{i,t}`,
the objective of (11). -/
def hits (tr : Trace N) (x : Fin N → ℕ → ℕ) : ℕ :=
  ∑ i, ∑ t ∈ reqTimes tr i, x i t

/-- The next request time of conversation `i` strictly after `t`, or `⊤` when
conversation `i` never requests again. -/
def nextReq (tr : Trace N) (i : Fin N) (t : ℕ) : WithTop ℕ :=
  ((reqTimes tr i).filter (fun s => t < s)).min

/-- The cap applied to conversation `j` when the caching state for time `t + 1` is chosen:
the TEL-safe budget of its next request, and `0` if it never requests again. -/
def nextCap (tr : Trace N) (ξ : ℕ) (j : Fin N) (t : ℕ) : ℕ :=
  match nextReq tr j t with
  | ⊤ => 0
  | (s : ℕ) => budget tr ξ j s

/-- The capped allocation `y_j` before eviction at the step from `t` to `t + 1`: the bound
of (5) (history through `t`) if `t ∈ T_j`, else the current `x_{j,t}` (6), further capped at
the TEL-safe budget of `j`'s next request. -/
def cappedAlloc (tr : Trace N) (ξ : ℕ) (x : Fin N → ℕ → ℕ) (t : ℕ) (j : Fin N) : ℕ :=
  min (if t ∈ reqTimes tr j then hist tr j t else x j t) (nextCap tr ξ j t)

/-- One step of Tail-Optimized Belady (§3, pp. 6–7; App. A, p. 17), for every tie-breaking:
starting from the capped allocation `y = cappedAlloc`, blocks are evicted one at a time from a
conversation whose next request is furthest in the future (`⊤` furthest) until the total fits
in `C`. Its outcomes are exactly the vectors `x_{·,t+1}` with `x_{·,t+1} ≤ y`,
`Σ_j x_{j,t+1} = min(C, Σ_j y_j)`, and: whenever conversation `k` lost blocks
(`x_{k,t+1} < y_k`), every conversation `j` whose next request is later than `k`'s is
emptied (`x_{j,t+1} = 0`). -/
def TOBStep (tr : Trace N) (C ξ : ℕ) (x : Fin N → ℕ → ℕ) (t : ℕ) : Prop :=
  (∀ j, x j (t + 1) ≤ cappedAlloc tr ξ x t j) ∧
  ∑ j, x j (t + 1) = min C (∑ j, cappedAlloc tr ξ x t j) ∧
  (∀ j k, x k (t + 1) < cappedAlloc tr ξ x t k → nextReq tr k t < nextReq tr j t →
    x j (t + 1) = 0)

/-- A run of Tail-Optimized Belady on the trace: empty cache at `t = 1`, then a
`TOBStep` from every `t ∈ [T]` with `t < T` to `t + 1`. -/
def IsTOBRun (tr : Trace N) (C ξ : ℕ) (x : Fin N → ℕ → ℕ) : Prop :=
  (∀ i, x i 1 = 0) ∧ ∀ t, 1 ≤ t → t < tr.T → TOBStep tr C ξ x t

end TailOptCaching.ETLRU.Supplement


