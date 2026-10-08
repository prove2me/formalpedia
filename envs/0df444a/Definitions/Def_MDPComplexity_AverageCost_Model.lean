-- Prove2me | Definitions.Def_MDPComplexity_AverageCost_Model
-- name    : MDPComplexity_AverageCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:45:04.184133+00:00
-- url     : https://prove2.me/theorems/f5ed1d7b-dd86-4003-b96e-ef678b003db7
-- title:
--   Average costs, decision walks, simple cycles and min-plus powers
-- statement:
--   For a finite deterministic process, a **policy** $\delta(s,t)$ selects a decision at state $s$ and time $t$. From initial state $s_0$ it generates states $s_{t+1}=\operatorname{next}(s_t,\delta(s_t,t))$ and costs $c(s_t,\delta(s_t,t))$. The finite average, its upper limit and the optimal value are
--
--   $$a_T^\delta=\frac{1}{T}\sum_{t=0}^{T}c(s_t,\delta(s_t,t)),\qquad g^\delta(s_0)=\limsup_{T\to\infty}a_T^\delta,\qquad g^*(s_0)=\inf_\delta g^\delta(s_0).$$
--
--   A state is **reachable** when a finite decision walk from $s_0$ ends there. A **simple cycle** is a positive-length sequence of distinct states and decision arcs returning to its starting state; its mean is its total cost divided by its length. The **min-plus adjacency matrix** $A$ assigns to $(u,v)$ the cheapest cost among decisions from $u$ to $v$, or $+\infty$ when there is none. Its $k$th min-plus power takes minima of sums of arc costs; the zeroth power is the identity matrix.
--
--   These objects connect the paper's policy problem to its directed-graph calculation.
--
--   **Formalization Note** The paper prints $T+1$ cost terms divided by $T$; at $T=0$ Lean assigns the quotient zero, which does not affect a limit. The paper writes a limit for arbitrary time-dependent policies, although it need not exist; the upper limit gives the cost-minimization reading. Finiteness of states and decision sets bounds every policy's averages. The optimum ranges over all $\delta(s,t)$. The min-plus entries use `WithTop ℝ` to represent a missing arc without a finite surrogate.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), pp. 444–446, §2 Markov Decision Processes and §3 The infinite horizon undiscounted case, https://doi.org/10.1287/moor.12.3.441

import Definitions.Def_MDPComplexity_AverageCost_DetMDP

namespace MDPComplexity.AverageCost

open Filter Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The paper's policy δ(s,t), allowed to depend on time. -/
def DetMDP.Policy (M : DetMDP S) := (s : S) → ℕ → M.D s

/-- The deterministic state trajectory from `s₀`. -/
def DetMDP.path (M : DetMDP S) (s₀ : S) (δ : M.Policy) : ℕ → S :=
  Nat.rec s₀ (fun t s => M.next s (δ s t))

/-- Cost incurred at time `t`. -/
def DetMDP.stageCost (M : DetMDP S) (s₀ : S) (δ : M.Policy) (t : ℕ) : ℝ :=
  M.c (M.path s₀ δ t) (δ (M.path s₀ δ t) t)

/-- The printed finite average has T+1 terms and denominator T. At T=0 its Lean value
is zero; this has no effect on the limit. -/
noncomputable def DetMDP.average (M : DetMDP S) (s₀ : S) (δ : M.Policy) (T : ℕ) : ℝ :=
  (∑ t ∈ range (T + 1), M.stageCost s₀ δ t) / T

/-- The upper limit of the finite averages, defined for every time-dependent policy. -/
noncomputable def DetMDP.avgCost (M : DetMDP S) (s₀ : S) (δ : M.Policy) : ℝ :=
  limsup (M.average s₀ δ) atTop

/-- The optimum ranges over all state-and-time policies, not just stationary policies. -/
noncomputable def DetMDP.optAvg (M : DetMDP S) (s₀ : S) : ℝ :=
  ⨅ δ : M.Policy, M.avgCost s₀ δ

/-- A finite walk of exactly `len` decision arcs. The states include both endpoints. -/
structure DetMDP.Walk (M : DetMDP S) (len : ℕ) where
  v : Fin (len + 1) → S
  d : (j : Fin len) → M.D (v j.castSucc)
  step : ∀ j : Fin len, M.next (v j.castSucc) (d j) = v j.succ

def DetMDP.Walk.start {M : DetMDP S} {len : ℕ} (W : M.Walk len) : S :=
  W.v ⟨0, Nat.zero_lt_succ len⟩

def DetMDP.Walk.finish {M : DetMDP S} {len : ℕ} (W : M.Walk len) : S :=
  W.v ⟨len, Nat.lt_succ_self len⟩

def DetMDP.Walk.cost {M : DetMDP S} {len : ℕ} (W : M.Walk len) : ℝ :=
  ∑ j : Fin len, M.c (W.v j.castSucc) (W.d j)

/-- A state is reachable when some finite decision walk from the initial state ends there. -/
def DetMDP.Reachable (M : DetMDP S) (s₀ u : S) : Prop :=
  ∃ (len : ℕ) (W : M.Walk len), W.start = s₀ ∧ W.finish = u

/-- A directed simple cycle of decision arcs. Its states are distinct; a loop has length one. -/
structure DetMDP.Cycle (M : DetMDP S) where
  len : ℕ
  positive : 0 < len
  v : Fin len → S
  d : (j : Fin len) → M.D (v j)
  distinct : Function.Injective v
  step : ∀ j : Fin len,
    M.next (v j) (d j) = v ⟨(j.val + 1) % len, Nat.mod_lt _ positive⟩

def DetMDP.Cycle.base {M : DetMDP S} (C : M.Cycle) : S :=
  C.v ⟨0, C.positive⟩

noncomputable def DetMDP.Cycle.mean {M : DetMDP S} (C : M.Cycle) : ℝ :=
  (∑ j : Fin C.len, M.c (C.v j) (C.d j)) / C.len

/-- The min-plus adjacency entry, with infinity when there is no decision from `u` to `v`.
The infimum chooses the cheapest of parallel decision arcs. -/
noncomputable def DetMDP.A (M : DetMDP S) (u v : S) : WithTop ℝ :=
  Finset.univ.inf (fun d : M.D u =>
    if M.next u d = v then (M.c u d : WithTop ℝ) else ⊤)

/-- The `k`th min-plus power of the adjacency matrix. The zero-th power is the identity.
Using a recursion avoids treating infinity as a large real constant. -/
noncomputable def DetMDP.minPlusPow (M : DetMDP S) : ℕ → S → S → WithTop ℝ
  | 0, u, v => if u = v then 0 else ⊤
  | k + 1, u, v => Finset.univ.inf (fun w : S => M.minPlusPow k u w + M.A w v)

end MDPComplexity.AverageCost


