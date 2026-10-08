-- Prove2me | Definitions.Def_MDPComplexity_StationaryHorizon_Model
-- name    : MDPComplexity_StationaryHorizon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:33:01.144394+00:00
-- url     : https://prove2.me/theorems/ed1bee56-ad6d-4f4d-9de6-f3f90bd82497
-- title:
--   Finite stationary deterministic processes, decision walks and cycle decompositions
-- statement:
--   A **stationary deterministic Markov decision process** consists of a finite state set $S$ and, at every state $s$, a finite nonempty decision set $D_s$. Each decision $d\in D_s$ has a successor $\operatorname{next}(s,d)\in S$ and a real cost $c(s,d)$. Distinct decisions may share endpoints, so the associated directed graph allows parallel arcs and loops.
--
--   A **policy** $\delta(s,t)$ chooses a decision at each state and time. From $s_0$ it gives a trajectory $s_{t+1}=\operatorname{next}(s_t,\delta(s_t,t))$. For a horizon of $T$ arcs, the cost and optimum are
--
--   $$J_T(s_0,\delta)=\sum_{t=0}^{T-1}c(s_t,\delta(s_t,t)),\qquad J_T^*(s_0)=\inf_{\delta}J_T(s_0,\delta).$$
--
--   A **walk** of $l$ arcs records its $l+1$ states and the decision used for each arc. A simple path has no repeated state. A simple cycle has positive length, returns to its first state, and has distinct states before the return. A cycle decomposition records a simple residual path and removed simple cycles, preserving the original walk's arc count, endpoints, cost, and multiset of decision arcs; each cycle is based at a state of the original walk.
--
--   These objects express the graph claims in the argument for Theorem 5.
--
--   **Formalization Note** The paper's §2 finite-horizon sum has $T+1$ decisions, whereas the paragraph before Theorem 5 explicitly uses a $T$-arc walk. This mission follows that paragraph, with decisions at $t=0,\ldots,T-1$. The optimum is over all time-dependent policies $\delta(s,t)$. Nonempty decision sets make a policy and walks of every finite length possible; this is implicit in the paper's policy definition. State labels are 0-based in Lean.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), pp. 444–445 §2 and §3, and p. 447 The finite horizon, stationary case, https://doi.org/10.1287/moor.12.3.441

import Mathlib

namespace MDPComplexity.StationaryHorizon

/-- The stationary deterministic case of Papadimitriou--Tsitsiklis, §§2--3. A decision is
an arc, so different decisions may have the same endpoints and loops are permitted. -/
structure DetMDP (S : Type) [Fintype S] where
  D : S → Type
  [finiteD : ∀ s, Fintype (D s)]
  [nonemptyD : ∀ s, Nonempty (D s)]
  next : (s : S) → D s → S
  c : (s : S) → D s → ℝ

attribute [instance] DetMDP.finiteD DetMDP.nonemptyD

variable {S : Type} [Fintype S]

/-- The paper's time-dependent Markov policy `δ(s,t)`. -/
def DetMDP.Policy (M : DetMDP S) := (s : S) → ℕ → M.D s

/-- The state at time `t` under a policy, beginning at `s₀`. -/
def DetMDP.path (M : DetMDP S) (s₀ : S) (δ : M.Policy) : ℕ → S
  | 0 => s₀
  | t + 1 => M.next (M.path s₀ δ t) (δ (M.path s₀ δ t) t)

/-- The cost of the decision taken at time `t`. -/
def DetMDP.stageCost (M : DetMDP S) (s₀ : S) (δ : M.Policy) (t : ℕ) : ℝ :=
  M.c (M.path s₀ δ t) (δ (M.path s₀ δ t) t)

/-- The §3 horizon `T` has exactly `T` decisions, hence `T` graph arcs. -/
def DetMDP.horizonCost (M : DetMDP S) (s₀ : S) (δ : M.Policy) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, M.stageCost s₀ δ t

/-- The optimum ranges over all policies `δ(s,t)`, not just stationary policies. -/
noncomputable def DetMDP.optHorizon (M : DetMDP S) (s₀ : S) (T : ℕ) : ℝ :=
  ⨅ δ : M.Policy, M.horizonCost s₀ δ T

/-- A directed `l`-arc walk, retaining its decisions as arcs. -/
structure DetMDP.Walk (M : DetMDP S) (l : ℕ) where
  x : Fin (l + 1) → S
  e : (t : Fin l) → M.D (x t.castSucc)
  valid : ∀ t : Fin l, M.next (x t.castSucc) (e t) = x t.succ

/-- The sum of the weights of a walk's decision arcs. -/
def DetMDP.Walk.cost (M : DetMDP S) {l : ℕ} (W : M.Walk l) : ℝ :=
  ∑ t : Fin l, M.c (W.x t.castSucc) (W.e t)

/-- The multiset of decision arcs in a walk. It distinguishes parallel decisions and
retains multiplicity when a cycle is traversed repeatedly. -/
def DetMDP.Walk.arcs (M : DetMDP S) {l : ℕ} (W : M.Walk l) :
    Multiset (Σ s : S, M.D s) :=
  Multiset.ofList (List.ofFn (fun t : Fin l => ⟨W.x t.castSucc, W.e t⟩))

/-- A walk with no repeated vertex, including the endpoint. -/
def DetMDP.Walk.IsSimplePath (M : DetMDP S) {l : ℕ} (W : M.Walk l) : Prop :=
  Function.Injective W.x

/-- A positive-length closed walk whose vertices before the last are distinct. A loop is a
simple cycle of length one. -/
def DetMDP.Walk.IsSimpleCycle (M : DetMDP S) {l : ℕ} (W : M.Walk l) : Prop :=
  0 < l ∧ W.x 0 = W.x ⟨l, Nat.lt_succ_self l⟩ ∧
    Function.Injective (fun t : Fin l => W.x t.castSucc)

/-- The numerical cycle-removal decomposition used in the proof of Theorem 5. The residual
walk is simple and has the original endpoints; each removed simple cycle is based at a vertex
of the original walk. Arc counts and costs are preserved. -/
def DetMDP.IsCycleDecomposition (M : DetMDP S) {l p : ℕ} (W : M.Walk l)
    (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)) : Prop :=
  P.IsSimplePath ∧ P.x 0 = W.x 0 ∧
    P.x ⟨p, Nat.lt_succ_self p⟩ = W.x ⟨l, Nat.lt_succ_self l⟩ ∧
    p + (Cs.map (fun C => C.1)).sum = l ∧
    P.cost + (Cs.map (fun C => C.2.cost)).sum = W.cost ∧
    P.arcs + (Cs.map (fun C => C.2.arcs)).sum = W.arcs ∧
    ∀ C ∈ Cs, C.2.IsSimpleCycle ∧ ∃ t : Fin (l + 1), W.x t = C.2.x 0

end MDPComplexity.StationaryHorizon


