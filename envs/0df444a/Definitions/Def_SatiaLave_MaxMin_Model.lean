-- Prove2me | Definitions.Def_SatiaLave_MaxMin_Model
-- name    : SatiaLave_MaxMin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:36:08.75432+00:00
-- url     : https://prove2.me/theorems/cc71eafa-deea-46c2-9410-071762dd1cdc
-- title:
--   Discounted Markovian decision process with uncertain transition rows, present values, and the max-min return of criterion (2)
-- statement:
--   This file sets up the game-theoretic model of Satia and Lave.
--
--   **The process.** There are finitely many states $i$ (the paper's $1,\dots,N$). In state $i$ the decision maker chooses a decision $k$ from a finite, nonempty set $D_i$ (the paper's $1,\dots,K_i$); the decision set depends on the state. A transition from $i$ to $j$ under decision $k$ earns the reward $r^k_{ij}$, and rewards are discounted by the factor $\beta$ with $0\le\beta<1$.
--
--   **The uncertainty.** The transition probabilities are not known. For every state $i$ and decision $k$ there is a set $S_i^k$ of admissible **probability rows** $p_i^k=(p^k_{i1},\dots,p^k_{iN})$, with $p^k_{ij}\ge 0$ and $\sum_j p^k_{ij}=1$. As in the paper, every $S_i^k$ is closed and convex; in addition every $S_i^k$ is nonempty. Nature's choice is a matrix $P\in S$, i.e. one row $p_i^k\in S_i^k$ for every pair $(i,k)$.
--
--   **Policies and present values.** A pure stationary **policy** $A=(A_1,\dots,A_N)$ selects one decision $A_i\in D_i$ in each state. Under nature's choice $P$ it induces the transition matrix $P^A=(p^{A_i}_{ij})$, and its **present-value vector** is
--   $$v^A=[I-\beta P^A]^{-1}\Big(\sum_j p^{A_i}_{ij}\,r^{A_i}_{ij}\Big)_i ,$$
--   the vector the paper obtains by solving equations (5), $v_i^A=\sum_j p^{A_i}_{ij}\,(r^{A_i}_{ij}+\beta v_j^A)$.
--
--   **Max-min return.** Nature's minimum for policy $A$ in state $i$ is
--   $$\underline v_i(A)=\inf_{P\in S} v_i^A(P),$$
--   and the max-min return of criterion (2) is $\bar v_i=\max_A \underline v_i(A)$, the maximum over all pure stationary policies. A policy $A$ is **max-min optimal** if $\underline v_i(A)=\bar v_i$ for every $i$, and **$\varepsilon$-optimal** if $|\underline v_i(A)-\bar v_i|\le\varepsilon$ for every $i$ ("its returns are within $\pm\varepsilon$ of the optimal returns", p. 731).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** States are a finite nonempty type `S` and decisions a family `D : S → Type*` of finite nonempty types, a relabelling of $\{1,\dots,N\}$ and $\{1,\dots,K_i\}$. The paper never states the range of $\beta$; $0\le\beta<1$ is the standing reading (every return is an infinite discounted sum, and the proof of Proposition 4 uses the bound $r/(1-\beta)$). Nonemptiness of each $S_i^k$ is an addition: Phase 1 opens with "select any feasible probability row", which presupposes it. The present value is defined with the matrix inverse; that $I-\beta P^A$ is invertible and that this vector is the unique solution of (5) is the milestone `eq5_presentValue_unique`. The infimum defining nature's minimum is over the nonempty type of admissible choices `Sel M` and is bounded below by $\min r/(1-\beta)$, so it is never the junk value of an empty or unbounded infimum. Nature's choice is a fixed matrix $P\in S$, as in the paper's model.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, pp. 728-729 (model, definition of S_i^k and S) and p. 730, Eq. (5); p. 729, Eq. (2); p. 731 (definition of ε-optimal)

import Mathlib

namespace SatiaLave.MaxMin

open Finset

/-- A finite-state, discrete-time, discounted Markovian decision process whose transition
probabilities are uncertain (Satia–Lave 1973, pp. 728–729). States are the elements of the
finite type `S` (the paper's `1, …, N`); in state `i` the decisions are the elements of the
finite type `D i` (the paper's `1, …, K_i`). `r i k j` is the reward `r^k_ij` of a transition
`i → j` under decision `k`, `β` the discount factor, and `U i k` the set `S_i^k` of admissible
probability rows `p_i^k`. -/
structure UncertainMDP (S : Type*) [Fintype S] (D : S → Type*) where
  /-- the reward `r^k_ij` -/
  r : (i : S) → D i → S → ℝ
  /-- the discount factor `β` -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the uncertainty set `S_i^k` of probability rows -/
  U : (i : S) → D i → Set (S → ℝ)
  /-- every admissible row is a probability row -/
  U_subset : ∀ i k, U i k ⊆ stdSimplex ℝ S
  /-- "`S_i^k` is a closed convex set for all `i` and all `k`" -/
  U_closed : ∀ i k, IsClosed (U i k)
  U_convex : ∀ i k, Convex ℝ (U i k)
  /-- (added) every uncertainty set contains a feasible row -/
  U_nonempty : ∀ i k, (U i k).Nonempty

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}

/-- A pure stationary policy `A = (A_1, …, A_N)`: one decision in each state. -/
abbrev Policy (S : Type*) (D : S → Type*) := (i : S) → D i

/-- Nature's choice `P ∈ S`: one admissible probability row `P i k ∈ S_i^k` for every state
`i` and every decision `k`. -/
def Sel (M : UncertainMDP S D) : Type _ :=
  {P : (i : S) → D i → S → ℝ // ∀ i k, P i k ∈ M.U i k}

/-- The transition matrix `P^A = (p^A_ij)` of policy `A` under nature's choice `P`. -/
def transMat (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) : Matrix S S ℝ :=
  Matrix.of fun i j => P.1 i (A i) j

/-- The one-step expected reward `Σ_j p^A_ij r^A_ij` of policy `A` under `P`. -/
def rewardVec (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) : S → ℝ :=
  fun i => ∑ j, P.1 i (A i) j * M.r i (A i) j

/-- `v` solves the present-value equations (5) for policy `A` under `P`:
`v_i = Σ_j p^A_ij (r^A_ij + β v_j)` for every state `i`. -/
def SolvesEq5 (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (v : S → ℝ) : Prop :=
  ∀ i, v i = ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * v j)

/-- The present-value vector `v^A = [I − βP^A]⁻¹ (Σ_j p^A_ij r^A_ij)_i` of policy `A` under
nature's choice `P`. -/
noncomputable def presentValue (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) : S → ℝ :=
  Matrix.mulVec (1 - M.β • transMat M A P)⁻¹ (rewardVec M A P)

/-- Nature's minimum for policy `A` in state `i`: the infimum, over all admissible choices
`P ∈ S`, of the present value of `A` in state `i`. -/
noncomputable def robustValue (M : UncertainMDP S D) (A : Policy S D) (i : S) : ℝ :=
  ⨅ P : Sel M, presentValue M A P i

variable [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

/-- The max-min return of criterion (2) in state `i`: the maximum over all pure stationary
policies of nature's minimum. -/
noncomputable def maxMinValue (M : UncertainMDP S D) (i : S) : ℝ :=
  (Finset.univ : Finset (Policy S D)).sup' Finset.univ_nonempty (fun A => robustValue M A i)

/-- `A` is max-min optimal: its max-min return equals the optimal max-min return in every
state. -/
def IsMaxMinOptimal (M : UncertainMDP S D) (A : Policy S D) : Prop :=
  ∀ i, robustValue M A i = maxMinValue M i

/-- `A` is `ε`-optimal (p. 731): its returns are within `±ε` of the optimal returns. -/
def IsEpsMaxMinOptimal (M : UncertainMDP S D) (ε : ℝ) (A : Policy S D) : Prop :=
  ∀ i, |robustValue M A i - maxMinValue M i| ≤ ε

end SatiaLave.MaxMin


