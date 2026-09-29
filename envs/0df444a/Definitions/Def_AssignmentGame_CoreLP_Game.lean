-- Prove2me | Definitions.Def_AssignmentGame_CoreLP_Game
-- name    : AssignmentGame_CoreLP_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:03:03.569337+00:00
-- url     : https://prove2.me/theorems/fba63d6a-778c-4563-b185-8d4faf216ef6
-- title:
--   Assignment game: characteristic function (2.6), core (3.5)–(3.6), and the assignment LP and its dual (3.1)–(3.4)
-- statement:
--   Let $M$ be a finite set of sellers and $N$ a finite set of buyers (either may be empty, and $|M|$, $|N|$ need not be equal), and let $a = (a_{ij})_{i \in M, j \in N}$ be a real matrix; $a_{ij}$ is the profit that the partnership of seller $i$ and buyer $j$ can realise.
--
--   1. **Coalitions and matchings.** A coalition $S \subseteq M \cup N$ is described by its sellers $A = S \cap M$ and its buyers $B = S \cap N$. A *matching* inside $(A, B)$ is a set $P$ of pairs $(i, j)$ with $i \in A$, $j \in B$, in which no seller and no buyer occurs twice.
--   2. **Characteristic function (2.6).** The worth of the coalition is
--   $$v(S) = \operatorname{worth}_a(A, B) = \max_{P \text{ matching in } (A,B)} \sum_{(i,j) \in P} a_{ij},$$
--   the maximum always existing because the empty matching (value $0$) is one of finitely many matchings.
--   3. **Core (3.5)–(3.6).** A payoff vector is a pair $(u, v)$ with $u \in \mathbb R^M$, $v \in \mathbb R^N$. It is in the core when
--   $$\sum_{i \in M} u_i + \sum_{j \in N} v_j = v(M \cup N) \quad\text{and}\quad \sum_{i \in A} u_i + \sum_{j \in B} v_j \ge \operatorname{worth}_a(A,B) \text{ for all } A \subseteq M,\ B \subseteq N.$$
--   4. **Primal assignment LP (3.1)–(3.2).** $x \in \mathbb R^{M \times N}$ is feasible when $x_{ij} \ge 0$, $\sum_{i \in M} x_{ij} \le 1$ for every $j$ and $\sum_{j \in N} x_{ij} \le 1$ for every $i$; its objective value is $z = \sum_{i \in M}\sum_{j \in N} a_{ij} x_{ij}$.
--   5. **Dual LP (3.3)–(3.4).** $(u, v)$ is dual feasible when $u_i \ge 0$, $v_j \ge 0$ and $u_i + v_j \ge a_{ij}$ for all $i \in M$, $j \in N$; its objective value is $w = \sum_{i} u_i + \sum_j v_j$. It is *dual optimal* when it is dual feasible and $w(u,v) \le w(u',v')$ for every dual-feasible $(u', v')$.
--
--   These are the objects of Shapley and Shubik's assignment game; the core and the dual LP are defined independently of each other, and the worth is the combinatorial maximum, not an LP value.
--
--   **Formalization Note** The worth maximises over all partial matchings inside the coalition rather than over exactly $k = \min(|S\cap M|, |S \cap N|)$ pairs as (2.6) is printed; for $a \ge 0$, the paper's standing assumption, the two maxima coincide (a partial matching can be completed to $k$ pairs without decreasing the sum). The letter $v$ is used in the paper both for the characteristic function and for buyers' payoffs; Lean calls the former `worth`, and payoff vectors are pairs `p : (M → ℝ) × (N → ℝ)` with `p.1 = u`, `p.2 = v`. The nonnegativity clause of an imputation is not part of `core`: it follows from the singleton coalitions.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), pp. 114-115, Sec. 2.2, Eqs. (2.3)-(2.6); p. 116, Sec. 2.3; pp. 117-118, Sec. 3.1, Eqs. (3.1)-(3.6)

import Mathlib

namespace AssignmentGame.CoreLP

open Finset

variable {M N : Type*} [Fintype M] [Fintype N]

/-- A (partial) matching inside the coalition whose sellers are `A` and whose buyers are `B`:
a set `P` of seller–buyer pairs with every seller in `A`, every buyer in `B`, and no seller and
no buyer occurring in two different pairs. -/
def IsMatching (A : Finset M) (B : Finset N) (P : Finset (M × N)) : Prop :=
  P ⊆ A ×ˢ B ∧ (∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q) ∧ (∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → p = q)

/-- The finite set of all matchings inside the coalition `(A, B)`. -/
noncomputable def matchings (A : Finset M) (B : Finset N) : Finset (Finset (M × N)) :=
  open Classical in (A ×ˢ B).powerset.filter (IsMatching A B)

omit [Fintype M] [Fintype N] in
/-- The empty matching lies inside every coalition. -/
theorem empty_mem_matchings (A : Finset M) (B : Finset N) : (∅ : Finset (M × N)) ∈ matchings A B := by
  simp [matchings, IsMatching]

/-- The characteristic function (2.6) of the assignment game with matrix `a`: the worth of the
coalition `S` with `S ∩ M = A` and `S ∩ N = B` is the largest total `∑_{(i,j) ∈ P} a i j` over
matchings `P` inside `(A, B)`. -/
noncomputable def worth (a : M → N → ℝ) (A : Finset M) (B : Finset N) : ℝ :=
  (matchings A B).sup' ⟨∅, empty_mem_matchings A B⟩ (fun P => ∑ p ∈ P, a p.1 p.2)

/-- The core (p. 118, (3.5)–(3.6)): payoff vectors `(u, v)` that distribute exactly the worth of
the all-player coalition `M ∪ N` and give every coalition at least its worth. -/
def core (a : M → N → ℝ) : Set ((M → ℝ) × (N → ℝ)) :=
  {p | ∑ i, p.1 i + ∑ j, p.2 j = worth a univ univ ∧
    ∀ (A : Finset M) (B : Finset N), worth a A B ≤ ∑ i ∈ A, p.1 i + ∑ j ∈ B, p.2 j}

/-- Primal feasibility (3.1): `x i j ≥ 0`, every column sum `∑_i x i j ≤ 1`, every row sum
`∑_j x i j ≤ 1`. -/
def PrimalFeasible (x : M → N → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ j, ∑ i, x i j ≤ 1) ∧ (∀ i, ∑ j, x i j ≤ 1)

/-- The primal objective (3.2): `z = ∑_i ∑_j a i j * x i j`. -/
def primalObj (a : M → N → ℝ) (x : M → N → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * x i j

/-- Dual feasibility (3.3): `u i ≥ 0`, `v j ≥ 0`, and `u i + v j ≥ a i j` for all `i, j`. -/
def DualFeasible (a : M → N → ℝ) (p : (M → ℝ) × (N → ℝ)) : Prop :=
  (∀ i, 0 ≤ p.1 i) ∧ (∀ j, 0 ≤ p.2 j) ∧ ∀ i j, a i j ≤ p.1 i + p.2 j

/-- The dual objective (3.4): `w = ∑_i u i + ∑_j v j`. -/
def dualObj (p : (M → ℝ) × (N → ℝ)) : ℝ :=
  ∑ i, p.1 i + ∑ j, p.2 j

/-- An optimal solution of the dual LP: a dual-feasible `(u, v)` minimizing (3.4) among all
dual-feasible vectors. -/
def DualOptimal (a : M → N → ℝ) (p : (M → ℝ) × (N → ℝ)) : Prop :=
  DualFeasible a p ∧ ∀ q, DualFeasible a q → dualObj p ≤ dualObj q

end AssignmentGame.CoreLP


