-- Prove2me | Definitions.Def_AssignmentGame_CoreCorners_Game
-- name    : AssignmentGame_CoreCorners_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:21:37.193113+00:00
-- url     : https://prove2.me/theorems/b93964db-50be-4aeb-b7d4-9fc8f4d7da22
-- title:
--   Assignment game: characteristic function (2.6), core, and the extremal core payoffs $u^*, u_*, v^*, v_*$
-- statement:
--   Let $M$ be a finite set of sellers and $N$ a finite set of buyers ($|M| = m$ and $|N| = n$ need not be equal, and either set may be empty), and let $a = (a_{ij})_{i \in M, j \in N}$ be a real matrix, where $a_{ij}$ is the gain that seller $i$ and buyer $j$ can realize by trading with each other.
--
--   1. A **matching** inside a coalition with seller part $A \subseteq M$ and buyer part $B \subseteq N$ is a set $P \subseteq A \times B$ of seller–buyer pairs in which no seller and no buyer occurs twice.
--   2. The **characteristic function** (2.6) assigns to the coalition $(A, B)$ the largest total gain of a matching inside it,
--   $$\operatorname{worth}(A, B) = \max_{P} \sum_{(i,j) \in P} a_{ij},$$
--   the maximum being over all matchings $P$ inside $(A, B)$ (the empty matching is allowed, so the worth is at least $0$).
--   3. The **core** is the set of payoff vectors $(u, v) \in \mathbb{R}^M \times \mathbb{R}^N$ with
--   $$\sum_{i \in M} u_i + \sum_{j \in N} v_j = \operatorname{worth}(M, N) \quad (3.5), \qquad \sum_{i \in A} u_i + \sum_{j \in B} v_j \ge \operatorname{worth}(A, B) \text{ for all } A \subseteq M,\ B \subseteq N \quad (3.6).$$
--   4. For each seller $i$, $u^*_i$ and $u_{*i}$ are the supremum and the infimum of $u_i$ over all $(u, v)$ in the core; for each buyer $j$, $v^*_j$ and $v_{*j}$ are the supremum and the infimum of $v_j$ over the core.
--
--   These are the objects of Theorem 3 of Shapley and Shubik: the core of the assignment game and the highest and lowest payoff each player receives in it.
--
--   **Formalization Note** A coalition $S \subseteq M \cup N$ is encoded as the pair $(A, B) = (S \cap M, S \cap N)$. The paper's maximum over $k = \min(|S \cap M|, |S \cap N|)$ disjoint pairs is replaced by the maximum over matchings of any size; the two agree when $a_{ij} \ge 0$, which every theorem of the mission assumes. The characteristic function is named `worth` because `v` denotes the buyers' payoffs. The extremal payoffs are defined with `sSup`/`sInf` on $\mathbb{R}$, which return $0$ on an empty or unbounded set; the mission's milestones state that the core is nonempty and bounded, which is what makes these definitions the true extrema. Core vectors are automatically nonnegative (singleton coalitions have worth $0$), so they are imputations in the paper's sense (p. 118, footnote 2).
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), pp. 114-115, Sec. 2.2, Eqs. (2.3)-(2.6); p. 118, Eqs. (3.5)-(3.6); p. 121, Theorem 3 (definition of u*_i, u_*i, v*_j, v_*j)

import Mathlib

namespace AssignmentGame.CoreCorners

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
theorem empty_mem_matchings (A : Finset M) (B : Finset N) :
    (∅ : Finset (M × N)) ∈ matchings A B := by
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

/-- `u*_i` (Theorem 3, p. 121): the highest payoff to seller `i` over all imputations in the core,
taken as the supremum of `{u_i : (u, v) ∈ core a}`. -/
noncomputable def uHi (a : M → N → ℝ) (i : M) : ℝ :=
  sSup ((fun p : (M → ℝ) × (N → ℝ) => p.1 i) '' core a)

/-- `u_{*i}` (Theorem 3, p. 121): the lowest payoff to seller `i` over all imputations in the
core, taken as the infimum of `{u_i : (u, v) ∈ core a}`. -/
noncomputable def uLo (a : M → N → ℝ) (i : M) : ℝ :=
  sInf ((fun p : (M → ℝ) × (N → ℝ) => p.1 i) '' core a)

/-- `v*_j` (Theorem 3, p. 121): the highest payoff to buyer `j` over all imputations in the core,
taken as the supremum of `{v_j : (u, v) ∈ core a}`. -/
noncomputable def vHi (a : M → N → ℝ) (j : N) : ℝ :=
  sSup ((fun p : (M → ℝ) × (N → ℝ) => p.2 j) '' core a)

/-- `v_{*j}` (Theorem 3, p. 121): the lowest payoff to buyer `j` over all imputations in the
core, taken as the infimum of `{v_j : (u, v) ∈ core a}`. -/
noncomputable def vLo (a : M → N → ℝ) (j : N) : ℝ :=
  sInf ((fun p : (M → ℝ) × (N → ℝ) => p.2 j) '' core a)

end AssignmentGame.CoreCorners


