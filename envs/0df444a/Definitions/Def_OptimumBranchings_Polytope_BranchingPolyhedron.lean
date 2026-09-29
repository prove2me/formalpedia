-- Prove2me | Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron
-- name    : OptimumBranchings_Polytope_BranchingPolyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:51:54.621984+00:00
-- url     : https://prove2.me/theorems/7fc5bab4-197f-4ed0-b25d-cd5876663f8b
-- title:
--   The polyhedron $P_G$ of the system $(L_1)$–$(L_3)$, and vertices (§5)
-- statement:
--   Let $G$ be a directed graph with node set $V$ and edge set $E$ (parallel edges allowed, no loops). The polyhedron $P_G\subseteq\mathbb R^{E}$ is the set of vectors $x=(x_e)_{e\in E}$ satisfying
--
--   1. $(L_1)$ $x_e\ge 0$ for every edge $e$;
--   2. $(L_2)$ for every node $v$, $\sum_{e:\ \mathrm{front}(e)=v} x_e\le 1$;
--   3. $(L_3)$ for every set $S$ of two or more nodes,
--   $$
--   \sum_{e:\ \mathrm{front}(e)\in S,\ \mathrm{rear}(e)\in S} x_e\;\le\;|S|-1 .
--   $$
--
--   A **vertex** (extreme point) of a set $P\subseteq\mathbb R^{E}$ is a point $x\in P$ for which there is a linear function $y\mapsto\sum_e c_e y_e$ such that $x$ is the unique point of $P$ maximizing it: $\sum_e c_e y_e<\sum_e c_e x_e$ for every $y\in P$ with $y\neq x$.
--
--   $P_G$ is the feasible region of the linear programming relaxation of the optimum branching problem; Edmonds' Theorem 2 identifies its vertices.
--
--   **Formalization Note** $P_G$ is written directly as the solution set of $(L_1)$–$(L_3)$ in `E → ℝ`; the right side of $(L_3)$ is the real number $|S|-1$. The vertex notion is the paper's "unique maximizer of some linear function" (equivalently Mathlib's exposed points), stated for an arbitrary set of vectors.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), p. 235, Section 5, (L_1)–(L_3); p. 236 (definition of polyhedron and vertex)

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph

namespace OptimumBranchings.Polytope

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The polyhedron `P_G` (§5, p. 235): the set of real vectors `x = [x_e]`, one coordinate per
edge, satisfying the system `L_G`:
* (L₁) `x e ≥ 0` for every edge `e`;
* (L₂) for every node `v`, the sum of `x e` over the edges directed toward `v` is at most `1`;
* (L₃) for every set `S` of two or more nodes, the sum of `x e` over the edges with both ends
  in `S` is at most `|S| - 1`. -/
def branchingPolyhedron (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧
    (∀ v : V, ∑ e ∈ Finset.univ.filter (fun e => G.front e = v), x e ≤ 1) ∧
    (∀ S : Finset V, 2 ≤ S.card →
      ∑ e ∈ Finset.univ.filter (fun e => G.front e ∈ S ∧ G.rear e ∈ S), x e
        ≤ (S.card : ℝ) - 1)}

/-- A *vertex* (extreme point) of a set `P` of vectors (§5, p. 236): a point `x` which, for some
linear function `y ↦ ∑ e, c e * y e`, is the unique point in `P` maximizing that function. -/
def IsVertex (P : Set (E → ℝ)) (x : E → ℝ) : Prop :=
  x ∈ P ∧ ∃ c : E → ℝ, ∀ y ∈ P, y ≠ x → ∑ e, c e * y e < ∑ e, c e * x e

end OptimumBranchings.Polytope


