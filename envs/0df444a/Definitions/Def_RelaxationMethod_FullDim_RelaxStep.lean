-- Prove2me | Definitions.Def_RelaxationMethod_FullDim_RelaxStep
-- name    : RelaxationMethod_FullDim_RelaxStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:24:26.40696+00:00
-- url     : https://prove2.me/theorems/e4098c45-7e50-43eb-934a-cc5f3ad01a01
-- title:
--   The relaxation step (1.5)–(1.7) for a system of linear inequalities
-- statement:
--   Work in the $n$-dimensional Euclidean space $E_n$. A system of $m$ linear inequalities
--
--   $$
--   \sum_{j=1}^n a_{ij}x_j + b_i \ge 0 \qquad (i = 1,\dots,m)
--   $$
--
--   is given by the rows $a_i = (a_{i1},\dots,a_{in}) \in E_n$ and the constants $b_i \in \mathbb R$. Each inequality defines the **closed half-space** $H_i = \{x : \langle a_i, x\rangle + b_i \ge 0\}$, and the solution set of the system is the **polytope** $A = \bigcap_{i=1}^m H_i$.
--
--   Fix a **relaxation parameter** $\lambda$. A point $p'$ is obtained from $p$ by a **relaxation step** if there is an index $j$ and a point $q$ such that
--
--   1. $H_j$ is a farthest half-space from $p$: $\operatorname{dist}(p, H_j) = \max_i \operatorname{dist}(p, H_i)$;
--   2. $q \in H_j$ realizes that distance: $|p - q| = \operatorname{dist}(p, H_j)$;
--   3. $p' = p + \lambda (q - p)$.
--
--   A **run** of the relaxation process is a sequence $p_0, p_1, p_2, \dots$ such that $p_{\nu+1}$ arises from $p_\nu$ by a relaxation step whenever $p_\nu \notin A$. When some $p_N \in A$ the process has terminated, and the later terms of the sequence carry no meaning.
--
--   These are the objects (1.2)–(1.9) of Motzkin and Schoenberg: $\lambda \in (0,2)$ is the relaxation method, $\lambda = 2$ (where $p'$ is the mirror image of $p$ in the boundary hyperplane of $H_j$) the reflexion method.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)`, the row $a_i$ is a vector `a i` and $\sum_j a_{ij}x_j$ is `inner ℝ (a i) x`; distances to sets are `Metric.infDist`. The parameter $\lambda$ is named `lam` because `λ` is a Lean keyword. The paper makes the step single-valued by "some pre-assigned rule for choosing $j$" when the maximizer in (1.5) is not unique; here the step is a relation that allows every maximizing $j$ at every step, so a statement about all runs covers every such rule.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), pp. 393–394, (1.2)–(1.9)

import Mathlib

namespace RelaxationMethod.FullDim

/-- The closed half-space `H : ⟨u, x⟩ + c ≥ 0` of (1.3): the `i`-th inequality of (1.2) with
coefficient row `u = (a_{i1}, …, a_{in})` and constant term `c = b_i`. -/
def halfSpace {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (c : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | 0 ≤ inner ℝ u x + c}

/-- The solution set `A = ⋂_{i=1}^m H_i` of the system (1.2), the convex polytope (1.4). -/
def polytope {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ⋂ i, halfSpace (a i) (b i)

/-- One relaxation step (1.5)–(1.7) with relaxation parameter `lam` (the paper's `λ`):
`p'` arises from `p` by choosing an index `j` of a farthest half-space,
`dist (p, H_j) = max_i dist (p, H_i)` (1.5), a point `q ∈ H_j` with
`|p - q| = dist (p, H_j)` (1.6), and setting `p' = p + lam (q - p)` (1.7).
Every maximizing `j` is allowed, so this relation contains every pre-assigned tie-breaking
rule of (1.8). -/
def IsRelaxStep {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ) (lam : ℝ)
    (p p' : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ j : Fin m,
    (∀ i : Fin m, Metric.infDist p (halfSpace (a i) (b i)) ≤
      Metric.infDist p (halfSpace (a j) (b j))) ∧
    ∃ q ∈ halfSpace (a j) (b j),
      dist p q = Metric.infDist p (halfSpace (a j) (b j)) ∧ p' = p + lam • (q - p)

/-- A run of the relaxation process (1.9): a sequence `p₀, p₁, …` in which every point that lies
outside the polytope `A` is followed by a relaxation step. Once a point of `A` is reached the
process has terminated and the later terms are irrelevant. -/
def IsRelaxRun {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ) (lam : ℝ)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ν : ℕ, p ν ∉ polytope a b → IsRelaxStep a b lam (p ν) (p (ν + 1))

end RelaxationMethod.FullDim


