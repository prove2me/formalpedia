-- Prove2me | Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
-- name    : ExplicitExpanders_Delete_IsNDLambda
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:55:49.823208+00:00
-- url     : https://prove2.me/theorems/8e2b84d6-3d96-43de-930d-f5dd28739520
-- title:
--   $(n,d,\lambda)$-graph (Section 1)
-- statement:
--   Let $A$ be a real symmetric matrix indexed by a finite set $V$, and let $\mathbf 1$ denote the all-ones vector on $V$. We say that $A$ is an **$(n,d,\lambda)$-matrix** if
--
--   1. $|V| = n$;
--   2. every row of $A$ sums to $d$, that is, $A\mathbf 1 = d\,\mathbf 1$;
--   3. every eigenvalue $\mu$ of $A$ that has an eigenvector $f \neq 0$ with $\sum_{v\in V} f(v) = 0$ satisfies
--   $$|\mu| \le \lambda .$$
--
--   A simple graph $G$ on $V$ is an **$(n,d,\lambda)$-graph** if it is $d$-regular and its adjacency matrix $A_G$ is an $(n,d,\lambda)$-matrix. This is the notion of Section 1 of the paper: a $d$-regular graph on $n$ vertices in which the absolute value of every nontrivial eigenvalue is at most $\lambda$.
--
--   Here the trivial eigenvalue is the top eigenvalue $d$, with the constant eigenvector. Since $A$ is symmetric and fixes $\mathbf 1$, the orthogonal complement $\{f : \sum_v f(v) = 0\}$ is invariant under $A$, and the eigenvalues of $A$ on that complement are exactly the eigenvalues of $A$ with one copy of $d$ removed. Condition 3 is therefore the paper's "every nontrivial eigenvalue": if $G$ is disconnected, the second copy of $d$ is nontrivial and condition 3 forces $\lambda \ge d$.
--
--   **Formalization Note** The predicate is split into a matrix-level part `IsNDLambdaMatrix` (symmetry, $|V| = n$, row sums, and the eigenvalue bound on eigenvectors orthogonal to $\mathbf 1$) and the graph-level `IsNDLambda`, which adds `G.IsRegularOfDegree d` for the adjacency matrix `G.adjMatrix ℝ`. Decidability of adjacency is supplied classically inside the definition, so the predicate applies to any graph on a finite vertex type.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 1, Section 1 (definition of (n, d, λ)-graph)

import Mathlib

namespace ExplicitExpanders.Delete

open Matrix

/-- Matrix level of an `(n, d, λ)`-graph (Alon, *Explicit expanders of every degree and size*,
arXiv:2003.11673v1, §1, p. 1): `A` is a real symmetric matrix indexed by a set of `n` vertices,
every row sums to `d` (so the constant vector is an eigenvector with the trivial eigenvalue `d`),
and every eigenvalue `μ` with an eigenvector orthogonal to the constant vector satisfies
`|μ| ≤ lam`. For a symmetric matrix fixing the constant vector, these are exactly the eigenvalues
other than one copy of `d`. -/
def IsNDLambdaMatrix {V : Type*} [Fintype V] (A : Matrix V V ℝ) (n d : ℕ) (lam : ℝ) : Prop :=
  A.IsSymm ∧ Fintype.card V = n ∧
    A *ᵥ (fun _ => (1 : ℝ)) = (d : ℝ) • (fun _ => (1 : ℝ)) ∧
    ∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → ∑ v, f v = 0 → A *ᵥ f = μ • f → |μ| ≤ lam

open Classical in
/-- `G` is an `(n, d, λ)`-graph (Alon, arXiv:2003.11673v1, §1, p. 1): a `d`-regular simple graph
on `n` vertices in which every nontrivial eigenvalue of the adjacency matrix has absolute value at
most `lam`. -/
def IsNDLambda {V : Type*} [Fintype V] (G : SimpleGraph V) (n d : ℕ) (lam : ℝ) : Prop :=
  G.IsRegularOfDegree d ∧ IsNDLambdaMatrix (G.adjMatrix ℝ) n d lam

end ExplicitExpanders.Delete


