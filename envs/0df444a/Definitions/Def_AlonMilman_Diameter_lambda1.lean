-- Prove2me | Definitions.Def_AlonMilman_Diameter_lambda1
-- name    : AlonMilman_Diameter_lambda1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:24:36.225354+00:00
-- url     : https://prove2.me/theorems/41e7ef9c-4714-42d7-a7c9-efe6529cc36b
-- title:
--   $\lambda_1(G)$: second-smallest eigenvalue of the Laplacian $Q = D - A_G$
-- statement:
--   Let $G = (V, E)$ be a finite simple graph on $n = |V|$ vertices, let $d(v)$ be the degree of the vertex $v$ and $A_G$ the adjacency matrix of $G$. The **Laplacian** of $G$ is the real symmetric $V \times V$ matrix
--   $$
--   Q = Q_G = \operatorname{diag}(d(v))_{v \in V} - A_G .
--   $$
--   (Equivalently $Q = C^{\mathsf T} C$ for the incidence matrix $C$ of any orientation of $G$.) Being symmetric and positive semidefinite, $Q$ has real eigenvalues $0 = \lambda_0 \le \lambda_1 \le \cdots \le \lambda_{n-1}$, listed with multiplicity. This definition sets
--   $$
--   \lambda_1(G) := \text{the second-smallest eigenvalue of } Q_G \text{, counted with multiplicity,}
--   $$
--   for every graph with $n \ge 2$ vertices.
--
--   $\lambda_1(G)$ is Fiedler's **algebraic connectivity**; it is positive exactly when $G$ is connected, and every result of the mission bounds a metric or isoperimetric quantity of $G$ in terms of it.
--
--   **Formalization Note** The Laplacian is Mathlib's `SimpleGraph.lapMatrix ℝ` (`degMatrix - adjMatrix`). Mathlib's `Matrix.IsHermitian.eigenvalues₀` lists the eigenvalues in *decreasing* order, indexed by `Fin n`; index $n-1$ is the smallest eigenvalue $\lambda_0$ and index $n-2$ is $\lambda_1$. For $n < 2$, where $\lambda_1$ does not exist, the definition returns $0$; every theorem of the mission assumes $n \ge 2$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 76, Section 2 (definition of Q and of λ₁)

import Mathlib

namespace AlonMilman.Diameter

/-- `λ₁(G)`: the second-smallest eigenvalue, counted with multiplicity, of the Laplacian
`Q = diag(d(v)) − A_G` (`G.lapMatrix ℝ`) of a finite simple graph `G`.
Mathlib's `eigenvalues₀` lists the eigenvalues in decreasing order, so index `card V - 1` is the
smallest eigenvalue `λ₀` and index `card V - 2` is `λ₁`. For graphs with fewer than two vertices
`λ₁` does not exist and the value is `0` by convention. -/
noncomputable def lambda1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  if h : 2 ≤ Fintype.card V then
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩
  else 0

end AlonMilman.Diameter


