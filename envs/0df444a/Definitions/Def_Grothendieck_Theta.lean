-- Prove2me | Definitions.Def_Grothendieck_Theta
-- name    : Grothendieck_Theta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-02T04:13:53.999195+00:00
-- url     : https://prove2.me/theorems/b28071b9-4cf3-40a5-923d-350c343f81b1
-- title:
--   The Lovász theta number of the complement of a graph
-- statement:
--   Let $G=(V,E)$ be a finite graph. The **Lovász theta number of the complement of $G$**, written $\vartheta(G)$, is the optimal value of the semidefinite program
--
--   $$
--   \vartheta(G)=\min\big\{\lambda\;:\;Z\in\mathbb R^{V\times V}\text{ positive semidefinite},\; Z(u,u)=\lambda-1\text{ for }u\in V,\; Z(u,v)=-1\text{ for }\{u,v\}\in E\big\}.
--   $$
--
--   So the variable is a real symmetric matrix $Z$ whose diagonal entries are all equal to the number $\lambda-1$ and whose entries across every edge of $G$ equal $-1$; the value of the program is the smallest such $\lambda$. Equivalently, one minimizes the common diagonal value plus one.
--
--   This parameter appears twice in the paper. First, it is the graph invariant that replaces Krivine's two-projection construction: the vector construction of Lemma 4.1 needs a pair of vector families whose inner products are $0$ across edges and $1/2$ on the diagonal, and such families are built from an optimal solution of the program above, which is why the resulting bound depends on $\vartheta(G)$ rather than on a constant. Second, $\vartheta(G)$ measures the size of the graph quantitatively: any proper $k$-colouring of $G$ yields a feasible solution with $\lambda=k$ (via the regular simplex on $k$ vertices), so $\vartheta(G)$ is a lower bound for the chromatic number, and $\vartheta(G)\ge2$ whenever $G$ has an edge, with $\vartheta(K_n)=n$.
--
--   **Formalization Note** $\vartheta(G)$ is the `sInf` of the feasible set of real numbers $\lambda$; `Matrix.PosSemidef` is the positive semidefiniteness predicate for real matrices. Feasibility of the set (needed for the `sInf` not to be a degenerate value) is supplied by the $|V|$-colouring of $G$, i.e. by the matrix $|V|\cdot I-J$.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, equation (4.1), p. 92 (and the remarks following it, p. 92). https://doi.org/10.4086/toc.2014.v010a004

import Mathlib

/-!
# The theta number of the complement of a graph

Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite
programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77--105.

Equation (4.1), p. 92: the theta number of the complement of `G` is the optimal value
of the semidefinite program

  `ϑ(G) = min { λ : Z ⪰ 0, Z(u,u) = λ - 1 for all u ∈ V, Z(u,v) = -1 for {u,v} ∈ E }`.
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The feasible set of the semidefinite program (4.1) defining the theta number of
the complement of `G`: the pairs `(lam, Z)` with `Z ⪰ 0`, diagonal `lam - 1` and off-diagonal
entry `-1` across every edge of `G`. -/
def ThetaFeasible (G : SimpleGraph V) (lam : ℝ) : Prop :=
  ∃ Z : Matrix V V ℝ, Z.PosSemidef ∧ (∀ u, Z u u = lam - 1) ∧
    (∀ u v, G.Adj u v → Z u v = -1)

/-- `ϑ(G)`, the Lovász theta number of the complement of `G`, defined as the optimal
value of the semidefinite program (4.1) of the paper (p. 92). -/
def thetaComplement (G : SimpleGraph V) : ℝ :=
  sInf {lam : ℝ | ThetaFeasible G lam}

end Grothendieck


