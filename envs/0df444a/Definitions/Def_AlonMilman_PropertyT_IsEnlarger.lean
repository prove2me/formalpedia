-- Prove2me | Definitions.Def_AlonMilman_PropertyT_IsEnlarger
-- name    : AlonMilman_PropertyT_IsEnlarger
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:30:29.559778+00:00
-- url     : https://prove2.me/theorems/29a1bbfa-8ae1-4132-85c7-6da082ce958b
-- title:
--   Definition 4.1 — (n, k, ε)-enlarger
-- statement:
--   Let $G$ be a finite multigraph on a vertex set $V$, given by a symmetric multiplicity matrix $M = (M_{u,w})$ of nonnegative integers, and let $n, k$ be natural numbers and $\varepsilon$ a real number. Then $G$ is an **$(n, k, \varepsilon)$-enlarger** if
--
--   1. $G$ has $n$ vertices, $|V| = n$;
--   2. $G$ is $k$-regular: $\sum_{w\in V} M_{u,w} = k$ for every vertex $u$;
--   3. $\lambda_1(G) \ge \varepsilon$, where $\lambda_1(G)$ is the second-smallest eigenvalue (with multiplicity) of the matrix $Q = \operatorname{diag}(d(v)) - M$.
--
--   Alon and Milman introduce enlargers as the spectral counterpart of expanders: by their Theorem 4.3 the extended double cover of an $(n,k,\varepsilon)$-enlarger is an expander, so a family of enlargers with fixed $k$ and $\varepsilon$ and growing $n$ ("linear enlargers") yields linear expanders and superconcentrators.
--
--   **Formalization Note** "Graph" is read as a finite multigraph (parallel edges and loops allowed), because the Cayley graphs of Section 4 are multigraphs; the multiplicity matrix is required to be symmetric, which is what makes the multigraph undirected.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 83, Definition 4.1

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_AlonMilman_PropertyT_laplacian

namespace AlonMilman.PropertyT

/-- Definition 4.1 (Alon–Milman 1985, p. 83): an `(n, k, ε)`-enlarger is a `k`-regular graph
`G` on `n` vertices with `λ₁(G) ≥ ε`.  The (multi)graph is given by a symmetric multiplicity
matrix `M : Matrix V V ℕ`; `k`-regular means every row of `M` sums to `k`, and `λ₁(G)` is
`lambda1` of the matrix `Q = laplacian M`. -/
def IsEnlarger {V : Type} [Fintype V] [DecidableEq V] (n k : ℕ) (ε : ℝ) (M : Matrix V V ℕ) :
    Prop :=
  Fintype.card V = n ∧ M.IsSymm ∧ (∀ u, ∑ w, M u w = k) ∧ ε ≤ lambda1 (laplacian M)

end AlonMilman.PropertyT


