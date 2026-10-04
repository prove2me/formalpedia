-- Prove2me | Definitions.Def_AlonExpanders_Core_IsEnlarger
-- name    : AlonExpanders_Core_IsEnlarger
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:45:46.276996+00:00
-- url     : https://prove2.me/theorems/6c2960fe-f424-409b-a734-525152b4e276
-- title:
--   $(n, d, \varepsilon)$-enlarger
-- statement:
--   Let $G = (V, E)$ be a finite simple graph with adjacency matrix $A_G$ and Laplacian $Q_G = \mathrm{diag}(d(v))_{v \in V} - A_G$, and let $\lambda(G)$ be the second-smallest eigenvalue of $Q_G$, counted with multiplicity. For natural numbers $n, d$ and a real number $\varepsilon$, $G$ is an **$(n, d, \varepsilon)$-enlarger** if
--
--   1. $|V| = n$;
--   2. every vertex has degree at most $d$;
--   3. $\lambda(G) \ge \varepsilon$.
--
--   Enlargers are the spectral counterpart of magnifiers: by Corollary 2.3 every enlarger is a magnifier, and by Lemma 2.4 every magnifier is an enlarger.
--
--   **Formalization Note** $\lambda(G)$ is the published `AlonMilman.Diameter.lambda1`, which is $0$ by convention on graphs with fewer than two vertices. This is a simple-graph notion with maximal degree at most $d$; it is not `AlonMilman.PropertyT.IsEnlarger`, which concerns regular multigraphs given by a multiplicity matrix.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 85, Section 2, definitions of Q_G, λ(G) and (n, d, ε)-enlarger

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

namespace AlonExpanders.Core

/-- `(n, d, ε)`-enlarger (Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), §2, p. 85):
a graph on `n` vertices with maximal degree (at most) `d` and `λ(G) ≥ ε`, where `λ(G)` is the
second-smallest eigenvalue of `Q_G = diag(d(v)) − A_G` (`AlonMilman.Diameter.lambda1`). -/
def IsEnlarger {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n d : ℕ) (ε : ℝ) : Prop :=
  Fintype.card V = n ∧ G.maxDegree ≤ d ∧ ε ≤ AlonMilman.Diameter.lambda1 G

end AlonExpanders.Core


