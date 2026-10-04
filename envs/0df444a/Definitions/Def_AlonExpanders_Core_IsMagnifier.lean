-- Prove2me | Definitions.Def_AlonExpanders_Core_IsMagnifier
-- name    : AlonExpanders_Core_IsMagnifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:45:55.988713+00:00
-- url     : https://prove2.me/theorems/a9e6b68f-4000-4f9e-80fa-2d2f38015223
-- title:
--   $(n, d, c)$-magnifier
-- statement:
--   Let $G = (V, E)$ be a finite simple graph, $n, d$ natural numbers and $c$ a real number, and write $N(X)$ for the set of neighbours of a set $X \subseteq V$. $G$ is an **$(n, d, c)$-magnifier** if
--
--   1. $|V| = n$;
--   2. every vertex has degree at most $d$;
--   3. every set $X \subseteq V$ with $|X| \le n/2$ satisfies
--   $$
--   |N(X) - X| \;\ge\; c\,|X|.
--   $$
--
--   Magnifiers are the non-bipartite counterpart of expanders: Lemma 2.4 and Corollary 2.3 show that magnifying constants and the spectral gap $\lambda(G)$ bound each other.
--
--   **Formalization Note** $N(X)$ is the published `AKSSorting.Core.neighbours`, and $|N(X) - X|$ is `Set.ncard` of the set difference. The condition $|X| \le n/2$ is written $2|X| \le n$ in natural numbers, which avoids truncating division. "Maximal degree $d$" is read as `G.maxDegree ≤ d`.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 85, Section 2, definition of (n, d, c)-magnifier

import Mathlib
import Definitions.Def_AKSSorting_Core_IsExpander

namespace AlonExpanders.Core

/-- `(n, d, c)`-magnifier (Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), §2, p. 85):
a graph `G` on `n` vertices with maximal degree (at most) `d` such that every set `X` of vertices
with `|X| ≤ n/2` satisfies `|N(X) − X| ≥ c · |X|`, where `N(X) = AKSSorting.Core.neighbours G X`.
The condition `|X| ≤ n/2` is written `2 * |X| ≤ n` (no natural-number division). -/
def IsMagnifier {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n d : ℕ) (c : ℝ) : Prop :=
  Fintype.card V = n ∧ G.maxDegree ≤ d ∧
    ∀ X : Finset V, 2 * X.card ≤ n →
      c * (X.card : ℝ) ≤ ((AKSSorting.Core.neighbours G X \ (X : Set V)).ncard : ℝ)

end AlonExpanders.Core


