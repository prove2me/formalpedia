-- Prove2me | Definitions.Def_AlonExpanders_Core_IsStrongExpander
-- name    : AlonExpanders_Core_IsStrongExpander
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:08:47.306247+00:00
-- url     : https://prove2.me/theorems/e65bab47-376e-4b1a-a5ce-36fe50fe1348
-- title:
--   Strong $(n, d, c)$-expander
-- statement:
--   For a set $X$ of vertices of a graph $G = (V, E)$ let $N(X) = \{v \in V : vx \in E \text{ for some } x \in X\}$ be its set of neighbours. Let $G = (I, O; E)$ be a bipartite graph on inputs $I$ and outputs $O$, let $n, d$ be natural numbers and $c$ a real number. $G$ is a **strong $(n, d, c)$-expander** if
--
--   1. $|I| = |O| = n$;
--   2. every vertex of $G$ has degree at most $d$;
--   3. for every set of inputs $X \subseteq I$,
--   $$
--   |N(X)| \;\ge\; \Bigl(1 + c\Bigl(1 - \frac{|X|}{n}\Bigr)\Bigr)\,|X|. \tag{1.1}
--   $$
--
--   A plain $(n, d, c)$-expander asks (1.1) only for $|X| \le n/2$; "strong" asks it for all $X \subseteq I$. The expansion $c$ is the quantity that Theorem 3.4 ties to the second-smallest Laplacian eigenvalue $\lambda(G)$.
--
--   **Formalization Note** $N(X)$ is the published `AKSSorting.Core.neighbours`, applied to the image of $X$ under `Sum.inl`, and $|N(X)|$ is `Set.ncard`. "The maximal degree of a vertex is $d$" is read as `G.maxDegree ≤ d`; every result of the mission is monotone in $d$ or fixes $d$ by regularity. The quotient $|X|/n$ is real; for $n = 0$ the only set is $X = \emptyset$.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 83, Section 1, definition of (n, d, c)-expander and strong (n, d, c)-expander, Eq. (1.1)

import Mathlib
import Definitions.Def_AKSSorting_Core_IsExpander
import Definitions.Def_AlonExpanders_Core_IsIOBipartite

namespace AlonExpanders.Core

/-- Strong `(n, d, c)`-expander (Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), §1,
p. 83): a bipartite graph on inputs `I` and outputs `O` with `|I| = |O| = n`, maximal degree (at
most) `d`, such that for **every** `X ⊆ I`
`|N(X)| ≥ (1 + c (1 - |X|/n)) · |X|`   (1.1),
where `N(X) = AKSSorting.Core.neighbours G X` is the set of vertices adjacent to some vertex of
`X`, and `X` is viewed inside `I ⊕ O` through `Sum.inl`. -/
def IsStrongExpander {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (c : ℝ) : Prop :=
  Fintype.card I = n ∧ Fintype.card O = n ∧ IsIOBipartite G ∧ G.maxDegree ≤ d ∧
    ∀ X : Finset I,
      (1 + c * (1 - (X.card : ℝ) / n)) * (X.card : ℝ) ≤
        ((AKSSorting.Core.neighbours G (X.map Function.Embedding.inl)).ncard : ℝ)

end AlonExpanders.Core


