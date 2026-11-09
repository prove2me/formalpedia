-- Prove2me | Definitions.Def_HypClass1_bipStructProb
-- name    : HypClass1_bipStructProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:26:25.695996+00:00
-- url     : https://prove2.me/theorems/ee7f7db6-42bb-4cd4-88a9-d9d09e222543
-- title:
--   Random $(\eta,q,n)$-bipartite structure $\Xi_{\eta,q}$
-- statement:
--   Let $\eta, q \in [0,1]$ and let $V$ be a vertex set of size $n \in 3\mathbb Z^+$. A **random $(\eta, q, n)$-bipartite structure** $\Xi_{\eta,q} = (X, Y, Z, M, E)$ is chosen as follows:
--   1. (C1) $V = X \cup Y \cup Z$ is an equipartition chosen uniformly at random;
--   2. (C2) $M$ is a perfect matching from $X$ to $Y$ chosen uniformly at random;
--   3. (C3) for a weight function $\varphi$ on $M \times Z$ with $\varphi(x,y,z) = (1\pm\eta)q$, the 3-graph $E \subseteq M \times Z$ is the random inhomogeneous 3-graph $(M\times Z)_\varphi$, $\mathbb P(\{x,y,z\} \in E) = \varphi(x,y,z)$.
--
--   This item is the probability that $\Xi_{\eta,q}$ has a given property. It is the model of random bipartification used to reduce perfect matchings in 3-graphs to perfect matchings in bipartite graphs.
--
--   **Formalization Note** The frame $(X,Y,Z,M)$ is uniform over all frames; since every equipartition has the same number $(n/3)!$ of perfect matchings this is (C1) followed by (C2). The weight function may depend on the outcome of (C1)–(C2); its admissibility $\varphi = (1\pm\eta)q$, $0 \le \varphi \le 1$, is a hypothesis of the statements that use the law.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Definition 5.1, p.12

import Mathlib
import Definitions.Def_HypClass1_IsBipFrame
import Definitions.Def_HypClass1_randSubProb

namespace HypClass1

open Classical in
/-- **Law of a random (η, q, n)-bipartite structure**, Definition 5.1. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), p.12:
"Given η, q ∈ [0, 1] and a vertex set V of size n ∈ 3Z+, we define a random (η, q, n)-bipartite
structure Ξ_{η,q} = (X, Y, Z, M, E) as a quintuplet on the vertex set V chosen in the following order:
(C1) V = X ∪ Y ∪ Z is an equipartition chosen uniformly at random;
(C2) M ⊆ X × Y is a perfect matching from X to Y chosen uniformly at random;
(C3) For a weight function φ : M × Z → [0, 1] satisfying φ(x, y, z) = (1 ± η)q for {x, y, z} ∈ M × Z,
the 3-graph E ⊆ M × Z is the random inhomogeneous 3-graph (M × Z)_φ given by
P({x, y, z} ∈ E) = φ(x, y, z)."

`bipStructProb φ ev` is the probability that the random structure `(s, E)`, `s = (X, Y, Z, M)`,
satisfies `ev s E`: `s` is uniform over the frames (`IsBipFrame`), and given `s`, `E` is the random
inhomogeneous subset of `M × Z` with weights `φ s`.

**Formalization Note.** Every equipartition `(X, Y, Z)` admits the same number `(n/3)!` of perfect
matchings from `X` to `Y`, so the uniform law on frames is (C1) followed by (C2). The weight function
may depend on the outcome of (C1)–(C2) (`φ : BipFrame V → Finset V → ℝ`); the admissibility condition
`φ = (1 ± η)q` on `M × Z` is a hypothesis of the statements using it. -/
noncomputable def bipStructProb {V : Type*} [Fintype V] [DecidableEq V]
    (φ : BipFrame V → Finset V → ℝ) (ev : BipFrame V → Finset (Finset V) → Prop) : ℝ :=
  (∑ s ∈ (Finset.univ : Finset (BipFrame V)).filter IsBipFrame,
      randSubProb (structTriples s.2.2.2 s.2.2.1) (φ s) (ev s)) /
    ((Finset.univ : Finset (BipFrame V)).filter IsBipFrame).card

end HypClass1


