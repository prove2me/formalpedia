-- Prove2me | Definitions.Def_CorrColoring_ThreeChoosable_IsChoosable
-- name    : CorrColoring_ThreeChoosable_IsChoosable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:58:29.676256+00:00
-- url     : https://prove2.me/theorems/4b0c6888-cd04-4e0b-be32-3041902f0e67
-- title:
--   $k$-choosability of a graph
-- statement:
--   Let $G$ be a graph and $k$ a natural number. A **list assignment** for $G$ is a function $L$ that assigns to each vertex $v$ a list (finite set) $L(v)$ of colours; an **$L$-coloring** of $G$ is a proper colouring $\varphi$ with $\varphi(v) \in L(v)$ for every vertex $v$. The graph $G$ is **$k$-choosable** if
--
--   $$\text{for every list assignment } L \text{ with } |L(v)| = k \text{ for all } v \in V(G), \text{ there is an } L\text{-coloring of } G,$$
--
--   that is, a map $\varphi$ with $\varphi(v) \in L(v)$ for all $v$ and $\varphi(u) \neq \varphi(v)$ for every edge $uv$.
--
--   Choosability is the list-colouring analogue of the chromatic number; the colours in different lists are arbitrary, so $k$-choosability is stronger than $k$-colourability.
--
--   **Formalization Note** The colours range over an arbitrary type $\alpha$ (in the universe `Type`), quantified inside the definition, and lists are `Finset α` of cardinality exactly $k$, as in the paper ("lists of size $k$"). Lists are not restricted to a fixed $k$-element palette; that restriction would give $k$-colourability.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 2, §1, definition of list assignment, L-coloring and k-choosable

import Mathlib

namespace CorrColoring.ThreeChoosable

/-- `k`-choosability (Dvořák–Postle, p. 2): for every colour type `α` and every assignment `L`
of lists of size exactly `k` to the vertices, there is a proper colouring `φ` with
`φ v ∈ L v` for every vertex `v` (an `L`-colouring). -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (α : Type) (L : V → Finset α), (∀ v, (L v).card = k) →
    ∃ φ : V → α, (∀ v, φ v ∈ L v) ∧ ∀ u v, G.Adj u v → φ u ≠ φ v

end CorrColoring.ThreeChoosable


