-- Prove2me | Definitions.Def_RobersonCx_IsTopMinor
-- name    : RobersonCx_IsTopMinor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:33.892835+00:00
-- url     : https://prove2.me/theorems/293052da-ad9a-4c13-8245-9344832c9d3a
-- title:
--   Topological minor (subdivision model)
-- statement:
--   A **subdivision** of a graph $H$ is obtained by replacing each edge $hh'$ by an $hh'$-path of positive length, whose internal vertices are new and distinct for different edges. $H$ is a **topological minor** of $G$ if a subgraph of $G$ is isomorphic to a subdivision of $H$.
--
--   Equivalently, there is an injective map $\iota:V(H)\to V(G)$ and, for each edge $hh'$ of $H$, a path of $G$ from $\iota(h)$ to $\iota(h')$, such that the only branch vertices on the path of $hh'$ are $\iota(h)$ and $\iota(h')$, and a vertex shared by the paths of two different edges is a branch vertex. Then the paths have disjoint interiors avoiding all other branch vertices, and their union is the required subdivision.
--
--   Topological minors connect immersions to minors in the paper: for cubic graphs in subcubic hosts an immersion is a topological minor (Lemma 4), and every topological minor is a minor.
--
--   **Formalization Note** Stated as the subdivision model above, with paths indexed by ordered adjacent pairs as in the immersion definition; positive length is automatic because $\iota$ is injective.
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §2.2, p.6 (PDF p.8)

import Mathlib

set_option autoImplicit false

namespace RobersonCx

/-- `IsTopMinor H G`: `H` is a topological minor of `G` (§2.2, p.6 (PDF p.8)): a subgraph of `G` is isomorphic
to a subdivision of `H`, where a subdivision replaces each edge `hh′` by an `hh′`-path of positive length whose
internal vertices are new and distinct for different edges.

**Formalization Note** Stated as a subdivision model: an injective `ι : V(H) → V(G)` and, for each edge `hh′`,
a path `P` of `G` from `ι h` to `ι h′`, such that (a) a branch vertex `ι c` lies on the path of `ab` only if
`c = a` or `c = b`, and (b) a vertex shared by the paths of two different edges is a branch vertex. By (a) and
(b) the paths have pairwise disjoint interiors that avoid all branch vertices, so their union is a subgraph of
`G` isomorphic to a subdivision of `H`; conversely such a subgraph gives a model. Paths are indexed by ordered
adjacent pairs, and (b) is only required between different edges, as in `IsImmersion`. Positive length is
automatic since `ι` is injective and adjacent vertices are distinct. -/
def IsTopMinor {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ (ι : W → V) (P : ∀ a b : W, H.Adj a b → G.Walk (ι a) (ι b)),
    Function.Injective ι ∧
    (∀ (a b : W) (h : H.Adj a b), (P a b h).IsPath) ∧
    (∀ (a b : W) (h : H.Adj a b), ∀ v ∈ (P a b h).support, ∀ c : W, v = ι c → c = a ∨ c = b) ∧
    (∀ (a b : W) (h : H.Adj a b) (a' b' : W) (h' : H.Adj a' b'), s(a, b) ≠ s(a', b') →
      ∀ v ∈ (P a b h).support, v ∈ (P a' b' h').support → ∃ c : W, v = ι c)

end RobersonCx


