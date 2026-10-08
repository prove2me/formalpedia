-- Prove2me | Definitions.Def_PathsTreesFlowers_Invariance_Config
-- name    : PathsTreesFlowers_Invariance_Config
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:17.292216+00:00
-- url     : https://prove2.me/theorems/2007dd04-33df-4a92-a667-74af3b4a8dcb
-- title:
--   6.0–6.2, pp. 463–464 — the output G*, {J_i} of construction 6.0 for a maximum matching, and the vertex families O(G), I(G)
-- statement:
--   Let $G$ be a finite graph and $M$ a maximum matching of $G$. Section 6 of Edmonds (1965) runs the matching algorithm on $(G, M)$ without augmenting (6.0): planted trees are grown from the exposed vertices one after another, blossoms are shrunk as they arise, and earlier trees are not removed. The result is a graph $G^*$ obtained from $G$ by shrinking blossoms, and a sequence $J_1, \dots, J_n$ of disjoint planted trees in $G^*$, one for each exposed vertex of $(G, M)$.
--
--   A **6.0 configuration** for $(G, M)$ records this output together with every invariant the construction establishes:
--
--   1. $M$ is a maximum matching of $G$;
--   2. a partition $\mathcal P$ of the vertices of $G$ each of whose parts is a blossom set for $M$; then $G^* = G/\mathcal P$ and $M^* = M/\mathcal P$;
--   3. alternating trees $J_1, \dots, J_n$ in $G^*$, each a planted tree for $M^*$ (with some root), pairwise vertex-disjoint;
--   4. *density* (4.20): every vertex of $G^*$ exposed for $M^*$ is a vertex of some $J_i$;
--   5. *ordered Hungarian* (6.1): $J_i$ is Hungarian in $G^* - J_1 - \dots - J_{i-1}$, i.e. every edge of $G^*$ at an outer vertex of $J_i$ ends at an inner vertex of $J_i$ or at a vertex of some $J_h$ with $h < i$;
--   6. every pseudovertex of $G^*$ (a part with more than one vertex) is an outer vertex of some $J_i$.
--
--   From a configuration, 6.2 defines two vertex families of $G$:
--
--   - the **outer vertices** $O(G)$: the non-pseudo outer vertices of the $J_i$ (vertices $v$ whose part $\{v\}$ is an outer vertex of some $J_i$) together with the vertices of the pseudovertex complete expansions (vertices whose part has more than one vertex);
--   - the **inner vertices** $I(G)$: the vertices $v$ whose part is an inner vertex of some $J_i$.
--
--   Theorem 6.2 shows that $O(G)$, $I(G)$ and $G^*$ do not depend on the configuration: they are determined by $G$ alone.
--
--   **Formalization Note** Each planted tree contains exactly one vertex exposed for $M^*$ (its root), and a part is exposed for $M^*$ exactly when it contains a vertex exposed for $M$; so density together with disjointness is the paper's "one corresponding to each exposed vertex of $(G, M)$". "By expanding all the pseudovertices of $G^*$ completely, we recover the graph $G$" holds by construction, since $G^*$ is the contraction of $G$ along $\mathcal P$. The trees are indexed by `Fin n` (from $0$). $O(G)$ and $I(G)$ are sets of vertices of $G$, defined literally as on the page. That configurations exist for every maximum matching is a separate theorem item (`exists_config_6_0`).
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), pp. 463–464, 6.0, 6.1 (first sentence), 6.2 (definitions of O(G), I(G)); p. 460, 4.20 (dense planted forest)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink

namespace PathsTreesFlowers.Invariance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The output of construction 6.0 (Edmonds 1965, pp. 463–464) applied to `(G, M)` with `M` a
maximum matching: the graph `G* = shrink G P` obtained by shrinking nested blossoms for `M`, with
`M* = M/P`, and a sequence `J₁, …, Jₙ` of disjoint planted trees in `G*`. The fields record every
invariant the construction establishes:

* `M` is a maximum matching of `G`;
* every part of `P` is a blossom set for `M` (the complete expansion of a pseudovertex, or a single
  vertex);
* each `Jᵢ` is a planted tree for `M*` in `G*`, and the trees are pairwise vertex-disjoint;
* every vertex of `G*` exposed for `M*` lies in some `Jᵢ` (the forest is *dense*, 4.20): there is
  one tree for each exposed vertex;
* `Jᵢ` is Hungarian in `G* − J₁ − ⋯ − J_{i−1}` (6.1): every edge of `G*` at an outer vertex of
  `Jᵢ` ends at an inner vertex of `Jᵢ` or at a vertex of an earlier tree;
* every pseudovertex of `G*` (a part with more than one vertex) is an outer vertex of some `Jᵢ`. -/
structure Config60 (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) where
  /-- `M` is a maximum matching of `G` -/
  hM : PathsTreesFlowers.Duality.IsMaxMatching G M
  /-- the partition of the vertices of `G` into the complete expansions of the vertices of `G*` -/
  P : Finpartition (Finset.univ : Finset V)
  /-- every part is a blossom set for `M` -/
  blossom : ∀ U ∈ P.parts, PathsTreesFlowers.Duality.IsBlossomSet G M U
  /-- the number of trees -/
  n : ℕ
  /-- the trees `J₁, …, Jₙ` (indexed from `0`) in `G*` -/
  J : Fin n → AltTree (shrink G P)
  /-- each `Jᵢ` is a planted tree for `M*` in `G*` -/
  planted : ∀ i, ∃ r, IsPlantedTree (shrink G P) (shrinkMatching G P M) (J i) r
  /-- the trees are pairwise disjoint -/
  disjoint : ∀ i j, i ≠ j → Disjoint (J i).verts (J j).verts
  /-- dense: every vertex of `G*` exposed for `M*` is a vertex of some tree -/
  dense : ∀ x, PathsTreesFlowers.Duality.IsExposed (shrink G P) (shrinkMatching G P M) x → ∃ i, x ∈ (J i).verts
  /-- `Jᵢ` is Hungarian in `G* − J₁ − ⋯ − J_{i−1}` -/
  ordered_hungarian : ∀ i, ∀ u ∈ (J i).outer, ∀ (e : ShrinkE G P) (w : {U // U ∈ P.parts}),
    (shrink G P).ends e = s(u, w) → w ∈ (J i).inner ∨ ∃ h < i, w ∈ (J h).verts
  /-- every pseudovertex of `G*` is an outer vertex of some tree -/
  pseudo_outer : ∀ (U : Finset V) (hU : U ∈ P.parts), 1 < U.card → ∃ i, ⟨U, hU⟩ ∈ (J i).outer

variable {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}

/-- The *outer vertices* `O(G)` of `G` (6.2 (a), p. 464): the non-pseudo outer vertices of the
`Jᵢ` (vertices `v` whose part `{v}` is an outer vertex of some tree) together with the vertices of
the pseudovertex complete expansions (vertices whose part has more than one vertex). -/
def outerSet (C : Config60 G M) : Set V :=
  {v | ((C.P.part v).card = 1 ∧ ∃ i, partOf C.P v ∈ (C.J i).outer) ∨ 1 < (C.P.part v).card}

/-- The *inner vertices* `I(G)` of `G` (6.2 (b), p. 464): the vertices whose part is an inner
vertex of some `Jᵢ`. -/
def innerSet (C : Config60 G M) : Set V :=
  {v | ∃ i, partOf C.P v ∈ (C.J i).inner}

end PathsTreesFlowers.Invariance


