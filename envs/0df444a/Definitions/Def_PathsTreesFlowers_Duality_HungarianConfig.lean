-- Prove2me | Definitions.Def_PathsTreesFlowers_Duality_HungarianConfig
-- name    : PathsTreesFlowers_Duality_HungarianConfig
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:36:52.438981+00:00
-- url     : https://prove2.me/theorems/9481006a-ade7-489f-b489-ac1381a2ab33
-- title:
--   §5.8, p. 463 — the outcome of the algorithm on a maximum matching: G′ with a maximally matched Hungarian tree J, and the sets S_J
-- statement:
--   Let $M$ be a matching of $G$. A **Hungarian configuration** for $(G, M)$ is the outcome described in 5.8 of applying the algorithm to $(G, M)$ from an exposed vertex $r$ (the root): "a graph $G'$ containing a maximally matched Hungarian tree $J$, a number of whose outer vertices are pseudo". It consists of
--
--   1. a partition $\mathcal P$ of the vertices of $G$ each of whose parts is a blossom set for $M$; then $G' = G/\mathcal P$ and $M' = M/\mathcal P$;
--   2. an alternating tree $J$ in $G'$ which is a planted tree for $(G', M')$ whose root is the vertex of $G'$ containing $r$ (so $M' \cap J$ is a maximum matching of $J$), and which is a Hungarian tree in $G'$;
--   3. the requirement that every pseudovertex of $G'$ (a part with more than one vertex) is an outer vertex of $J$, as is the case for every pseudovertex created by the algorithm (4.13).
--
--   Two derived objects:
--   - $X$, the vertices of $G$ not absorbed into a vertex of $J$. They are the vertices of $G' - J$, and an edge of $G$ is an edge of $G' - J$ exactly when both its end-points lie in $X$.
--   - $\mathcal S_J$, the odd sets consisting of one inner vertex of $J$, together with the odd sets consisting of the vertices in the complete expansion of one pseudovertex of $J$.
--
--   These are the objects of the induction step in Edmonds' proof of the matching-duality theorem.
--
--   **Formalization Note** The inner vertices of $J$ are parts of size one, because every pseudovertex is outer; so a member of $\mathcal S_J$ of the first type is the singleton of a vertex of $G$.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 463, 5.8 (with 4.11, 4.13, 4.16)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

namespace PathsTreesFlowers.Duality

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- 5.8, p. 463 (with 4.11, 4.13 and 4.16): the outcome of applying the algorithm to `(G, M)` from
an exposed vertex `root`: "a graph `G′` containing a maximally matched Hungarian tree `J`, a number
of whose outer vertices are pseudo".

* `P` is a partition of the vertices of `G` each of whose parts is a blossom set for `M` (a single
  vertex, or the complete expansion of a pseudovertex obtained by successively shrinking
  blossoms); `G′ = G/P` is `shrink G P` and `M′ = M/P` is `shrinkMatching G P M`.
* `J` is an alternating tree of `G′` that is planted for `M′` with root the vertex of `G′`
  containing `root` (so `M′ ∩ J` is a maximum matching of `J`: `J` is *maximally matched*), and
  `J` is a Hungarian tree in `G′`.
* Every pseudovertex of `G′` (a part with more than one vertex) is an outer vertex of `J`. -/
structure HungarianConfig (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) where
  /-- the partition of the vertices of `G` into the vertices of `G′` -/
  P : Finpartition (Finset.univ : Finset V)
  /-- every vertex of `G′` is a blossom set for `M` -/
  blossom_sets : ∀ U ∈ P.parts, IsBlossomSet G M U
  /-- the tree `J` in `G′` -/
  J : AltTree (shrink G P)
  /-- the exposed vertex of `G` used as root -/
  root : V
  /-- `J` is a planted tree for `(G′, M′)` whose root is the vertex of `G′` containing `root` -/
  planted : IsPlantedTree (shrink G P) (shrinkMatching G P M) J (toPart P root)
  /-- `J` is a Hungarian tree in `G′` -/
  hungarian : IsHungarianTree (shrink G P) J
  /-- every pseudovertex of `G′` is an outer vertex of `J` -/
  pseudo_outer : ∀ (U : Finset V) (hU : U ∈ P.parts), 2 ≤ U.card →
    (⟨U, hU⟩ : {U : Finset V // U ∈ P.parts}) ∈ J.outer

namespace HungarianConfig

variable {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}

/-- The vertices of `G′ − J`, as vertices of `G`: the vertices of `G` not absorbed into a vertex
of `J`. (Every pseudovertex of `G′` lies in `J`, so these vertices are vertices of `G′`, and an
edge of `G` is an edge of `G′ − J` exactly when both its end-points lie in this set.) -/
def X (C : HungarianConfig G M) : Finset V :=
  Finset.univ.filter (fun v => toPart C.P v ∉ C.J.verts)

/-- 5.8, p. 463: `S_J`, the odd sets consisting of one inner vertex of `J`, and the odd sets
consisting of the vertices in the complete expansion of one pseudovertex of `J`. (Inner vertices of
`J` are parts of size one, since every pseudovertex is outer.) -/
def SJ (C : HungarianConfig G M) : Finset (Finset V) :=
  (C.J.inner ∪ C.J.outer.filter (fun U => 2 ≤ U.1.card)).image Subtype.val

end HungarianConfig

end PathsTreesFlowers.Duality


