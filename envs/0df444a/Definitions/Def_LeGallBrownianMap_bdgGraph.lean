-- Prove2me | Definitions.Def_LeGallBrownianMap_bdgGraph
-- name    : LeGallBrownianMap_bdgGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:21.410708+00:00
-- url     : https://prove2.me/theorems/1e7ff756-21a6-400e-a3ff-40920e0c6902
-- title:
--   The graph of the Bouttier–Di Francesco–Guitter map of a labeled $p$-tree
-- statement:
--   Let $\theta=(\tau,\ell)\in\mathbb T^p_n$ with contour sequence $v_0,\dots,v_{pn}$ extended periodically, and add an extra vertex $\partial$. The BDG map has vertex set $\tau^\circ\cup\{\partial\}$ and, for every $i\in\{0,\dots,pn-1\}$:
--
--   1. if $\ell_{v_i}=\min\ell$, an edge between $v_i$ and $\partial$;
--   2. if $\ell_{v_i}>\min\ell$, an edge between $v_i$ and $v_j$, where $j$ is the first index among $i+1,\dots,i+pn-1$ with $\ell_{v_j}=\ell_{v_i}-1$ (the successor of $i$).
--
--   The resulting planar map is a rooted pointed $2p$-angulation with $n$ faces; this definition records its graph, whose graph distance is the distance $d_{gr}$ of the map.
--
--   **Formalization Note** Vertices are `Option` words, `none` being $\partial$. Edge multiplicities, the planar embedding and the root orientation are not recorded; they do not affect graph distances.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.2, pp.10–11

import Mathlib
import Definitions.Def_LeGallBrownianMap_labelSeq
import Definitions.Def_LeGallBrownianMap_minLabel

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.2,
pp.10–11: "We associate with the pair (θ, ε) a 2p-angulation M with n faces, whose set of
vertices is m = τ° ∪ {∂} and whose edges are obtained as follows: For every i ∈ {0, 1, ..., pn − 1},
• if ℓ_{v_i} = min{ℓ_v : v ∈ τ°}, draw an edge between the corner v_i and ∂;
• if ℓ_{v_i} > min{ℓ_v : v ∈ τ°}, draw an edge between the corner v_i and the corner v_j, where j
is the first index in the sequence i + 1, i + 2, ..., i + pn − 1 such that ℓ_{v_j} = ℓ_{v_i} − 1".

`bdgGraph θ` is the graph of the planar map built from `θ` by this rule, on the vertex type
`Option (List ℕ+)`: `some v` is the white vertex `v` and `none` is the extra vertex `∂`. Its
graph distance is the graph distance `d_gr` of the map (§2.2, p.12, "we write d_gr for the graph
distance in the vertex set m").

**Formalization Note.** Only the edge rule enters: the map's graph distance depends on which
pairs of vertices are joined, not on the planar embedding, on edge multiplicities or on the
orientation `ε` of the root. The relation is symmetrized by `SimpleGraph.fromRel` (the two
endpoints always differ: their labels differ). Here `k = #τ − 1 = pn` and indices of the contour
and label sequences are taken modulo `k` (the periodic extension). No edges touch vertices
outside `τ° ∪ {∂}`. -/
noncomputable def bdgGraph (θ : Finset (List ℕ+) × (List ℕ+ → ℤ)) :
    SimpleGraph (Option (List ℕ+)) :=
  SimpleGraph.fromRel fun x y =>
    ∃ i < θ.1.card - 1, x = some (contourSeq θ.1 i) ∧
      ((labelSeq θ i = minLabel θ ∧ y = none) ∨
        (minLabel θ < labelSeq θ i ∧
          ∃ j, i < j ∧ j < i + (θ.1.card - 1) ∧ labelSeq θ j = labelSeq θ i - 1 ∧
            (∀ j', i < j' → j' < j → labelSeq θ j' ≠ labelSeq θ i - 1) ∧
            y = some (contourSeq θ.1 j)))

end LeGallBrownianMap


