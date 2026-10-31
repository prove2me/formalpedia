-- Prove2me | Definitions.Def_SteinerCutDominants_cutDominant
-- name    : SteinerCutDominants_cutDominant
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:06.900368+00:00
-- url     : https://prove2.me/theorems/d422161a-c1bb-4683-a9f0-e9d1d31d49a6
-- title:
--   The $T$-Steiner cut dominant $\mathrm{CUT}_+(G,T)$
-- statement:
--   The **$T$-Steiner cut dominant** is the Minkowski sum of $\mathrm{CUT}(G,T)$ and the nonnegative orthant,
--   $$
--   \mathrm{CUT}_+(G,T)=\mathrm{CUT}(G,T)+\mathbb R^{E(G)}_{\ge 0},
--   $$
--   i.e. the polyhedron of all points $y$ that dominate some $x\in\mathrm{CUT}(G,T)$ in the sense of $y\ge x$. Minimizing a nonnegative linear function over it is minimizing over $\mathrm{CUT}(G,T)$.
--
--   **Formalization Note** The definition uses the page's second description, with the coordinatewise order on `G.edgeSet → ℝ`.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §1, p.1

import Mathlib
import Definitions.Def_SteinerCutDominants_cutPolytope

namespace SteinerCutDominants

/-- The `T`-Steiner cut dominant `CUT₊(G, T)`: the points `y` that dominate some
`x ∈ CUT(G, T)` in the sense of `y ≥ x` (Conforti, Kaibel, *Steiner Cut Dominants*,
arXiv:2209.14802v2, §1, p.1).

**Formalization Note** This is the page's second description of the Minkowski sum
`CUT(G, T) + ℝ^{E(G)}_{≥0}`; `x ≤ y` is the coordinatewise order. -/
def cutDominant {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset V) :
    Set (G.edgeSet → ℝ) :=
  {y | ∃ x ∈ cutPolytope G T, x ≤ y}

end SteinerCutDominants


