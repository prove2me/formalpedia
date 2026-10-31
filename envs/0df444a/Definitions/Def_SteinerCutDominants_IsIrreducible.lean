-- Prove2me | Definitions.Def_SteinerCutDominants_IsIrreducible
-- name    : SteinerCutDominants_IsIrreducible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:53.545323+00:00
-- url     : https://prove2.me/theorems/1e0ac48d-a1f2-4403-a3e4-153f4cf9456c
-- title:
--   Irreducible facet inducing Steiner graph
-- statement:
--   A facet inducing Steiner graph $(G,T)$ is **irreducible** if $G$ has no cut node and no node in $V(G)\setminus T$ has degree two.
--
--   The irreducible graphs are those that cannot be undone by the inverse operations of subdivision and gluing, and so are the generators of all facet inducing Steiner graphs.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §6, p.10

import Mathlib
import Definitions.Def_SteinerCutDominants_IsFacetInducing
import Definitions.Def_SteinerCutDominants_IsCutNode

namespace SteinerCutDominants

/-- A facet inducing Steiner graph `(G, T)` is irreducible if `G` has no cut node and no node in
`V(G) \ T` has degree two (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, §6,
p.10). -/
def IsIrreducible (H : WSG) : Prop :=
  IsFacetInducing H ∧ (∀ w, ¬ IsCutNode H.G w) ∧ ∀ v, v ∉ H.T → H.G.degree v ≠ 2

end SteinerCutDominants


