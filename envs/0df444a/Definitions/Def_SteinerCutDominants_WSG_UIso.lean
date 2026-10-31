-- Prove2me | Definitions.Def_SteinerCutDominants_WSG_UIso
-- name    : SteinerCutDominants_WSG_UIso
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:16.333114+00:00
-- url     : https://prove2.me/theorems/bb6d20ab-84c4-4cff-9282-1f08dc918464
-- title:
--   Isomorphism of Steiner graphs
-- statement:
--   An **isomorphism** of the Steiner graphs $(G,T)$ underlying two weighted Steiner graphs: a graph isomorphism carrying terminals onto terminals. The weights are ignored.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §6, p.11, Theorem 4 ("up to isomorphisms")

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG

namespace SteinerCutDominants

/-- An isomorphism of the underlying Steiner graphs `(G, T)`, ignoring the weights. -/
def WSG.UIso (H H' : WSG) : Prop :=
  ∃ f : H.V ≃ H'.V, (∀ x y, H.G.Adj x y ↔ H'.G.Adj (f x) (f y)) ∧ H'.T = H.T.map f.toEmbedding

end SteinerCutDominants


