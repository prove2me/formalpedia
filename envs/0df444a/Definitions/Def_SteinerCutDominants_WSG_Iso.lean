-- Prove2me | Definitions.Def_SteinerCutDominants_WSG_Iso
-- name    : SteinerCutDominants_WSG_Iso
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:16.551934+00:00
-- url     : https://prove2.me/theorems/f967234f-3920-44b2-afee-5bd6de53fd0d
-- title:
--   Isomorphism of weighted Steiner graphs
-- statement:
--   An **isomorphism** of weighted Steiner graphs is a graph isomorphism that carries the terminals of the first graph onto those of the second and preserves edge weights.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §6, p.10–11 ("up to isomorphisms")

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_wt

namespace SteinerCutDominants

/-- An isomorphism of weighted Steiner graphs: a graph isomorphism carrying the terminals onto the
terminals and the weights onto the weights. -/
def WSG.Iso (H H' : WSG) : Prop :=
  ∃ f : H.V ≃ H'.V, (∀ x y, H.G.Adj x y ↔ H'.G.Adj (f x) (f y)) ∧
    H'.T = H.T.map f.toEmbedding ∧ ∀ x y, H'.wt (f x) (f y) = H.wt x y

end SteinerCutDominants


