-- Prove2me | Definitions.Def_SteinerCutDominants_cutPolytope
-- name    : SteinerCutDominants_cutPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:17.695443+00:00
-- url     : https://prove2.me/theorems/54463cb7-de9b-4484-b65c-fbaccce67b5c
-- title:
--   The $T$-Steiner cut polytope $\mathrm{CUT}(G,T)$
-- statement:
--   The **$T$-Steiner cut polytope** is
--   $$
--   \mathrm{CUT}(G,T)=\operatorname{conv}\{\chi(\delta(S)) : \delta(S)\text{ is a }T\text{-Steiner cut}\}\subseteq\mathbb R^{E(G)} .
--   $$
--   Its dominant is the object of the mission.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §1, p.1

import Mathlib
import Definitions.Def_SteinerCutDominants_cutVec
import Definitions.Def_SteinerCutDominants_IsSteinerCut

namespace SteinerCutDominants

/-- The `T`-Steiner cut polytope `CUT(G, T)`: the convex hull of the incidence vectors of the
`T`-Steiner cuts (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, §1, p.1). -/
noncomputable def cutPolytope {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset V) :
    Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ S : Finset V, IsSteinerCut T S ∧ x = cutVec G S}

end SteinerCutDominants


