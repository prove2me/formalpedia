-- Prove2me | Definitions.Def_SteinerCutDominants_rootCuts
-- name    : SteinerCutDominants_rootCuts
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:58.114975+00:00
-- url     : https://prove2.me/theorems/0d552d4d-1b2c-4141-b551-107c4dfefcf1
-- title:
--   The incidence vectors of the roots
-- statement:
--   The set $\{\chi(\delta(S)) : \delta(S)\text{ is a root of }a\}\subseteq\mathbb R^{E(G)}$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_IsRootOf

namespace SteinerCutDominants

/-- The set of incidence vectors of the roots of `a` (Conforti, Kaibel, *Steiner Cut Dominants*,
arXiv:2209.14802v2, §2, p.4). -/
def rootCuts {V : Type} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (T : Finset V) (a : G.edgeSet → ℝ) : Set (G.edgeSet → ℝ) :=
  {x | ∃ S : Finset V, IsRootOf G T a S ∧ x = cutVec G S}

end SteinerCutDominants


