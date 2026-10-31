-- Prove2me | Definitions.Def_SteinerCutDominants_lminOf
-- name    : SteinerCutDominants_lminOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:43.117781+00:00
-- url     : https://prove2.me/theorems/16714c3e-6b31-49ed-b503-2b2f13059ad2
-- title:
--   The minimal members $\mathcal L_{\min}$
-- statement:
--   $\mathcal L_{\min}$ is the subfamily of the inclusionwise minimal members of $\mathcal L$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §3, p.6

import Mathlib

namespace SteinerCutDominants

/-- `𝓛_min`, the subfamily of the inclusionwise minimal members of `𝓛` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §3, p.6). -/
def lminOf {V : Type} [DecidableEq V] (L : Finset (Finset V)) : Finset (Finset V) :=
  L.filter fun A => ∀ B ∈ L, B ⊆ A → B = A

end SteinerCutDominants


