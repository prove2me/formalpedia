-- Prove2me | Definitions.Def_SteinerCutDominants_IsLaminar
-- name    : SteinerCutDominants_IsLaminar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:23.176606+00:00
-- url     : https://prove2.me/theorems/12025aac-fc5a-4d75-b60a-5b84a65b1b64
-- title:
--   Laminar family
-- statement:
--   A family $\mathcal L$ of pairwise distinct subsets of $V$ is **laminar** if no two sets in $\mathcal L$ intersect. Equivalently, each pair of sets is either disjoint or comparable with respect to inclusion.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §3, p.6

import Mathlib
import Definitions.Def_SteinerCutDominants_Intersect

namespace SteinerCutDominants

/-- A family of subsets is laminar if no two of its sets intersect (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §3, p.6). -/
def IsLaminar {V : Type} [DecidableEq V] (L : Finset (Finset V)) : Prop :=
  ∀ A ∈ L, ∀ B ∈ L, ¬ Intersect A B

end SteinerCutDominants


