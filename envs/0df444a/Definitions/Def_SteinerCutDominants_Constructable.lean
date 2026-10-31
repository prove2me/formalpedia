-- Prove2me | Definitions.Def_SteinerCutDominants_Constructable
-- name    : SteinerCutDominants_Constructable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:00.606728+00:00
-- url     : https://prove2.me/theorems/2d115fe1-9259-4896-b1aa-2af89191e12f
-- title:
--   Constructable from a family
-- statement:
--   A weighted Steiner graph $(G,T)$ is **constructable** from a family $\mathcal F$ of weighted Steiner graphs if there is a sequence $(G_0,T_0),\dots,(G_r,T_r)=(G,T)$ with $(G_0,T_0)\in\mathcal F$ such that, for each $i\in[r]$, $(G_i,T_i)$ can be obtained as a subdivision of $(G_{i-1},T_{i-1})$ or from gluing $(G_{i-1},T_{i-1})$ with some member of $\mathcal F$.
--
--   **Formalization Note** An inductive predicate. The sequence is linear, as on the page: the second argument of a gluing is a member of $\mathcal F$. Members are taken up to isomorphism.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §6, p.10

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_Iso
import Definitions.Def_SteinerCutDominants_IsSubdivision
import Definitions.Def_SteinerCutDominants_IsGluing

namespace SteinerCutDominants

/-- A weighted Steiner graph is constructable from the family `F` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §6, p.10): there is a sequence
`(G₀, T₀), …, (G_r, T_r) = (G, T)` with `(G₀, T₀) ∈ F` such that each `(Gᵢ, Tᵢ)` is a subdivision of
`(Gᵢ₋₁, Tᵢ₋₁)` or arises from gluing `(Gᵢ₋₁, Tᵢ₋₁)` with some member of `F`.

**Formalization Note** The sequence is linear, as on the page: the second argument of a gluing is a
member of `F` up to isomorphism, never another constructed graph. -/
inductive Constructable (F : Set WSG) : WSG → Prop
  | base {H₀ H : WSG} : H₀ ∈ F → WSG.Iso H₀ H → Constructable F H
  | subdiv {H' H : WSG} : Constructable F H' → IsSubdivision H' H → Constructable F H
  | glue {H₁ H₂ H₀ H : WSG} : Constructable F H₁ → H₀ ∈ F → WSG.Iso H₀ H₂ →
      IsGluing H₁ H₂ H → Constructable F H

end SteinerCutDominants


