-- Prove2me | Definitions.Def_SponsoredAssort_supp
-- name    : SponsoredAssort_supp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:59.592775+00:00
-- url     : https://prove2.me/theorems/3dcd8683-170d-42bb-9d3b-ee40a6cdd4e4
-- title:
--   Support $\mathrm{supp}_i(m,v_{-i})$ of a mechanism
-- statement:
--   For a mechanism $m$, a seller $i$ and the others' attractiveness $v_{-i}$, the **support** is the set of assortments the mechanism displays as seller $i$'s report varies:
--
--   $$
--   \mathrm{supp}_i(m,v_{-i})=\{S\in 2^{[n]}:\ \exists\,v_i\ge0,\ S(v_i,v_{-i})=S\}.
--   $$
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2.3, p.14

import Mathlib
import Definitions.Def_SponsoredAssort_Mechanism

open scoped NNReal

namespace SponsoredAssort

/-- The **support** `suppᵢ(m, v₋ᵢ) = {S ∈ 𝒮 : ∃ vᵢ, S(vᵢ, v₋ᵢ) = S}` of a mechanism for seller
`i` (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), §2.3, p.14): the assortments the mechanism
displays as seller `i`'s report ranges over `ℝ₊`, the others' reports being fixed at `v₋ᵢ`.

**Formalization Note.** It depends on `v` only through `v₋ᵢ`, since the `i`-th coordinate is
overwritten. -/
def supp {n : ℕ} (m : Mechanism n) (i : Fin n) (v : Attr n) : Set (Finset (Fin n)) :=
  {S | ∃ y : ℝ≥0, m.alloc (Function.update v i y) = S}

end SponsoredAssort


