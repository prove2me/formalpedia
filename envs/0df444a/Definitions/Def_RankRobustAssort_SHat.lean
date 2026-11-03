-- Prove2me | Definitions.Def_RankRobustAssort_SHat
-- name    : RankRobustAssort_SHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:53.280011+00:00
-- url     : https://prove2.me/theorems/594ea734-4dec-4bac-9539-9dab2d39eedb
-- title:
--   Assortments revenue-ordered relative to the past assortments, $\widehat{\mathcal S}$
-- statement:
--   The collection
--
--   $$
--   \widehat{\mathcal S}=\big\{S\in\mathcal S:\ \text{if } i^*\in S,\ r_{i^*}<r_i, \text{ and } \mathcal M_{i^*}\subseteq\mathcal M_i, \text{ then } i\in S\big\}
--   $$
--
--   consists of the assortments containing the no-purchase option that, whenever they offer a product $i^*$, also offer every more expensive product $i$ that was offered in all past assortments offering $i^*$. It is the paper's notion of being revenue-ordered *relative to* the past assortments; the main theorem says an optimal robust assortment can be found in it.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §4, p.12

import Mathlib
import Definitions.Def_RankRobustAssort_Mset

namespace RankRobustAssort

/-- The collection `Ŝ` of assortments that are revenue-ordered relative to the past assortments:
`Ŝ ≜ {S ∈ 𝒮 : if i* ∈ S, r_{i*} < r_i, and ℳ_{i*} ⊆ ℳ_i, then i ∈ S}`.

Sturt, arXiv:2112.05010v4, §4, p.12.

Formalization Note: `S ∈ 𝒮` is `0 ∈ S`; `i*` and `i` range over all products `𝒩₀ = Fin (n+1)`. -/
def SHat {n M : ℕ} (P : Problem n M) : Set (Finset (Fin (n + 1))) :=
  {S | 0 ∈ S ∧ ∀ i' ∈ S, ∀ i, P.r i' < P.r i → Mset P i' ⊆ Mset P i → i ∈ S}

end RankRobustAssort


