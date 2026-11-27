-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_SHatOO
-- name    : RankRobustAssort_Supplement_SHatOO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:35:28.255808+00:00
-- url     : https://prove2.me/theorems/163d9028-483d-4e43-a246-20a1e21c9128
-- title:
--   The collection $\widehat{\mathcal S}^{OO}$
-- statement:
--   With $\mathcal M_i=\{m\in\mathcal M:i\in S_m\}$ the past assortments that offered product $i$, let
--
--   $$
--   \widehat{\mathcal S}^{OO}=\bigl\{S\in\mathcal S:\ \text{if } i^*\in S,\ 0<r_i<r_{i^*},\text{ and }\mathcal M_{i^*}\subseteq\mathcal M_i,\ \text{then } i\notin S\bigr\}.
--   $$
--
--   An assortment belongs to $\widehat{\mathcal S}^{OO}$ when it contains the no-purchase option and no product other than $0$ is dominated by a product of the assortment with higher revenue that was offered only in past assortments where the first one was offered too. It is the optimistic counterpart of $\widehat{\mathcal S}$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Appendix J.1.1, p.ec55

import Mathlib
import Definitions.Def_RankRobustAssort_Mset

namespace RankRobustAssort.Supplement

/-- The collection of assortments
`Ŝ^OO ≜ {S ∈ 𝒮 : if i* ∈ S, 0 < r_i < r_{i*}, and ℳ_{i*} ⊆ ℳ_i, then i ∉ S}`:
no product of `S` other than the no-purchase option is dominated (lower revenue, offered in every
past assortment that offered `i*`) by a product `i*` of `S`.

Sturt, arXiv:2112.05010v4, Appendix J.1.1, p.ec55.

Formalization Note: `S ∈ 𝒮` is `0 ∈ S`; `i*` and `i` range over all products `𝒩₀ = Fin (n+1)`;
`ℳ_i` is the published `Mset`. The condition `0 < r_i` (i.e. `i ≠ 0`, since `r₀ = 0 < r₁`) is kept,
so `0` is never excluded. -/
def SHatOO {n M : ℕ} (P : Problem n M) : Set (Finset (Fin (n + 1))) :=
  {S | 0 ∈ S ∧ ∀ i' ∈ S, ∀ i, 0 < P.r i → P.r i < P.r i' → Mset P i' ⊆ Mset P i → i ∉ S}

end RankRobustAssort.Supplement


