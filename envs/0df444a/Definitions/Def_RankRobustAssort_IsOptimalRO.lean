-- Prove2me | Definitions.Def_RankRobustAssort_IsOptimalRO
-- name    : RankRobustAssort_IsOptimalRO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:09.958429+00:00
-- url     : https://prove2.me/theorems/c6c4e6ad-4f53-4037-96a2-c2f699bb99ca
-- title:
--   Optimal assortment for (RO)
-- statement:
--   Let $\mathcal S=\{S\subseteq\mathcal N_0: 0\in S\}$ be the assortments that include the no-purchase option. An assortment $S$ is **optimal for the robust optimization problem**
--
--   $$
--   \max_{S\in\mathcal S}\ \min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)\tag{RO}
--   $$
--
--   when $S\in\mathcal S$ and $\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S')\le\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)$ for every $S'\in\mathcal S$.
--
--   Optimality is against all assortments containing the no-purchase option.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, (RO), p.2 and §2, p.7

import Mathlib
import Definitions.Def_RankRobustAssort_worstCase

namespace RankRobustAssort

/-- `S` is optimal for the robust optimization problem
`(RO)  max_{S∈𝒮} min_{λ∈𝒰} ℛ^λ(S)`: `S ∈ 𝒮` (i.e. `0 ∈ S`) and its worst-case revenue is at least
that of every assortment `S' ∈ 𝒮 = {S' ⊆ 𝒩₀ : 0 ∈ S'}`.

Sturt, arXiv:2112.05010v4, (RO), p.2; `𝒮`, p.7.

Formalization Note: optimality is against *all* assortments containing the no-purchase option,
not only against those in `Ŝ`. -/
def IsOptimalRO {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) : Prop :=
  0 ∈ S ∧ ∀ S' : Finset (Fin (n + 1)), 0 ∈ S' → worstCase P S' ≤ worstCase P S

end RankRobustAssort


