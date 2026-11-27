-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_IsOptimalOO
-- name    : RankRobustAssort_Supplement_IsOptimalOO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:34:01.203369+00:00
-- url     : https://prove2.me/theorems/60ee0dae-ab50-56b5-b7c1-5382f69396a4
-- title:
--   Optimality for the optimistic problem (OO)
-- statement:
--   An assortment $S$ is **optimal for the optimistic optimization problem**
--
--   $$
--   \text{(OO)}\qquad \max_{S\in\mathcal S}\ \max_{\lambda\in\mathcal U}\mathscr R^\lambda(S)
--   $$
--
--   if $S\in\mathcal S$ (that is, $0\in S$) and $\max_{\lambda\in\mathcal U}\mathscr R^\lambda(S')\le\max_{\lambda\in\mathcal U}\mathscr R^\lambda(S)$ for every assortment $S'\in\mathcal S=\{S'\subseteq\mathcal N_0:0\in S'\}$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §6.1, (OO), p.23; 𝒮, p.7

import Mathlib
import Definitions.Def_RankRobustAssort_Supplement_bestCase

namespace RankRobustAssort.Supplement

/-- `S` is optimal for the optimistic optimization problem
`(OO)  max_{S∈𝒮} max_{λ∈𝒰} ℛ^λ(S)`: `S ∈ 𝒮` (i.e. `0 ∈ S`) and its best-case revenue is at least
that of every assortment `S' ∈ 𝒮 = {S' ⊆ 𝒩₀ : 0 ∈ S'}`.

Sturt, arXiv:2112.05010v4, §6.1, (OO), p.23; `𝒮`, p.7.

Formalization Note: optimality is against *all* assortments containing the no-purchase option,
exactly as the published `IsOptimalRO` for `(RO)`. -/
def IsOptimalOO {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) : Prop :=
  0 ∈ S ∧ ∀ S' : Finset (Fin (n + 1)), 0 ∈ S' → bestCase P S' ≤ bestCase P S

end RankRobustAssort.Supplement


