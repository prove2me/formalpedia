-- Prove2me | Definitions.Def_RankRobustAssort_worstCase
-- name    : RankRobustAssort_worstCase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:58.068471+00:00
-- url     : https://prove2.me/theorems/e9f23f8f-1677-4a1f-bf23-417e482c6a26
-- title:
--   Worst-case expected revenue $\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)$
-- statement:
--   The worst-case expected revenue of an assortment $S$ is
--
--   $$
--   \min_{\lambda\in\mathcal U}\mathcal R^\lambda(S),
--   $$
--
--   the inner problem of the robust optimization problem (RO) $\max_{S\in\mathcal S}\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)$.
--
--   **Formalization Note.** The minimum is the infimum of $\{\mathcal R^\lambda(S):\lambda\in\mathcal U\}$. When $\mathcal U\ne\emptyset$ (the paper's standing assumption, a hypothesis of every theorem using this quantity) the set is nonempty and bounded below by $0$, and the infimum is attained since $\mathcal U$ is a compact polytope and $\lambda\mapsto\mathcal R^\lambda(S)$ is linear, so it is the paper's minimum. For $\mathcal U=\emptyset$ the infimum would be the default value $0$, which is never used.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, (RO), p.2 and §2, p.8

import Mathlib
import Definitions.Def_RankRobustAssort_consistentSet
import Definitions.Def_RankRobustAssort_revenue

namespace RankRobustAssort

/-- The worst-case expected revenue of an assortment `S`, `min_{λ∈𝒰} ℛ^λ(S)`, the inner problem
of `(RO)`: `max_{S∈𝒮} min_{λ∈𝒰} ℛ^λ(S)`.

Sturt, arXiv:2112.05010v4, (RO), p.2; `𝒰` and its nonemptiness, p.8.

Formalization Note: the minimum is `sInf` of the image of `𝒰` under `λ ↦ ℛ^λ(S)`. When `𝒰` is
nonempty (the paper's standing assumption, which every theorem using this definition takes as a
hypothesis) the image is nonempty and bounded below by `0` (revenues are nonnegative and `λ ≥ 0`),
and the infimum is attained because `𝒰` is a compact polytope and `ℛ^λ(S)` is linear in `λ`; so
`sInf` is the paper's `min`. On `𝒰 = ∅` the value would be `sInf ∅ = 0`, which is never used. -/
noncomputable def worstCase {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) : ℝ :=
  sInf ((fun lam => revenue P.r lam S) '' consistentSet P)

end RankRobustAssort


