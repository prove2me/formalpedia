-- Prove2me | Definitions.Def_RankRobustAssort_revenue
-- name    : RankRobustAssort_revenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:46.926143+00:00
-- url     : https://prove2.me/theorems/a6ebafb8-6e6f-41a6-ab57-9f28c2fcf62e
-- title:
--   Expected revenue $\mathcal R^\lambda(S)$
-- statement:
--   With product revenues $r=(r_0,\dots,r_n)$, the expected revenue of an assortment $S$ under the ranking-based choice model $\lambda$ is
--
--   $$
--   \mathcal R^\lambda(S)=\sum_{i\in\mathcal N_0} r_i\,\mathcal D^\lambda_i(S)=r^\top\mathcal D^\lambda(S).
--   $$
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §2, p.7

import Mathlib
import Definitions.Def_RankRobustAssort_choiceProb

namespace RankRobustAssort

/-- The expected revenue of assortment `S` under the ranking-based choice model `λ` with product
revenues `r`: `ℛ^λ(S) ≜ ∑_{i∈𝒩₀} r_i 𝒟^λ_i(S) = r^⊤ 𝒟^λ(S)`.

Sturt, arXiv:2112.05010v4, §2, p.7. -/
noncomputable def revenue {n : ℕ} (r : Fin (n + 1) → ℝ) (lam : Equiv.Perm (Fin (n + 1)) → ℝ)
    (S : Finset (Fin (n + 1))) : ℝ :=
  ∑ i, r i * choiceProb lam S i

end RankRobustAssort


