-- Prove2me | Definitions.Def_RankRobustAssort_consistentSet
-- name    : RankRobustAssort_consistentSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:04.888701+00:00
-- url     : https://prove2.me/theorems/2bd1b01a-741f-4fd0-b7bb-03821517c6df
-- title:
--   Consistent set $\mathcal U$ of ranking-based choice models
-- statement:
--   A ranking-based choice model is **consistent with the historical sales data** when its predicted purchase frequencies on the past assortments are within distance $\eta$ of the observed ones:
--
--   $$
--   \mathcal U=\Big\{\lambda\in\Delta_\Sigma:\ \exists\,\epsilon \text{ with } \|\epsilon\|\le\eta \text{ and } \mathcal D^\lambda_i(S_m)-v_{m,i}=\epsilon_{m,i}\ \text{ for all } i\in S_m,\ m\in\mathcal M\Big\}.
--   $$
--
--   $\mathcal U$ is the uncertainty set of the robust problem (RO). The paper assumes throughout that $\mathcal U\neq\emptyset$; here that assumption is not built in, and every theorem that needs it states it as a hypothesis.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §2, p.8

import Mathlib
import Definitions.Def_RankRobustAssort_Problem
import Definitions.Def_RankRobustAssort_errNorm
import Definitions.Def_RankRobustAssort_IsDist
import Definitions.Def_RankRobustAssort_choiceProb

namespace RankRobustAssort

/-- The set `𝒰` of ranking-based choice models consistent with the historical sales data:
`𝒰 ≜ {λ ∈ Δ_Σ : there exists a vector ϵ such that ‖ϵ‖ ≤ η and
𝒟^λ_i(S_m) − v_{m,i} = ϵ_{m,i} for all i ∈ S_m and m ∈ ℳ}`.

Sturt, arXiv:2112.05010v4, §2, p.8.

Formalization Note: `ϵ` is a function `Fin M → Fin (n+1) → ℝ`; only its coordinates `(m,i)` with
`i ∈ S_m` enter the constraints and the norm `errNorm` (see there), so the existential is over the
paper's vectors. The paper's standing assumption that `𝒰` is nonempty (p.8) is *not* built in;
results that need it take `(consistentSet P).Nonempty` as a hypothesis. -/
def consistentSet {n M : ℕ} (P : Problem n M) : Set (Equiv.Perm (Fin (n + 1)) → ℝ) :=
  {lam | IsDist lam ∧ ∃ ε : Fin M → Fin (n + 1) → ℝ, errNorm P.norm P.S ε ≤ P.η ∧
      ∀ m, ∀ i ∈ P.S m, choiceProb lam (P.S m) i - P.v m i = ε m i}

end RankRobustAssort


