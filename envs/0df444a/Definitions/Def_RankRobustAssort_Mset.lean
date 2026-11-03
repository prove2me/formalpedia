-- Prove2me | Definitions.Def_RankRobustAssort_Mset
-- name    : RankRobustAssort_Mset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:52.520083+00:00
-- url     : https://prove2.me/theorems/d1bd78a7-065d-495d-aa42-29a06df00682
-- title:
--   Past assortments offering product $i$: $\mathcal M_i$
-- statement:
--   For a product $i\in\mathcal N_0$, the set of past assortments in which it was offered is
--
--   $$
--   \mathcal M_i=\{m\in\mathcal M: i\in S_m\}.
--   $$
--
--   Thus $\mathcal M_{i}\subseteq\mathcal M_{j}$ says that $j$ was offered in every past assortment that offered $i$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §4, p.11

import Mathlib
import Definitions.Def_RankRobustAssort_Problem

namespace RankRobustAssort

/-- The past assortments that offered product `i`: `ℳ_i ≜ {m ∈ ℳ : i ∈ S_m}`.

Sturt, arXiv:2112.05010v4, §4, p.11.

Formalization Note: past-assortment indices are `Fin M` (paper index `m` = Lean index `m - 1`). -/
def Mset {n M : ℕ} (P : Problem n M) (i : Fin (n + 1)) : Finset (Fin M) :=
  Finset.univ.filter (fun m => i ∈ P.S m)

end RankRobustAssort


