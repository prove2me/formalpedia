-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_bestCase
-- name    : RankRobustAssort_Supplement_bestCase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:33:24.44089+00:00
-- url     : https://prove2.me/theorems/454e83f7-8f61-420c-bdbe-15f1bc6e8e9e
-- title:
--   Best-case expected revenue $\max_{\lambda\in\mathcal U}\mathscr R^\lambda(S)$
-- statement:
--   For an assortment $S$, the **best-case expected revenue** is
--
--   $$
--   \max_{\lambda\in\mathcal U}\mathscr R^\lambda(S),
--   $$
--
--   the largest expected revenue of $S$ over all ranking-based choice models $\lambda$ consistent with the historical sales data. It is the inner problem of the optimistic optimization problem (OO), which bounds what a firm can gain from experimenting with new assortments.
--
--   **Formalization Note.** The maximum is taken as the supremum of the set of values $\mathscr R^\lambda(S)$, $\lambda\in\mathcal U$. When $\mathcal U\neq\emptyset$ (the paper's standing assumption, taken as a hypothesis by every theorem that uses this definition) that set is nonempty, bounded and its supremum is attained; on $\mathcal U=\emptyset$ the value would be $0$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §6.1, (OO), p.23

import Mathlib
import Definitions.Def_RankRobustAssort_consistentSet
import Definitions.Def_RankRobustAssort_revenue

namespace RankRobustAssort.Supplement

/-- The best-case expected revenue of an assortment `S`, `max_{λ∈𝒰} ℛ^λ(S)`, the inner problem
of the optimistic optimization problem `(OO)  max_{S∈𝒮} max_{λ∈𝒰} ℛ^λ(S)`.

Sturt, arXiv:2112.05010v4, §6.1, (OO), p.23; `𝒰` and its nonemptiness, p.8.

Formalization Note: the maximum is `sSup` of the image of `𝒰` under `λ ↦ ℛ^λ(S)`. When `𝒰` is
nonempty (the paper's standing assumption, taken as a hypothesis by every theorem using this
definition) the image is nonempty and bounded above by `r_n` (`λ` is a probability distribution
and each `𝒟^λ_i(S) ≤ 1`), and the supremum is attained because `𝒰` is a compact polytope and
`ℛ^λ(S)` is linear in `λ`; so `sSup` is the paper's `max`. On `𝒰 = ∅` the value would be
`sSup ∅ = 0`, which is never used. -/
noncomputable def bestCase {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) : ℝ :=
  sSup ((fun lam => revenue P.r lam S) '' consistentSet P)

end RankRobustAssort.Supplement


