-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_tupleHigh
-- name    : RankRobustAssort_Supplement_tupleHigh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:31:15.552502+00:00
-- url     : https://prove2.me/theorems/2b7390d5-5d25-4df0-8ad8-77daa9252699
-- title:
--   The tuple $(\bar i^j_1,\dots,\bar i^j_n)=(n,\dots,n,j,\dots,j)$
-- statement:
--   For the reverse revenue-ordered past assortments ($M=n$) and a product $j\in\{1,\dots,n-1\}$, the tuple
--
--   $$
--   (\bar i^j_1,\dots,\bar i^j_n)=(\underbrace{n,\dots,n}_{j},\underbrace{j,\dots,j}_{n-j})
--   $$
--
--   has entry $n$ in the past assortments $S_1,\dots,S_j$ and entry $j$ in $S_{j+1},\dots,S_n$. It describes customers whose first choice is $j$ and second choice is $n$.
--
--   **Formalization Note.** A tuple is a function from the past-assortment indices $\{0,\dots,n-1\}$ to the products; the function is defined for every $j$ but used only for $1\le j\le n-1$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Appendix E.1, p.ec26

import Mathlib

namespace RankRobustAssort.Supplement

/-- The tuple `(īʲ₁,…,īʲ_n) ≜ (n,…,n,j,…,j)` of Appendix E.1: the first `j` entries are `n`
and the last `n − j` entries are `j` (defined in the paper for `j ∈ {1,…,n−1}`).

Sturt, arXiv:2112.05010v4, Appendix E.1, p.ec26.

Formalization Note: a tuple is a function `Fin n → Fin (n+1)`; Lean entry `k` is the paper's
entry `k + 1`, so "entry `m ≤ j`" is `k < j`; the product `n` is `Fin.last n`. The function is
defined for every `j`, but it is only used for `j ∈ {1,…,n−1}`. -/
def tupleHigh (n : ℕ) (j : Fin (n + 1)) : Fin n → Fin (n + 1) :=
  fun k => if k.val < j.val then Fin.last n else j

end RankRobustAssort.Supplement


