-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_tupleLow
-- name    : RankRobustAssort_Supplement_tupleLow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:31:01.278808+00:00
-- url     : https://prove2.me/theorems/113867c3-03d9-5e74-93fa-0c0718944d9c
-- title:
--   The tuple $(\underline i^j_1,\dots,\underline i^j_n)=(0,\dots,0,j,\dots,j)$
-- statement:
--   For the reverse revenue-ordered past assortments ($M=n$) and a product $j\in\{1,\dots,n-1\}$, the tuple
--
--   $$
--   (\underline i^j_1,\dots,\underline i^j_n)=(\underbrace{0,\dots,0}_{j},\underbrace{j,\dots,j}_{n-j})
--   $$
--
--   has entry $0$ in the past assortments $S_1,\dots,S_j$ and entry $j$ in $S_{j+1},\dots,S_n$. It describes customers who buy $j$ when it is offered and otherwise buy nothing.
--
--   **Formalization Note.** A tuple is a function from the past-assortment indices $\{0,\dots,n-1\}$ to the products; the function is defined for every $j$ but used only for $1\le j\le n-1$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Appendix E.1, p.ec26

import Mathlib

namespace RankRobustAssort.Supplement

/-- The tuple `(i̲ʲ₁,…,i̲ʲ_n) ≜ (0,…,0,j,…,j)` of Appendix E.1: the first `j` entries are `0`
and the last `n − j` entries are `j` (defined in the paper for `j ∈ {1,…,n−1}`).

Sturt, arXiv:2112.05010v4, Appendix E.1, p.ec26.

Formalization Note: a tuple is a function `Fin n → Fin (n+1)`; Lean entry `k` is the paper's
entry `k + 1`, so "entry `m ≤ j`" is `k < j`. The function is defined for every `j`, but it is
only used for `j ∈ {1,…,n−1}`. -/
def tupleLow (n : ℕ) (j : Fin (n + 1)) : Fin n → Fin (n + 1) :=
  fun k => if k.val < j.val then 0 else j

end RankRobustAssort.Supplement


