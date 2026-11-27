-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_revPast
-- name    : RankRobustAssort_Supplement_revPast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:30:49.325895+00:00
-- url     : https://prove2.me/theorems/5f88f96e-169e-50e5-9467-b7e3064f8cc9
-- title:
--   Reverse revenue-ordered past assortments $\widetilde{\mathcal S}$
-- statement:
--   Let $\mathcal N_0=\{0,1,\dots,n\}$ be the products, $0$ the no-purchase option and $n$ the product with the highest revenue. The past assortments are **reverse revenue-ordered** when there are $M=n$ of them and
--
--   $$
--   S_1=\{0,n\},\qquad S_m=\{0,1,\dots,m-1,n\}\quad(m=2,\dots,n),\qquad \mathcal M=\widetilde{\mathcal S}=\{S_1,\dots,S_n\}.
--   $$
--
--   They are nested, $S_1\subset\cdots\subset S_n=\mathcal N_0$. This is the family for which the paper shows that the characterization $\widehat{\mathcal S}$ of Theorem 1 is exact (Theorem 2) and has $2^{M-2}$ members.
--
--   **Formalization Note.** Past assortment $m$ has Lean index $m-1$, and uniformly $S_m=\{j: j\le m-1\}\cup\{n\}$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Definition 1, p.14

import Mathlib

namespace RankRobustAssort.Supplement

/-- The **reverse revenue-ordered** past assortments `S̃ = {S₁,…,S_n}`:
`S₁ ≜ {0,n}` and `S_m ≜ {0,1,…,m−1,n}` for `m ∈ {2,…,n}` (so `M = n`).

Sturt, arXiv:2112.05010v4, Definition 1, p.14.

Formalization Note: past assortments are indexed by `Fin n` with Lean index `k = m − 1`, and
`revPast n k = {j : j ≤ k} ∪ {n}` uniformly (for `k = 0` this is `{0,n}`, for `k = n − 1` it is
all of `𝒩₀ = Fin (n+1)`). Products are `Fin (n+1)`, `0` the no-purchase option, `Fin.last n` the
product `n`. -/
def revPast (n : ℕ) : Fin n → Finset (Fin (n + 1)) :=
  fun k => Finset.univ.filter (fun j => j.val ≤ k.val ∨ j = Fin.last n)

end RankRobustAssort.Supplement


