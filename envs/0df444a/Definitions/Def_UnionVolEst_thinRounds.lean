-- Prove2me | Definitions.Def_UnionVolEst_thinRounds
-- name    : UnionVolEst_thinRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:47.239622+00:00
-- url     : https://prove2.me/theorems/ca6cdad7-2365-4eb5-adf7-74038f915c40
-- title:
--   Halving rounds of the while loop (Algorithm 1, lines 11–12)
-- statement:
--   Starting from stored points $L$ and a pending Poisson count $N$, one round of lines 11–12 keeps each stored point independently with probability $1/2$ and replaces $N$ by $\mathrm{Binomial}(N,1/2)$. Here round $r$ keeps the stored point in position $j$ iff the coin $c_{r,j}$ shows true, and keeps pending item $j$ iff $c_{r,|L_r|+j}$ shows true; $\mathrm{thinRounds}(c,L,N,r)$ is the pair (surviving points, surviving count) after $r$ rounds.
--
--   **Formalization Note** Positions are re-indexed in each round, so every item meets a fresh coin in every round; with independent fair coins this realizes lines 11–12 exactly. The pending items are counts: the new points are drawn after the loop.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, Algorithm 1 lines 11–12, p.15 (PDF p.17)

import Mathlib

namespace UnionVolEst

/-- The halving rounds of the while loop of Algorithm 1, lines 11–12 (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, printed p.15,
PDF p.17): starting from the stored points `L` and the pending Poisson count `N`, round `r`
keeps the stored item in position `j` iff the coin `c r j` is `true` ("throw `y` from `X` with
probability 1/2"), and keeps the pending item `j` iff `c r (|L_r| + j)` is `true`
(`N ← Binomial(N, 1/2)`). `thinRounds c L N r` is the pair (survivors, pending count) after `r`
rounds.

**Formalization Note** Positions are recomputed in every round (the survivors are re-indexed from
`0`, and the pending items follow the stored ones), so each item meets a fresh coin in every
round; with independent fair coins this realizes lines 11–12 exactly. The pending items are
counts, not points: the new points are drawn only after the loop (lines 13–15). -/
def thinRounds {α : Type*} (c : ℕ → ℕ → Bool) (L : List α) (N : ℕ) : ℕ → List α × ℕ
  | 0 => (L, N)
  | r + 1 =>
    let st := thinRounds c L N r
    ((st.1.zipIdx.filter (fun p => c r p.2)).map Prod.fst,
     ((List.range st.2).filter (fun j => c r (st.1.length + j))).length)

end UnionVolEst


