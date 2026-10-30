-- Prove2me | Definitions.Def_SubsamplingSM_Offline_testCost
-- name    : SubsamplingSM_Offline_testCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:28.246218+00:00
-- url     : https://prove2.me/theorems/fd70e7a8-3436-437c-b693-2c915fba5a24
-- title:
--   Oracle calls of one while-test of SampleGreedy
-- statement:
--   One test of the while condition of SampleGreedy iterates over the sample $N'=T$, testing $S\cup\{u\}\in\mathcal I$ and $f(u\mid S)>0$ for each $u\in T$. Its cost in oracle calls is
--   $$c(T)=\begin{cases}0,& T=\emptyset,\\ 2|T|+1,& T\neq\emptyset,\end{cases}$$
--   namely $|T|$ independence queries, the $|T|$ values $f(S\cup\{u\})$, and the value $f(S)$ once.
--
--   **Formalization Note** The paper fixes no formal cost model; this is the accounting of the proof of Theorem 1 (p. 15). It also scans elements already in $S$, so it over-counts any leaner implementation.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, proof of Theorem 1, §4.1.1, p. 15

import Mathlib

namespace SubsamplingSM.Offline

/-- **Oracle cost of one evaluation of the while condition of SampleGreedy.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, proof of Theorem 1, §4.1.1, p. 15 (unnumbered): "iterating over each `u ∈ N′` and
testing `S + u ∈ I` and `f(u | S) > 0` requires `O(nq)` calls to the evaluation and
independence oracle."

`testCost T` is the number of oracle calls of one test of the while condition of Algorithm 1,
Line 6, when the sample is `N′ = T`: `0` if `T = ∅`, and otherwise `|T|` independence calls
(`S + u ∈ I`) and `|T| + 1` value calls (`f(S + u)` for each `u ∈ T`, and `f(S)` once),
`2|T| + 1` in all.

**Formalization Note.** The paper fixes no formal cost model; this is the accounting of p. 15
(paper.md Reading 4). It also scans elements already in `S`, so it over-counts, and an upper
bound in this model bounds any leaner implementation. -/
def testCost {α : Type*} [DecidableEq α] (T : Finset α) : ℕ :=
  if T = ∅ then 0 else 2 * T.card + 1

end SubsamplingSM.Offline


