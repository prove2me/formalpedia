-- Prove2me | Definitions.Def_SubsamplingSM_Offline_sgQueries
-- name    : SubsamplingSM_Offline_sgQueries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:53:05.682953+00:00
-- url     : https://prove2.me/theorems/bf4d5085-2a83-4019-a2cc-637ef8a6af6e
-- title:
--   Number of oracle calls of SampleGreedy on a given sample
-- statement:
--   For a fixed sample $T$, $Q(T)$ is the number of oracle calls that SampleGreedy makes in its while loop: the counter after $n+1$ iterations of the counting step, started from $S=\emptyset$ with count $0$. This covers at most $n$ successful tests and the final failing one.
--
--   Theorem 1 bounds the expectation $\mathbb E_q[Q]$.
--
--   **Formalization Note** The count is produced by running the loop, not by a closed formula.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Theorem 1, p. 7, and proof of Theorem 1, §4.1.1, p. 15

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_sgQueryStep

namespace SubsamplingSM.Offline

/-- **Number of oracle calls made by SampleGreedy on a given sample.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Theorem 1, p. 7: "SampleGreedy uses in expectation `O(nk/p)` calls to the evaluation
and independence oracles", with the accounting of p. 15.

`sgQueries f I T` is the counter after `n + 1` iterations of `sgQueryStep` from
`(S, count, done) = (∅, 0, false)`, where `n = |α|` and the sample is `N′ = T`: at most
`n` successful tests and the final failing one.

**Formalization Note.** The count is produced by the run itself (paper.md Reading 4), not by a
closed formula. -/
noncomputable def sgQueries {α : Type*} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T : Finset α) : ℕ :=
  ((sgQueryStep f I T)^[Fintype.card α + 1] ⟨∅, 0, false⟩).count

end SubsamplingSM.Offline


