-- Prove2me | Definitions.Def_SubsamplingSM_Offline_sgQueryStep
-- name    : SubsamplingSM_Offline_sgQueryStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:52:18.495459+00:00
-- url     : https://prove2.me/theorems/6a86098b-f3c5-4db8-92ab-265f57fac7ef
-- title:
--   One iteration of SampleGreedy, counting oracle calls
-- statement:
--   On a state that has not terminated, one iteration tests the while condition on the sample $T$, which costs $c(T)$ oracle calls. If some candidate exists, the greedy choice $\operatorname{pick}(S,C(T,S))$ is added to $S$; otherwise the state is marked as terminated. A terminated state is left unchanged, so the final, failing test is counted exactly once.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 1, Lines 6–8, p. 9, and p. 15

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_cands
import Definitions.Def_SubsamplingSM_Offline_pick
import Definitions.Def_SubsamplingSM_Offline_testCost
import Definitions.Def_SubsamplingSM_Offline_SGCountState

namespace SubsamplingSM.Offline

/-- **One iteration of SampleGreedy's while loop, counting oracle calls.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 1, Lines 6–8, p. 9, with the accounting of p. 15: each test of the while
condition iterates over `u ∈ N′` testing `S + u ∈ I` and `f(u | S) > 0`.

On a state that is not done, the while condition is tested on the sample `T = N′`, which costs
`testCost T` calls; if it succeeds, the element chosen by `pick` (the same rule as
`greedyStep`) is added to `S`; if it fails, the state becomes done. A done state is left
unchanged, so the final, failing test is counted exactly once. -/
noncomputable def sgQueryStep {α : Type*} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T : Finset α) (st : SGCountState α) : SGCountState α :=
  if st.done then st
  else if h : (cands f I T st.S).Nonempty then
    { S := insert (pick f st.S (cands f I T st.S) h) st.S, count := st.count + testCost T,
      done := false }
  else
    { S := st.S, count := st.count + testCost T, done := true }

end SubsamplingSM.Offline


