-- Prove2me | Definitions.Def_SubsamplingSM_Offline_greedyStep
-- name    : SubsamplingSM_Offline_greedyStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:49:48.369219+00:00
-- url     : https://prove2.me/theorems/254326c8-5e41-44ac-b14d-7e1dccff0cf4
-- title:
--   One iteration of SampleGreedy's while loop
-- statement:
--   Given the sample $T=N'$ and a current solution $S$, one iteration of the while loop of SampleGreedy adds the greedy choice among the candidates:
--   $$\operatorname{step}_T(S)=\begin{cases}S\cup\{\operatorname{pick}(S,C(T,S))\}, & C(T,S)\neq\emptyset,\\ S, & C(T,S)=\emptyset.\end{cases}$$
--
--   The second case is the termination of the loop; further iterations then leave $S$ unchanged.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 1, Lines 6–8, p. 9

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_cands
import Definitions.Def_SubsamplingSM_Offline_pick

namespace SubsamplingSM.Offline

/-- **One iteration of the while loop of SampleGreedy.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 1, Lines 6–8, p. 9: "while there exists `u ∈ N′` such that `S + u ∈ I` and
`f(u | S) > 0` do / Let `u ∈ N′` be the element of this kind maximizing `f(u | S)`. / Add
`u` to `S`."

`greedyStep f I T S` adds to `S` the element chosen by `pick` (maximum marginal gain, ties to
the earliest element) among the candidates `cands f I T S` of the sampled pool `T = N′`, and
returns `S` unchanged when there is no candidate (the loop has terminated). -/
noncomputable def greedyStep {α : Type*} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T S : Finset α) : Finset α :=
  if h : (cands f I T S).Nonempty then insert (pick f S (cands f I T S) h) S else S

end SubsamplingSM.Offline


