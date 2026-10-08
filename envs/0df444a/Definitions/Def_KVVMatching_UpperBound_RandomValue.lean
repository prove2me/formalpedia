-- Prove2me | Definitions.Def_KVVMatching_UpperBound_RandomValue
-- name    : KVVMatching_UpperBound_RandomValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:01:34.881605+00:00
-- url     : https://prove2.me/theorems/003aa47b-802a-4e3c-961b-c4aeeb31677d
-- title:
--   Expected matching size of RANDOM
-- statement:
--   RANDOM matches each arriving column to a uniformly chosen eligible row. Let $V_G(t,S)$ be its expected number of future matches when $t$ columns remain and the set $S$ of rows is already matched. For the next column $c=t-1$, let $E$ be its adjacent rows outside $S$. Then
--
--   $$V_G(0,S)=0,\qquad V_G(t,S)=\begin{cases}V_G(t-1,S),&E=\varnothing,\\ 1+|E|^{-1}\sum_{r\in E}V_G(t-1,S\cup\{r\}),&E\ne\varnothing.\end{cases}$$
--
--   The value of RANDOM on $G$ is $V_G(n,\varnothing)$. The recurrence is the conditional expectation of the uniform random choice and is used in all three milestones.
--
--   **Formalization Note** When no row is eligible, no division is performed and the column remains unmatched.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 357, paragraph preceding Lemma 13 (RANDOM)

import Mathlib
import Definitions.Def_KVVMatching_UpperBound_OnlineAlg

namespace KVVMatching.UpperBound

/-- Expected number of future matches under uniform choice from eligible rows,
with `t` columns still to arrive and matched-row set `S`. -/
noncomputable def randomValueAux {n : ℕ} (G : Graph n) :
    (t : ℕ) → Finset (Fin n) → ℝ
  | 0, _ => 0
  | t + 1, S =>
      if h : t < n then
        let E := eligibleRows G S ⟨t, h⟩
        if E.Nonempty then
          1 + (∑ r ∈ E, randomValueAux G t (insert r S)) / (E.card : ℝ)
        else randomValueAux G t S
      else 0

/-- Expected size of the matching returned by RANDOM on the graph. -/
noncomputable def randomValue {n : ℕ} (G : Graph n) : ℝ :=
  randomValueAux G n ∅

end KVVMatching.UpperBound


