-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_numMistakes
-- name    : YoungConventions_RiskDominance_numMistakes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:50.322821+00:00
-- url     : https://prove2.me/theorems/02df6298-63b1-4535-869e-63fb02b148a5
-- title:
--   Number of mistakes (resistance) of a transition
-- statement:
--   Let $h'$ be a successor of $h$ and let $s$ be the right-most element of $h'$. A **mistake** in the transition $h\to h'$ is a component $s_i$ of $s$ that is not an optimal response by player $i$ to any sample of size $k$ from $h$. The **resistance** $r(h,h')$ is the number of mistakes in $h\to h'$:
--   $$r(h,h')=\#\{i : s_i\text{ is not a best reply of } i\text{ to any sample of size } k\text{ from } h\}.$$
--   For $h'$ not a successor of $h$ the paper sets $r(h,h')=\infty$.
--
--   **Formalization Note** The count is only applied to successor pairs: the paths of the next definition move by successor steps, which is how the value $\infty$ for non-successors is encoded.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 68, displayed definitions (Mistake, Resistance)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_newest
import Definitions.Def_YoungConventions_RiskDominance_IsSampleBestReply

open Classical

namespace YoungConventions.RiskDominance

/-- **Number of mistakes in a transition.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 68 (PDF p. 13), displayed definitions:
"Let `h′` be a successor of `h` and let `s` be the right-most element of `h′`. A mistake in the
transition `h → h′` is a component `sᵢ` of `s` that is not an optimal response by agent `i` to any
sample of size `k` from `h`." "For any two states `h, h′` the resistance `r(h, h′)` is the total
number of mistakes involved in the transition `h → h′` if `h′` is a successor of `h`; otherwise
`r(h, h′) = ∞`."

`numMistakes u k h h'` is the number of players `i` whose component of the right-most play of `h′`
is not a best reply of `i` to any sample of size `k` from `h`.

**Formalization Note.** This is the resistance `r(h, h′)` on successor pairs; it is only ever used
for successor pairs (the paths of `PathResistance` move by successor steps), which is how the value
`r(h, h′) = ∞` for non-successors is encoded. -/
noncomputable def numMistakes {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m]
    (u : ι → ((i : ι) → S i) → ℝ) (k : ℕ) (h h' : YoungConventions.AdaptivePlay.History S m) : ℕ :=
  (Finset.univ.filter (fun i => ¬ IsSampleBestReply u k h i (newest h' i))).card

end YoungConventions.RiskDominance


