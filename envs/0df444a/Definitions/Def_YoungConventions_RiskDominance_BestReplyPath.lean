-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_BestReplyPath
-- name    : YoungConventions_RiskDominance_BestReplyPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:35.506994+00:00
-- url     : https://prove2.me/theorems/9f7cce0f-f063-4830-808f-834992dc0ca1
-- title:
--   Directed paths of given length in the best-reply graph
-- statement:
--   For $n\ge0$, there is a **best-reply path of length $n$** from $s$ to $s'$ if there are strategy-tuples $s=s^0\to s^1\to\cdots\to s^n=s'$ with each $s^l\to s^{l+1}$ an edge of the best-reply graph.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_BestReplyEdge

namespace YoungConventions.RiskDominance

/-- **Directed path of a given length in the best-reply graph.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9),
used for `L(s)`.

`BestReplyPath u n s s'` holds iff there is a directed path of exactly `n` edges from `s` to `s′`. -/
def BestReplyPath {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → ((i : ι) → S i) → ℝ) : ℕ → ((i : ι) → S i) → ((i : ι) → S i) → Prop
  | 0, s, s' => s = s'
  | n + 1, s, s' => ∃ s'', BestReplyEdge u s s'' ∧ BestReplyPath u n s'' s'

end YoungConventions.RiskDominance


