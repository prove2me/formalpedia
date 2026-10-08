-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_BestReplyEdge
-- name    : YoungConventions_AdaptivePlay_BestReplyEdge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:44.634777+00:00
-- url     : https://prove2.me/theorems/2fa9e939-5953-498e-9898-33d064ab88fa
-- title:
--   Edge $s \to s'$ of the best-reply graph (§4, p. 64)
-- statement:
--   The **best-reply graph** of a game $\Gamma$ has the strategy tuples $s \in \prod_j S_j$ as vertices. There is a directed edge $s \to s'$ if and only if $s \neq s'$ and there is exactly one player $i$ such that $s'_i$ is a best reply to $s_{-i}$ and $s'_{-i} = s_{-i}$.
--
--   Equivalently, $s \to s'$ is an edge if and only if there are a player $i$ and a strategy $x \in S_i$ with
--   $$x \neq s_i, \qquad x \text{ a best reply of } i \text{ to } s_{-i}, \qquad s' = (x, s_{-i}).$$
--   An edge is thus a single player switching to a different best reply against the current strategies of the others.
--
--   **Formalization Note** The second form is the one formalized. It is equivalent to the paper's: if $s \neq s'$ and $s'_{-i} = s_{-i}$, then $s$ and $s'$ differ exactly in coordinate $i$, so the player $i$ is automatically unique.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReply

namespace YoungConventions.AdaptivePlay

/-- **Edge of the best-reply graph** (Young 1993, *The Evolution of Conventions*, Econometrica
61:57–84, §4, p. 64, PDF p. 9): "each vertex is an `n`-tuple of strategies `s ∈ ∏Sᵢ`, and for
every two vertices `s` and `s′` there is a directed edge `s → s′` if and only if `s ≠ s′` and there
exists exactly one agent `i` such that `s′ᵢ` is a best reply to `s₋ᵢ` and `s′₋ᵢ = s₋ᵢ`."

`BestReplyEdge u s s'` holds iff some player `i` and some strategy `x ≠ sᵢ` that is a best reply of
`i` to `s₋ᵢ` give `s′ = (x, s₋ᵢ)`.

**Formalization Note.** Equivalence with the page: if `s ≠ s′` and `s′₋ᵢ = s₋ᵢ`, then `s` and `s′`
differ exactly in coordinate `i`, so the agent `i` is automatically unique and "exactly one" adds
nothing; and `s ≠ s′` with `s′ = (x, s₋ᵢ)` is `x ≠ sᵢ`. Best replies are pure best replies
(`IsBestReply`), not best replies to a sample. -/
def BestReplyEdge {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s s' : ∀ i, S i) : Prop :=
  ∃ (i : ι) (x : S i), x ≠ s i ∧ IsBestReply u i s x ∧ s' = Function.update s i x

end YoungConventions.AdaptivePlay


