-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_IsBestReply
-- name    : YoungConventions_AdaptivePlay_IsBestReply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:16.352986+00:00
-- url     : https://prove2.me/theorems/d6c9312b-451b-40ef-8a9e-149ed76a5616
-- title:
--   Best reply $x$ of player $i$ to $s_{-i}$ (§4, p. 64)
-- statement:
--   Let $\Gamma$ be a game in strategic form with a finite set of players, a strategy set $S_i$ for each player $i$, and real payoff functions $u_i(s)$ defined on strategy tuples $s = (s_1,\dots,s_n) \in \prod_j S_j$. For a strategy tuple $s$ write $(x, s_{-i})$ for the tuple obtained from $s$ by replacing the strategy of player $i$ with $x \in S_i$.
--
--   A strategy $x \in S_i$ is a **best reply of player $i$ to $s_{-i}$** if
--   $$u_i(y, s_{-i}) \le u_i(x, s_{-i}) \qquad \text{for every } y \in S_i .$$
--
--   Best replies are pure strategies and need not be unique. This is the notion used to define the edges of the best-reply graph.
--
--   **Formalization Note** The payoffs are `u : ι → (∀ i, S i) → ℝ`, and $(x, s_{-i})$ is `Function.update s i x`; the $i$-th coordinate of $s$ plays no role.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9), definition of the best-reply graph

import Mathlib

namespace YoungConventions.AdaptivePlay

/-- **Best reply to `s₋ᵢ`** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84,
§4, p. 64, PDF p. 9, in the definition of the best-reply graph: "`s′ᵢ` is a best reply to `s₋ᵢ`").

The strategy `x ∈ Sᵢ` is a best reply of player `i` to the strategies `s₋ᵢ` of the other players
if no strategy `y ∈ Sᵢ` gives `i` a strictly higher payoff against `s₋ᵢ`:
`uᵢ(y, s₋ᵢ) ≤ uᵢ(x, s₋ᵢ)` for all `y`.

**Formalization Note.** The players are a type `ι`, the strategies a family `S : ι → Type*`, and the
payoffs `u : ι → (∀ i, S i) → ℝ` (`u i s` is `uᵢ(s)`, p. 61). The profile `(y, s₋ᵢ)` is
`Function.update s i y`; the `i`-th coordinate of `s` itself is ignored. Best replies are pure
strategies and need not be unique. -/
def IsBestReply {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (i : ι) (s : ∀ i, S i) (x : S i) : Prop :=
  ∀ y : S i, u i (Function.update s i y) ≤ u i (Function.update s i x)

end YoungConventions.AdaptivePlay


