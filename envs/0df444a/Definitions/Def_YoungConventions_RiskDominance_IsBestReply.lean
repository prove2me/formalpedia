-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsBestReply
-- name    : YoungConventions_RiskDominance_IsBestReply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:15.57915+00:00
-- url     : https://prove2.me/theorems/b82e90cd-db07-4e9c-9d81-c34214c03470
-- title:
--   Pure best reply to $s_{-i}$
-- statement:
--   For a strategy-tuple $s$ and a player $i$, a strategy $x\in S_i$ is a **best reply to $s_{-i}$** if
--   $$u_i(y,s_{-i})\le u_i(x,s_{-i})\qquad\text{for all }y\in S_i.$$
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64

import Mathlib

namespace YoungConventions.RiskDominance

/-- **Pure best reply to `s₋ᵢ`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9), in the definition of the best-reply
graph: "`s′ᵢ` is a best reply to `s₋ᵢ`".

`x` is a best reply of `i` to `s₋ᵢ` iff `uᵢ(y, s₋ᵢ) ≤ uᵢ(x, s₋ᵢ)` for every `y ∈ Sᵢ`.

**Formalization Note.** `Function.update s i y` is the profile `(y, s₋ᵢ)`. -/
def IsBestReply {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → ((i : ι) → S i) → ℝ) (s : (i : ι) → S i) (i : ι) (x : S i) : Prop :=
  ∀ y : S i, u i (Function.update s i y) ≤ u i (Function.update s i x)

end YoungConventions.RiskDominance


