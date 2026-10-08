-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_BestReplyEdge
-- name    : YoungConventions_RiskDominance_BestReplyEdge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:54.246986+00:00
-- url     : https://prove2.me/theorems/8c798571-8908-4e5b-8897-c914ab7329f5
-- title:
--   Edge of the best-reply graph
-- statement:
--   The **best-reply graph** of $\Gamma$ has the strategy-tuples $s\in\prod_iS_i$ as vertices, and a directed edge $s\to s'$ if and only if $s\neq s'$ and there is exactly one agent $i$ such that $s'_i$ is a best reply to $s_{-i}$ and $s'_{-i}=s_{-i}$.
--
--   **Formalization Note** Encoded as: there are an agent $i$ and a best reply $x\neq s_i$ to $s_{-i}$ with $s'=(x,s_{-i})$. This is equivalent: if $s\ne s'$ and $s'_{-i}=s_{-i}$, then $i$ is automatically the only such agent.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_IsBestReply

namespace YoungConventions.RiskDominance

/-- **Edge of the best-reply graph.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9): "each vertex is an `n`-tuple of
strategies `s ∈ ΠSᵢ`, and for every two vertices `s` and `s′` there is a directed edge `s → s′` if and
only if `s ≠ s′` and there exists exactly one agent `i` such that `s′ᵢ` is a best reply to `s₋ᵢ` and
`s′₋ᵢ = s₋ᵢ`."

**Formalization Note.** Encoded as: some agent `i` and some `x ≠ sᵢ` with `x` a best reply to `s₋ᵢ`
and `s′ = (x, s₋ᵢ)`. This is equivalent to the page: if `s ≠ s′` and `s′₋ᵢ = s₋ᵢ`, then `s′ᵢ ≠ sᵢ`
and no other agent `j` has `s′₋ⱼ = s₋ⱼ`, so "exactly one" is automatic. -/
def BestReplyEdge {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → ((i : ι) → S i) → ℝ) (s s' : (i : ι) → S i) : Prop :=
  ∃ (i : ι) (x : S i), x ≠ s i ∧ IsBestReply u s i x ∧ s' = Function.update s i x

end YoungConventions.RiskDominance


