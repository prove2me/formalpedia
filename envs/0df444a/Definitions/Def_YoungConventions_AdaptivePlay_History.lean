-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_History
-- name    : YoungConventions_AdaptivePlay_History
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:19.81554+00:00
-- url     : https://prove2.me/theorems/8120b8d6-900b-4ed9-90bd-4c1d20ddbbd8
-- title:
--   The state space $H$: sequences of $m$ plays (§3, p. 61)
-- statement:
--   Fix a memory $m \in \mathbb N$. A **play** is a strategy tuple $s \in \prod_i S_i$. The state space of adaptive play is
--   $$H = \Big(\prod_i S_i\Big)^m,$$
--   the set of all sequences $h = (h_0, h_1, \dots, h_{m-1})$ of $m$ plays. A state records the plays of the last $m$ periods: if the current period is $t$, then $h = (s(t-m+1), \dots, s(t))$.
--
--   **Formalization Note** Positions are `Fin m`, read left to right: position $0$ is the oldest (left-most) play and position $m-1$ the most recent (right-most) play.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, p. 61 (PDF p. 6)

import Mathlib

namespace YoungConventions.AdaptivePlay

/-- **The state space `H` of adaptive play** (Young 1993, *The Evolution of Conventions*,
Econometrica 61:57–84, §3, p. 61, PDF p. 6): "a finite Markov chain on the state space `H`
consisting of all sequences of length `m` drawn from `∏Sᵢ`".

A state `h : History S m` is a sequence of `m` plays (strategy tuples).

**Formalization Note.** Positions are `Fin m`, read left to right: position `0` is the **oldest**
(left-most) play and position `m − 1` the most recent (right-most) play, as in the paper's
`h = (s(t − m + 1), …, s(t))`. -/
abbrev History {ι : Type*} (S : ι → Type*) (m : ℕ) : Type _ :=
  Fin m → ∀ i, S i

end YoungConventions.AdaptivePlay


