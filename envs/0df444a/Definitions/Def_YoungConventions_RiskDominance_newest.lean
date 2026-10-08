-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_newest
-- name    : YoungConventions_RiskDominance_newest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:15.724164+00:00
-- url     : https://prove2.me/theorems/8f8273a5-8490-4c78-994c-8d67011dedb2
-- title:
--   The right-most (most recent) play of a state
-- statement:
--   For a state $h=(s^1,\dots,s^m)\in H$ with $m\ge1$, the **right-most element** of $h$ is its most recent play $s^m$.
--
--   It is the new play appended by a transition: in (1) and (2) the transition probability from $h$ to a successor $h'$ is computed from the right-most element of $h'$.
--
--   **Formalization Note** Positions are `Fin m` with $m\ge1$ recorded by the instance `NeZero m`; the right-most play is position $m-1$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, pp. 61–62

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History

namespace YoungConventions.RiskDominance

/-- **The right-most (most recent) play of a state.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, pp. 61–62 (PDF pp. 6–7), where
"`s` is the right-most element of `h′`".

**Formalization Note.** The state space is only used with `m ≥ 1` (the paper fixes
`1 ≤ k ≤ m`), recorded by the instance `[NeZero m]`; the right-most play is position `m − 1`. -/
def newest {ι : Type*} {S : ι → Type*} {m : ℕ} [NeZero m] (h : YoungConventions.AdaptivePlay.History S m) : (i : ι) → S i :=
  h ⟨m - 1, Nat.sub_lt (NeZero.pos m) Nat.one_pos⟩

end YoungConventions.RiskDominance


