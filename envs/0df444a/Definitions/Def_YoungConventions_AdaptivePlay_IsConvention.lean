-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_IsConvention
-- name    : YoungConventions_AdaptivePlay_IsConvention
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:02:04.038888+00:00
-- url     : https://prove2.me/theorems/d00423b2-e9d3-4476-b0f5-f9426ac0bfff
-- title:
--   Convention: $m$ repetitions of a strict pure Nash equilibrium (§4, p. 62)
-- statement:
--   A state $h \in H$ is a **convention** if it consists of $m$ repetitions of a strict pure strategy Nash equilibrium:
--   $$h = (s, s, \dots, s) \qquad \text{for some strict pure Nash equilibrium } s .$$
--
--   Conventions are the absorbing states of adaptive play. Once reached, every sample shows only $s$, and each player's unique best reply keeps $s$ in place.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 62 (PDF p. 7)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash

namespace YoungConventions.AdaptivePlay

/-- **Convention** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84, §4, p. 62,
PDF p. 7): "any state `h` consisting of `m` repetitions of a strict, pure strategy Nash
equilibrium is clearly an absorbing state. Such a state will be called a *convention*."

`IsConvention u h` holds iff there is a strict pure Nash equilibrium `s` with `h = (s, s, …, s)`
(every one of the `m` positions holds `s`).

**Formalization Note.** For `m = 0` the empty history would count as a convention as soon as the
game has a strict Nash equilibrium; every theorem of the mission assumes `1 ≤ k ≤ m`. -/
def IsConvention {ι : Type*} [DecidableEq ι] {S : ι → Type*} {m : ℕ}
    (u : ι → (∀ i, S i) → ℝ) (h : History S m) : Prop :=
  ∃ s : ∀ i, S i, IsStrictNash u s ∧ h = fun _ => s

end YoungConventions.AdaptivePlay


