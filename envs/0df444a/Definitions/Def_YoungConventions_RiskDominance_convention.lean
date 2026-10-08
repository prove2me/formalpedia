-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_convention
-- name    : YoungConventions_RiskDominance_convention
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:44.846274+00:00
-- url     : https://prove2.me/theorems/b39c23cc-0aff-4bae-bea9-3242210ce5b6
-- title:
--   The state of $m$ repetitions of a play
-- statement:
--   For a strategy-tuple $s$, $(s,s,\dots,s)\in H$ is the state consisting of $m$ repetitions of $s$. For the $2\times2$ case, $h_1=((1,1),\dots,(1,1))$ and $h_2=((2,2),\dots,(2,2))$ are of this form.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 62; §7, p. 70

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History

namespace YoungConventions.RiskDominance

/-- **The state of `m` repetitions of a play.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 62 (PDF p. 7): "any state `h`
consisting of `m` repetitions of a strict, pure strategy Nash equilibrium ... Such a state will be
called a convention"; §7, p. 70 (PDF p. 15): `h₁ = ((1,1), (1,1), …, (1,1))`.

`convention s` is the state `(s, s, …, s)` of length `m`. -/
def convention {ι : Type*} {S : ι → Type*} {m : ℕ} (s : (i : ι) → S i) : YoungConventions.AdaptivePlay.History S m :=
  fun _ => s

end YoungConventions.RiskDominance


