-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsConvention
-- name    : YoungConventions_RiskDominance_IsConvention
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:14.12+00:00
-- url     : https://prove2.me/theorems/47ce4ac9-bbdc-478e-8456-f7875371960a
-- title:
--   Convention
-- statement:
--   A state $h\in H$ is a **convention** if it consists of $m$ repetitions of a strict pure-strategy Nash equilibrium: $h=(s,s,\dots,s)$ for some strict pure Nash equilibrium $s$. Conventions are exactly the absorbing states of adaptive play without mistakes (p. 62).
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 62

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_convention
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash

namespace YoungConventions.RiskDominance

/-- **Convention.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 62 (PDF p. 7): "any state `h` consisting of `m` repetitions of a
strict, pure strategy Nash equilibrium is clearly an absorbing state. Such a state will be called a
convention." -/
def IsConvention {ι : Type*} [DecidableEq ι] {S : ι → Type*} {m : ℕ}
    (u : ι → ((i : ι) → S i) → ℝ) (h : YoungConventions.AdaptivePlay.History S m) : Prop :=
  ∃ s, YoungConventions.AdaptivePlay.IsStrictNash u s ∧ h = convention s

end YoungConventions.RiskDominance


