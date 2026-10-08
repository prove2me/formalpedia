-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_IsSink
-- name    : YoungConventions_AdaptivePlay_IsSink
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:59:51.562862+00:00
-- url     : https://prove2.me/theorems/9e3aea8f-1177-4ffc-a31e-fe49520d5ada
-- title:
--   Sink of the best-reply graph (§4, p. 64)
-- statement:
--   A strategy tuple $s$ is a **sink** of the best-reply graph of $\Gamma$ if no edge leaves it: there is no $s'$ with $s \to s'$.
--
--   Sinks are the end points of the paths in the definition of weak acyclicity.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9), displayed definition 'Acyclic Game'

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_BestReplyEdge

namespace YoungConventions.AdaptivePlay

/-- **Sink of the best-reply graph** (Young 1993, *The Evolution of Conventions*, Econometrica
61:57–84, §4, p. 64, PDF p. 9: "some vertex `s*` from which there is no exiting edge (a *sink*)").

The vertex `s` is a sink if there is no edge `s → s′` of the best-reply graph. -/
def IsSink {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ s' : ∀ i, S i, ¬ BestReplyEdge u s s'

end YoungConventions.AdaptivePlay


