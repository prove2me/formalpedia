-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsAcyclic
-- name    : YoungConventions_RiskDominance_IsAcyclic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:12.180851+00:00
-- url     : https://prove2.me/theorems/c20e0729-6630-4107-b5ed-d257d8e78fe3
-- title:
--   Acyclic game
-- statement:
--   A game $\Gamma$ is **acyclic** if its best-reply graph contains no directed cycle, i.e. no nonempty directed path from a vertex back to itself.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64, displayed definition (Acyclic Game)

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_BestReplyEdge

namespace YoungConventions.RiskDominance

/-- **Acyclic game.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9), displayed definition: "A game `Γ` is acyclic if
its best reply graph contains no directed cycles."

**Formalization Note.** A directed cycle is a nonempty chain of edges from a vertex back to itself
(`Relation.TransGen`). -/
def IsAcyclic {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → ((i : ι) → S i) → ℝ) : Prop :=
  ∀ s : (i : ι) → S i, ¬ Relation.TransGen (BestReplyEdge u) s s

end YoungConventions.RiskDominance


