-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsWeaklyAcyclic
-- name    : YoungConventions_RiskDominance_IsWeaklyAcyclic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:28.868767+00:00
-- url     : https://prove2.me/theorems/b3750f61-161e-4dab-89ff-8dd1f462ce69
-- title:
--   Weakly acyclic game
-- statement:
--   A game $\Gamma$ is **weakly acyclic** if from any initial vertex $s$ of its best-reply graph there is a directed path to some vertex $s^*$ from which there is no exiting edge (a **sink**).
--
--   **Formalization Note** Directed paths may be empty, so a sink reaches itself.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64, displayed definition (Acyclic Game)

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_BestReplyEdge

namespace YoungConventions.RiskDominance

/-- **Weakly acyclic game.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9), displayed definition: "It is weakly acyclic
if, from any initial vertex `s`, there exists a directed path to some vertex `s*` from which there is
no exiting edge (a sink)."

**Formalization Note.** A directed path may be empty (`Relation.ReflTransGen`), so a sink is reached
from itself. -/
def IsWeaklyAcyclic {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → ((i : ι) → S i) → ℝ) : Prop :=
  ∀ s : (i : ι) → S i, ∃ s' : (i : ι) → S i,
    Relation.ReflTransGen (BestReplyEdge u) s s' ∧ ∀ s'', ¬ BestReplyEdge u s' s''

end YoungConventions.RiskDominance


