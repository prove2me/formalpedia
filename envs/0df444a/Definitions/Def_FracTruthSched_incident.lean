-- Prove2me | Definitions.Def_FracTruthSched_incident
-- name    : FracTruthSched_incident
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:55.212693+00:00
-- url     : https://prove2.me/theorems/a8e0a16f-dcf0-4ece-8f5a-7beed742e62f
-- title:
--   Incidence of a machine and a core task
-- statement:
--   A machine $i$ is **incident** to a core task $e$ if $i$ is an endpoint of the edge $e$ or the owner of the self-loop $e$. These are the eligible machines of $e$; in a graph input, each machine's values are those on its incident core tasks.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Definition 3, p.9; §2.4, p.6

import Mathlib
import Definitions.Def_FracTruthSched_CoreTask

set_option autoImplicit false

namespace FracTruthSched

/-- Machine `i` is **incident** to a core task `e` (Anastasiadis et al., arXiv:2611.06642v1,
Definition 3, p.9: "each machine's values are those on the core tasks of which it is an endpoint or
the owner"): `i` is an endpoint of the edge `e`, or the owner of the self-loop `e`. These are the
*eligible* machines of `e` (§2.4, p.6; Definition 2, p.8). -/
def incident {n ℓ : ℕ} (i : Fin n) : CoreTask n ℓ → Prop
  | .inl e => i = e.1.1.1 ∨ i = e.1.1.2
  | .inr k => i = k

instance incident.decidablePred {n ℓ : ℕ} (i : Fin n) : DecidablePred (incident (ℓ := ℓ) i) :=
  fun e =>
    match e with
    | .inl e => inferInstanceAs (Decidable (i = e.1.1.1 ∨ i = e.1.1.2))
    | .inr k => inferInstanceAs (Decidable (i = k))

end FracTruthSched


