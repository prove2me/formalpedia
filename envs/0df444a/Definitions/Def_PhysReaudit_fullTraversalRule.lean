-- Prove2me | Definitions.Def_PhysReaudit_fullTraversalRule
-- name    : PhysReaudit_fullTraversalRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:44:05.9284+00:00
-- url     : https://prove2.me/theorems/e5580e2d-0cd0-4518-ad79-f557c9730fd8
-- title:
--   Rules that traverse full episodes without voluntary aborts
-- statement:
--   Given a stopping decision $\sigma$ on finite lists of target outcomes, with values *continue*, *accept* or *stop*, the **full-traversal rule** with decision $\sigma$ acts as follows. At each step it evaluates $\sigma$ on the target outcomes observed so far. If $\sigma$ says accept or stop, the rule halts accordingly; otherwise it attempts the next transition inside an active episode and issues a new root setup when no episode is active (at the start, after a navigation failure, and after a target observation).
--
--   Such a rule never aborts an episode voluntarily, and since the list of target outcomes changes only at a target observation it can halt only at the start or right after a target observation. Whether the $i$-th target observation is requested depends only on the earlier target outcomes. The SPRT of Theorem 4 is such a rule.
--
--   **Formalization Note** The decision $\sigma$ does not depend on the side variable; the rule ignores old data.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), Proposition 3, p.3 (PDF p.4): "Traversing episodes without voluntary aborts"; proof of Theorem 4, p.4 (PDF p.5): "Traverse full episodes until each next target observation Yi is obtained"; "Whether observation i is requested depends only on earlier target outcomes"

import Mathlib
import Definitions.Def_PhysReaudit_Rule

namespace PhysReaudit

/-- The target outcomes recorded in a fresh history, most recent first. -/
def targets : List Obs → List Bool
  | [] => []
  | .target y :: h => y :: targets h
  | _ :: h => targets h

/-- Whether an episode is active after the given history: the last observation is a root setup or a
successful navigation transition. -/
def inEpisode : List Obs → Bool
  | .started :: _ => true
  | .nav true :: _ => true
  | _ => false

/-- A rule that traverses full episodes without voluntary aborts
(Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), Proposition 3, p.3 (PDF p.4): "Traversing episodes without voluntary aborts"; proof of Theorem 4,
p.4: "Traverse full episodes until each next target observation Yi is obtained").

At every step it consults `stopDec` on the target outcomes seen so far: `some true` accepts, `some false`
stops without a certificate, and `none` continues, attempting the next transition inside an active episode
and issuing a new root setup otherwise (at the start, after a navigation failure, after a target
observation). Since the list of target outcomes changes only at a target observation, the rule stops only
at the start or right after a target observation.

**Formalization Note** The stopping decision depends only on the target outcomes, not on the side variable;
the rule is constant in `w`. -/
def fullTraversalRule (W : Type) [MeasurableSpace W] (stopDec : List Bool → Option Bool) : Rule W where
  decide _ h :=
    match stopDec (targets h) with
    | some true => .accept
    | some false => .stop
    | none => if inEpisode h then .attempt else .setup
  measurable_decide _ := measurable_const

end PhysReaudit


