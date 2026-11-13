-- Prove2me | Definitions.Def_PhysReaudit_Rule
-- name    : PhysReaudit_Rule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:26.878225+00:00
-- url     : https://prove2.me/theorems/21f04eed-0e4f-40f1-ba3b-6226e742b50f
-- title:
--   Audit actions, observations and rules with old data and private randomness
-- statement:
--   An **audit** of the changed target mechanism interacts with the physical system through four actions: a **root setup** (start a new episode at the root, cost 1; issued during an episode it abandons that episode, which is the paper's abort or restart), an **attempt** of the next transition of the current episode (cost 1), **accept** (stop and issue the certificate), and **stop** (stop without a certificate). After a costly action the auditor observes that a setup took place, the success bit of a navigation transition, or the Bernoulli outcome of the target transition.
--
--   An **audit rule** with side information in a measurable space $W$ is a map
--
--   $$
--   R:\;W\times\{\text{fresh histories}\}\to\{\text{setup},\text{attempt},\text{accept},\text{stop}\},
--   $$
--
--   measurable in $w\in W$ for each history. The side variable $w$ carries the old transcript and the rule's private randomness; the rule never sees the physical outcomes before they happen, so every decision is predictable.
--
--   **Formalization Note** Histories are lists of observations, most recent first. The sample space of an audit is $W\times\{0,1\}^{\mathbb N}\times\{0,1\}^{\mathbb N}$ (side variable, navigation tape, target tape).
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), §4, pp.2–3 (PDF pp.3–4), "Access, old evidence, and the decision": "An auditor may adaptively abort or restart", "The audit may use old data and private randomness"

import Mathlib

namespace PhysReaudit

/-- The auditor's actions in the navigation-limited audit
(Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, pp.2–3 (PDF pp.3–4), "Access, old evidence, and the decision").

* `setup`: a root setup, starting a new episode at the root (cost 1). Issued during an episode it abandons
  that episode: this is the paper's abort/restart (root resets are allowed, internal resets are not).
* `attempt`: attempt the next transition of the current episode (cost 1).
* `accept`: stop and accept (issue the certificate).
* `stop`: stop without a certificate. -/
inductive Action
  | setup
  | attempt
  | accept
  | stop
  deriving DecidableEq

/-- Every set of actions is measurable. -/
instance : MeasurableSpace Action := ⊤

/-- What the auditor observes after a costly action: `started` after a root setup, `nav ok` after a
navigation attempt (`ok = true` iff the transition succeeded), `target y` after the target transition
(`y` is the Bernoulli(q) outcome). -/
inductive Obs
  | started
  | nav (ok : Bool)
  | target (y : Bool)
  deriving DecidableEq

/-- The sample space of an audit: the side variable `w` (old data and private randomness), the
navigation tape and the target tape. -/
abbrev Omega (W : Type) : Type := W × ((ℕ → Bool) × (ℕ → Bool))

/-- An audit rule (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.3 (PDF p.4): "An auditor may adaptively abort or restart", "The audit may
use old data and private randomness").

The rule chooses its next action from the side variable `w ∈ W` (the old transcript together with private
randomness) and the list of fresh observations made so far, most recent first. It never sees the tapes
themselves, so every decision is predictable.

**Formalization Note** The decision is required to be measurable in `w` for each fresh history; the set
of histories is countable, so this makes every event of the audit measurable. -/
structure Rule (W : Type) [MeasurableSpace W] where
  /-- The next action, given the side variable and the fresh history (most recent observation first). -/
  decide : W → List Obs → Action
  /-- Measurability of the decision in the side variable. -/
  measurable_decide : ∀ h, Measurable (fun w => decide w h)

end PhysReaudit


