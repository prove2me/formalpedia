-- Prove2me | Definitions.Def_CausalFailureRank_Event
-- name    : CausalFailureRank_Event
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:53.351351+00:00
-- url     : https://prove2.me/theorems/47bf3be1-008e-4e21-a334-43287b1d1095
-- title:
--   Contracts, caps, actions and visible events
-- statement:
--   The **contract** is either current-window $I$ in the larger class, where an already committed correction may be executed later, or its variant requiring actual execution before advance. The **caps** are a review quota per stage and a cumulative call limit $H$; infinity means no cap. A policy may **review**, **write** a bit, **commit** a tool, **decline** a correction, **execute** a committed correction, or **stop**. The visible **events** are bought observations, its own writes, authoritative reports, and its own allocations; a history is a list of events.
--
--   Each review charges $c_i$, each actual correction charges $f_{ir}$, and no other event charges anything.
--
--   **Formalization Note** A history can contain no future fact and no unread tape entry, which is how freshness is modeled.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, pp.4–5

import Mathlib
import Definitions.Def_CausalFailureRank_Instance

namespace CausalFailureRank

/-- The allocation contract, §2, p.5, of Zang, Li, Jin, Xu, *Causal Failure Rank Determines
Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…).

**Formalization Note.** `current` is contract I in "the larger class in which an already committed
correction may be executed later"; `currentPay` also requires "actual execution before advance",
as "our upper controllers" do. -/
inductive Contract
  | current
  | currentPay
  deriving DecidableEq

/-- The given limits, §2, p.5: a review quota per stage and a cumulative call limit `H`.
`⊤` means no cap. -/
structure Caps (N : ℕ) where
  /-- The review quota of stage `i`. -/
  Q : Fin N → ℕ∞
  /-- The cumulative call limit. -/
  H : ℕ∞

/-- An action a policy may request. `execute j` carries out the correction committed at stage `j`.
**Formalization Note.** There is no blind overwrite and no pre-allocation: `commit` is legal only
right after an actual error report (see `step`). -/
inductive Action (N q : ℕ)
  | review
  | write (b : Bool)
  | commit (r : Fin q)
  | decline
  | execute (j : Fin N)
  | stop
  deriving DecidableEq

/-- A visible event, §2, p.4. **Formalization Note.** An event records only what the policy sees: an
observation it bought, its write, the authoritative report and its own allocations. No future fact
and no unread tape entry can occur in a history, which is what freshness says. -/
inductive Event {N q : ℕ} (I : Instance N q)
  | obs (i : Fin N) (y : I.α i)
  | wrote (i : Fin N) (b : Bool)
  | report (i : Fin N) (x : Bool)
  | committed (i : Fin N) (r : Fin q)
  | declined (i : Fin N)
  | executed (i : Fin N) (r : Fin q)

/-- The visible history of a run. -/
abbrev History {N q : ℕ} (I : Instance N q) : Type := List (Event I)

/-- The charge of one event: `c_i` for a review, `f_ir` for an actual correction, §2, p.5. -/
noncomputable def Event.charge {N q : ℕ} {I : Instance N q} : Event I → ℝ
  | .obs i _ => I.c i
  | .executed i r => I.f i r
  | _ => 0

/-- The observation charge of one event: `c_i` for a review and nothing else. -/
noncomputable def Event.obsCharge {N q : ℕ} {I : Instance N q} : Event I → ℝ
  | .obs i _ => I.c i
  | _ => 0

/-- Whether an event is a bought review. -/
def Event.isObs {N q : ℕ} {I : Instance N q} : Event I → Bool
  | .obs _ _ => true
  | _ => false

end CausalFailureRank


