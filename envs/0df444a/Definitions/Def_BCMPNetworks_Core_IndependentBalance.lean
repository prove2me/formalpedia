-- Prove2me | Definitions.Def_BCMPNetworks_Core_IndependentBalance
-- name    : BCMPNetworks_Core_IndependentBalance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:41:27.941777+00:00
-- url     : https://prove2.me/theorems/fc926f6e-a10c-4cb7-9631-c9613e79f086
-- title:
--   Independent balance equations for BCMP networks
-- statement:
--   Each customer is associated with a **label** (§3.1, p. 252): a customer in service or queued at a type 2, 3 or 4 center $i$ with class $r$ is in stage $l$ of its service time (for LCFS, the stage it was in when last preempted); every customer at a type-1 center $i$ is associated with the center $i$ itself (its single exponential stage); and a customer arriving from, or leaving to, the outside is associated with the outside world of its subchain $E_k$.
--
--   Every event moves one customer; it **leaves** one label and **enters** another. A function $\pi$ on states satisfies the **independent balance equations** when, for every state $S$ and every label $L$,
--   $$\pi(S)\cdot\big(\text{rate of events out of } S \text{ whose customer leaves } L\big) = \sum_{S'} \pi(S')\cdot\big(\text{rate of events } S' \to S \text{ whose customer enters } L\big).$$
--
--   These are the paper's sufficient conditions for global balance; the product form is proved by checking them.
--
--   **Formalization Note** At a type-1 center the label is the center, not the pair (center, class): the out-flow of an FCFS center is caused by the head's class and the in-flow by the arriving customer's class, and per-class labels are inconsistent there (p. 253). The outside world is split per subchain under both arrival processes; this is a finer family of equations than a single outside label.
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), pp. 251-252, Section 3.1 (independent balance equations); p. 253, Section 3.1

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics

namespace BCMPNetworks.Core

/-- The "stage of service" a customer is associated with in the independent balance
equations (§3.1, p. 252): the outside world of subchain `k` (for customers arriving from, or
leaving to, outside the network), a whole type-1 center `i` (every customer at an FCFS center
is associated with its single exponential stage), or stage `l` of the class-`r` service time
at a type-2, -3 or -4 center `i`. -/
inductive Label (N R m : ℕ)
  | outside (k : Fin m)
  | center (i : Fin N)
  | stage (i : Fin N) (r : Fin R) (l : ℕ)
  deriving DecidableEq

namespace Network

variable {N R m : ℕ} (net : Network N R m)

/-- The label a class-`s` customer is associated with on entering center `j`: the center
itself if it is of type 1, stage `0` of its service time otherwise. -/
def entryLabel (j : Fin N) (s : Fin R) : Label N R m :=
  if net.type j = .fcfs then .center j else .stage j s 0

/-- The label a class-`r` customer completing service at center `i` enters when routed to
`d`: the outside world of its subchain, or the entry label of its next center. -/
def destLabel (i : Fin N) (r : Fin R) : Option (Fin N × Fin R) → Label N R m
  | none => .outside (net.chain i r)
  | some (j, s) => net.entryLabel j s

/-- The label of the customer that moves in event `ev`, as seen before the event: the label
it leaves. -/
def leaveLabel (S : net.Config) : Event N R net.u → Label N R m
  | .arrive j s => .outside (net.chain j s)
  | .fcfsDone i _ => .center i
  | .stageNext i r l => .stage i r l.val
  | .stageDone i r l _ => .stage i r l.val
  | .lcfsNext i =>
      match S i with
      | .lcfs (x :: _) => .stage i x.1 x.2.val
      | _ => .center i
  | .lcfsDone i _ =>
      match S i with
      | .lcfs (x :: _) => .stage i x.1 x.2.val
      | _ => .center i

/-- The label the moving customer of event `ev` enters. -/
def enterLabel (S : net.Config) : Event N R net.u → Label N R m
  | .arrive j s => net.entryLabel j s
  | .fcfsDone i d =>
      match S i with
      | .fcfs (r :: _) => net.destLabel i r d
      | _ => .center i
  | .stageNext i r l => .stage i r (l.val + 1)
  | .stageDone i r _ d => net.destLabel i r d
  | .lcfsNext i =>
      match S i with
      | .lcfs (x :: _) => .stage i x.1 (x.2.val + 1)
      | _ => .center i
  | .lcfsDone i d =>
      match S i with
      | .lcfs (x :: _) => net.destLabel i x.1 d
      | _ => .center i

open Classical in
/-- The independent balance equations (§3.1, p. 252): for every state `S` and every label
`L`, the rate of flow out of `S` due to a customer leaving `L` equals the rate of flow into
`S` due to a customer entering `L`:
`π(S) ∑_{ev : leaves L} rate(S, ev) = ∑_{S'} π(S') ∑_{ev : S' → S, enters L} rate(S', ev)`. -/
noncomputable def IndependentBalance (π : net.State → ℝ) : Prop :=
  ∀ (S : net.State) (L : Label N R m),
    π S * ∑ ev : Event N R net.u,
        (if net.leaveLabel S.1 ev = L then net.evRate S.1 ev else 0) =
      ∑' S' : net.State, π S' * ∑ ev : Event N R net.u,
        (if net.evTarget S'.1 ev = S.1 ∧ net.enterLabel S'.1 ev = L
          then net.evRate S'.1 ev else 0)

end Network

end BCMPNetworks.Core


