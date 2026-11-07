-- Prove2me | Definitions.Def_EulerianLE_relayTrail
-- name    : EulerianLE_relayTrail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:01:13.439727+00:00
-- url     : https://prove2.me/theorems/dbdd2089-20cb-4bcb-a3f6-05823d14aa64
-- title:
--   Relay trails, successors, local leaders, and acting as an edge
-- statement:
--   Fix a round $r$ and the input pairing $\pi^\top$. For a port $p$ of a non-relay node, the **relay trail** from $p$ follows the circuit of $\pi^\top$ through $p$ until it first reaches a non-relay node: it crosses the edge at $p$, enters a Relay node $x_h$ through a port $q_h$ and leaves through the partner $\bar q_h$, and stops at the port $q$ of the first non-relay node it reaches. The port $q$ is the **successor** of $p$, its node the successor node, and the pairs $(q_h,\bar q_h)$ are the **relay pairs** of the trail.
--
--   The Check node $u$ is a **local leader** if the successor node of every port of $u$ is $u$ itself.
--
--   A relay trail from $p$ to $q$ **acts as an edge** if every pulse sent through either endpoint is eventually delivered at the other endpoint and every relay pair on the trail sends only by forwarding pulses: in counts, the pulses delivered at each endpoint never exceed, and eventually reach, those sent through the other, and every relay pair has sent through $\bar q_h$ at most as many pulses as it consumed at $q_h$, and through $q_h$ at most as many as it consumed at $\bar q_h$.
--
--   **Formalization Note** Trails refer to $\pi^\top$ "even after the algorithm changes a pairing" (p.36). Pulses are indistinguishable and channels FIFO, so the count form says exactly that pulses flow between the endpoints without reflection.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.2, pp.36–37 (PDF pp.38–39): relay trails, successors, acting as an edge; App. C.3, p.38: local leader

import Mathlib
import Definitions.Def_EulerianLE_ValidConfig

namespace EulerianLE

variable {G : Network}

/-- The relay trail from the port arrived at, with fuel: the entry ports of the Relay nodes crossed,
in order, and the port of the first non-relay node reached. -/
def trailAux (nr : G.V → Bool) (pp : ∀ v, Pairs (G.deg v)) : ℕ → G.Port → List G.Port × Option G.Port
  | 0, _ => ([], none)
  | n + 1, y =>
    if nr y.1 then ([], some y)
    else
      let r := trailAux nr pp n (G.link (partner pp y))
      (y :: r.1, r.2)

/-- The relay trail from a port `p` of a non-relay node (Frei, Gelles, Ghazy, Nolin, STOC 2027 submission
(manuscript sha256 90954a93…), §C.2, pp.36–37): "Starting through p, follow the circuit of π⊤
through p until first reaching a non-relay node". The result lists the ports `q_h` through which the
trail enters its Relay nodes `x_1, …, x_{k−1}` (it leaves `x_h` through the partner `q̄_h`; the relay
pairs of the trail are the pairs `(q_h, q̄_h)`), and the port `q` at which it reaches a non-relay node,
the **successor** of `p` (`none` only if no non-relay node is reached).

**Formalization Note.** `pp` is the input pairing `π⊤` of the round ("The relay trails and successors
defined below refer to the pairing π⊤ of the input configuration I, even after the algorithm changes a
pairing", p.36). The fuel, the number of ports, bounds the length of any trail. -/
def relayTrail (ids : G.V → ℕ) (r : ℕ) (pp : ∀ v, Pairs (G.deg v)) (p : G.Port) :
    List G.Port × Option G.Port :=
  trailAux (fun u => decide (NonRelay G ids r u)) pp (Fintype.card G.Port) (G.link p)

/-- The successor of `p`. -/
def succPort (ids : G.V → ℕ) (r : ℕ) (pp : ∀ v, Pairs (G.deg v)) (p : G.Port) : Option G.Port :=
  (relayTrail ids r pp p).2

/-- The successor node of `p` is Counting in round `r`. -/
def SuccCounting (ids : G.V → ℕ) (r : ℕ) (pp : ∀ v, Pairs (G.deg v)) (p : G.Port) : Prop :=
  ∃ q, succPort ids r pp p = some q ∧ r ≤ ids q.1

/-- The Check node `u` of round `r` is a **local leader** (§C.3, p.38): "the successor node of every
port of u is u itself". -/
def IsLocalLeader (ids : G.V → ℕ) (r : ℕ) (pp : ∀ v, Pairs (G.deg v)) (u : G.V) : Prop :=
  ids u + 1 = r ∧ ∀ i : Fin (G.deg u), ∃ q, succPort ids r pp ⟨u, i⟩ = some q ∧ q.1 = u

variable {Out : G.V → Type} {P : ∀ v, NodeProg (G.deg v) (Out v)} {tag : Tag P}

/-- At time `t`, every send so far by a relay pair on the trail forwards a pulse away from the endpoint
it comes from (Lemma 22(a), p.37), in count form: for each relay pair `(y, ȳ)` of the trail, entered at
`y` from the side of the first endpoint, the pair has sent through `ȳ` at most as many pulses as it
consumed at `y`, and through `y` at most as many as it consumed at `ȳ`.

**Formalization Note.** Pulses are indistinguishable and channels FIFO (§2, p.8), and "we regard the
sent pulse as the consumed pulse, forwarded" (p.8); a reflection (a send back through the port of
consumption) is exactly what these inequalities exclude. -/
def ForwardsAway (ρ : Run P tag) (pp : ∀ v, Pairs (G.deg v)) (ys : List G.Port) (t : ℕ) : Prop :=
  ∀ y ∈ ys, (ρ.cfg t).sent (partner pp y) ≤ (ρ.cfg t).consumed y ∧
    (ρ.cfg t).sent y ≤ (ρ.cfg t).consumed (partner pp y)

/-- A relay trail with endpoints `p`, `q` and relay-pair entry ports `ys` acts as an edge (§C.2, p.37):
"every pulse sent through either endpoint is eventually delivered at the other endpoint, and every
relay pair on the trail sends only by forwarding pulses"; in count form, the pulses delivered at each
endpoint are at most those sent through the other at every time and eventually at least those sent
through the other by any given time, and the relay pairs only forward. -/
def ActsAsEdge (ρ : Run P tag) (pp : ∀ v, Pairs (G.deg v)) (p q : G.Port) (ys : List G.Port) : Prop :=
  (∀ t, ∃ t', (ρ.cfg t).sent p ≤ (ρ.cfg t').delivered q) ∧
  (∀ t, ∃ t', (ρ.cfg t).sent q ≤ (ρ.cfg t').delivered p) ∧
  (∀ t, (ρ.cfg t).delivered q ≤ (ρ.cfg t).sent p ∧ (ρ.cfg t).delivered p ≤ (ρ.cfg t).sent q) ∧
  ∀ t, ForwardsAway ρ pp ys t

end EulerianLE


