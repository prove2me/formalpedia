-- Prove2me | Definitions.Def_EulerianLE_SameCircuit
-- name    : EulerianLE_SameCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:05.597117+00:00
-- url     : https://prove2.me/theorems/7f0b9fab-20a9-4083-94f6-21c7ff589cad
-- title:
--   Port pairings, splices, circuits and their orientations
-- statement:
--   A **port pairing** of a node $u$ is a perfect matching $\pi$ on its ports, stored as a list of *ordered* pairs: every port occurs in exactly one pair, as exactly one component. If $(i,\bar\imath)\in\pi$, the ports $i$ and $\bar\imath$ are **partners**. The **splice** of two stored pairs $(i,\bar\imath),(j,\bar\jmath)$ replaces them by $(i,\bar\jmath)$ and $(j,\bar\imath)$ (Program 3):
--   $$\pi\leftarrow\{(i,\bar\jmath),(j,\bar\imath)\}\cup\pi\setminus\{(i,\bar\imath),(j,\bar\jmath)\}.$$
--
--   A choice of a pairing at every node determines a decomposition of the network into edge-disjoint **circuits** (Corollary 3): in the graph on all ports in which the two ports of each edge and the two ports of each pair are adjacent, every port has degree two, and each component is a circuit. Two ports **lie on the same circuit** when they are in the same component. Traversing a circuit, one leaves a node through an *outgoing* port $o$, crosses the edge to $\mathrm{link}(o)$, and leaves the next node through the partner of $\mathrm{link}(o)$. The outgoing ports of the traversal that leaves through $o$ form the CW orientation of the circuit in which $o$ is an outgoing CW port.
--
--   These are the objects of Lemma 4 and of the configurations of the algorithm.
--
--   **Formalization Note** A circuit is identified with its class of ports; its edge set is the set of edges whose two ports lie in the class. The orientation in which $o$ is outgoing is the set `cwOrbit` of iterates of the traversal step from $o$.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §2, pp.6–7 (PDF pp.8–9): port pairings, Corollary 3, orientations, splice; Program 3, p.19

import Mathlib
import Definitions.Def_EulerianLE_Network

namespace EulerianLE

/-- A port pairing as stored by a node: a list of **ordered** pairs of its ports ("We store each port
pair as an ordered pair; membership (i, j) ∈ π refers to this stored order", Frei, Gelles, Ghazy,
Nolin, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.6). -/
abbrev Pairs (deg : ℕ) : Type := List (Fin deg × Fin deg)

/-- "A port pairing π is a perfect matching on [deg(u)]" (§2, p.6): every port occurs in exactly one
stored pair, as exactly one of its two components. -/
def IsPairing {deg : ℕ} (π : Pairs deg) : Prop :=
  (π.flatMap fun a => [a.1, a.2]).Perm (List.finRange deg)

/-- The other component of the first stored pair containing `i`: the partner `ī` of `i` when `π` is a
pairing (§2, p.6). -/
def otherEnd {deg : ℕ} (π : Pairs deg) (i : Fin deg) : Option (Fin deg) :=
  π.findSome? fun a => if a.1 = i then some a.2 else if a.2 = i then some a.1 else none

/-- Program 3, `Splice((i, ī), (j, j̄))` (p.19, PDF p.21): `π ← {(i, j̄), (j, ī)} ∪ π \ {(i, ī), (j, j̄)}`,
for stored pairs `a = (i, ī)` and `b = (j, j̄)`. -/
def splice {deg : ℕ} (π : Pairs deg) (a b : Fin deg × Fin deg) : Pairs deg :=
  ((π.erase a).erase b) ++ [(a.1, b.2), (b.1, a.2)]

variable {G : Network}

/-- The partner in `pp` (one pairing per node) of a port at its node; a port that occurs in no pair is
its own partner (this does not happen for pairings). -/
def partner (pp : ∀ v, Pairs (G.deg v)) (p : G.Port) : G.Port :=
  match otherEnd (pp p.1) p.2 with
  | some q => ⟨p.1, q⟩
  | none => p

/-- Two ports lie on the same circuit of the circuit decomposition determined by the pairings `pp`
(Corollary 3, p.6): they are in one component of "the multigraph on all ports in which the two ports
of each edge and the two ports of each port pair are adjacent" (§2, p.6).

**Formalization Note.** A circuit is identified with its class of ports. The edge set of a circuit is
the set of edges whose two ports lie in the class (both ports of an edge always lie in the same
class), and a node lies on the circuit when one of its ports does. -/
def SameCircuit (pp : ∀ v, Pairs (G.deg v)) : G.Port → G.Port → Prop :=
  Relation.EqvGen fun p q => q = G.link p ∨ q = partner pp p

/-- One step of a traversal on outgoing ports: cross the edge at the outgoing port `o`, then leave
the node reached through the partner of the port of arrival. -/
def nextOut (pp : ∀ v, Pairs (G.deg v)) (o : G.Port) : G.Port := partner pp (G.link o)

/-- The outgoing ports of the orientation in which `o` is an outgoing port of its circuit (§2, p.6,
"Each of the two traversal directions of a circuit is an orientation of it"): the traversal leaving
through `o` crosses, for each `o'` in this set, the edge at `o'` from `o'` to `G.link o'`.

**Formalization Note.** An oriented circuit with `o` an outgoing CW port is the circuit of `o`
together with the CW direction `cwOrbit pp o`. -/
def cwOrbit (pp : ∀ v, Pairs (G.deg v)) (o : G.Port) : Set G.Port :=
  {o' | ∃ n : ℕ, (nextOut pp)^[n] o = o'}

end EulerianLE


