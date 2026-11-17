-- Prove2me | Definitions.Def_EulerianLE_Supplement_IsTwoEdgeConnected
-- name    : EulerianLE_Supplement_IsTwoEdgeConnected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:16:27.490064+00:00
-- url     : https://prove2.me/theorems/88ac400d-2fd0-451a-a7d9-5ff897dc7e07
-- title:
--   Simple and 2-edge-connected port-numbered networks
-- statement:
--   Let $G$ be a port-numbered network, as in the mission's model: a finite node set $V$, ports $0,\dots,\deg(u)-1$ at each node $u$, and an involution $\mathrm{link}$ without fixed points that pairs every port with the port at the other end of its edge.
--
--   1. $G$ is **simple** when no edge is a self-loop ($\mathrm{link}(p)$ never lies at the node of $p$) and no two distinct ports of one node lead to the same neighbour (no parallel edges).
--   2. $G$ is **2-edge-connected** when it has at least one node, any two nodes are joined by a path, and any two nodes are still joined by a path after any single edge $\{p,\mathrm{link}(p)\}$ is deleted.
--
--   These are the networks of the paper's lower bound: 2-edge-connected graphs $G=(V,E)$ with any port numbering. The one-node network without edges is 2-edge-connected, with $|E|=0$; the empty network is not.
--
--   **Formalization Note** The mission's `Network` is a multigraph; `IsSimpleNet` cuts out the simple graphs. Connectivity is the reflexive-transitive closure of adjacency, and "after deleting the edge at $p$" uses only the ports other than $p$ and $\mathrm{link}(p)$.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §6, pp.26–28 (PDF pp.28–30), Lemma 16 and Theorem 18

import Mathlib
import Definitions.Def_EulerianLE_Network

namespace EulerianLE.Supplement

/-- A **simple** network (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election
on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §6, pp.26–28, PDF pp.28–30:
the networks of the lower bound are graphs `G = (V, E)`): no edge is a self-loop, and no two distinct
ports of one node lead to the same node (no parallel edges).

**Formalization Note.** The published `Network` is a port-numbered multigraph; this predicate cuts out
the simple graphs, with every port numbering. -/
def IsSimpleNet (G : Network) : Prop :=
  (∀ p : G.Port, (G.link p).1 ≠ p.1) ∧
  ∀ p q : G.Port, p.1 = q.1 → (G.link p).1 = (G.link q).1 → p = q

/-- `u` and `w` are joined by an edge other than the edge `{p, link p}`. -/
def AdjacentAvoiding (G : Network) (p : G.Port) (u w : G.V) : Prop :=
  ∃ q : G.Port, q ≠ p ∧ q ≠ G.link p ∧ q.1 = u ∧ (G.link q).1 = w

/-- A **2-edge-connected** network (§6, p.26 and Lemma 16, p.27, PDF pp.28–29): it has a node, any two
nodes are joined by a path, and they stay joined by a path after any single edge `{p, link p}` is
deleted.

**Formalization Note.** A network with no node is excluded (a connected graph has a node, and leader
election on it is impossible). The one-node network without ports is 2-edge-connected; it has
`|E| = 0`. -/
def IsTwoEdgeConnected (G : Network) : Prop :=
  Nonempty G.V ∧
  (∀ u v, Relation.ReflTransGen G.Adjacent u v) ∧
  ∀ p : G.Port, ∀ u v, Relation.ReflTransGen (AdjacentAvoiding G p) u v

end EulerianLE.Supplement


