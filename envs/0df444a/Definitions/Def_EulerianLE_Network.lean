-- Prove2me | Definitions.Def_EulerianLE_Network
-- name    : EulerianLE_Network
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:29.205444+00:00
-- url     : https://prove2.me/theorems/b4e0f970-a4e5-4084-9f81-e867c3c7fd28
-- title:
--   Port-numbered network, $|E|$ and $\mathrm{ID}_{\max}$
-- statement:
--   The network is a finite set $V$ of nodes; node $u$ has ports $0,1,\dots,\deg(u)-1$ (the paper numbers them $1,\dots,\deg(u)$). Write $\mathrm{link}(p)$ for the port at the other end of the edge at port $p$. The map $\mathrm{link}$ is an involution without fixed points, and an **edge** is a pair $\{p,\mathrm{link}(p)\}$; a self-loop joins two ports of the same node, and several edges may join the same two nodes.
--
--   The network is **Eulerian** when every degree is even, there is at least one edge ($|E|\ge 1$), and any two nodes are joined by a path. The number of edges is $|E|$, half the number of ports, and for identifiers $\mathrm{ID}:V\to\mathbb N$ we write
--   $$\mathrm{ID}_{\max}=\max_{u\in V}\mathrm{ID}_u .$$
--
--   This is the network of the paper: "a finite connected undirected Eulerian graph $G=(V,E)$" whose ports are numbered at each node, with $|E|\ge1$ and distinct nonnegative identifiers.
--
--   **Formalization Note** Ports are 0-based (`Fin (deg v)`), so the printed port $k$ is the index $k-1$. Multigraphs are allowed, as the paper's own arguments use self-loops and parallel edges; every simple graph with every port numbering is an instance.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.6 (PDF p.8)

import Mathlib

namespace EulerianLE

/-- The port-numbered network of Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader
Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.6
(PDF p.8): "The network is a finite connected undirected Eulerian graph G = (V, E) … its ports
are numbered 1, 2, …, deg(u)".

**Formalization Note.** The ports of `v` are `Fin (deg v)`; print numbers them `1, …, deg v`, so
the printed port `k` is the index `k − 1`. An edge is a two-element orbit `{p, link p}` of the
fixed-point-free involution `link` on ports, so `link p` is the port at the other end of the edge
at `p`. This is a multigraph: self-loops (`(link p).1 = p.1`) and parallel edges are allowed, as the
paper's own proofs use them (proof of Lemma 23, p.38; proof of Lemma 32, p.43; App. B.1, p.33).
Every simple graph with every port numbering is an instance. -/
structure Network where
  /-- The nodes. -/
  V : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  /-- The degree of a node. -/
  deg : V → ℕ
  /-- The port at the other end of the edge at a port. -/
  link : (Σ v : V, Fin (deg v)) → (Σ v : V, Fin (deg v))
  link_involutive : Function.Involutive link
  link_ne : ∀ p, link p ≠ p

attribute [instance] Network.fintypeV Network.decEqV

/-- A port of the network: a node together with one of its port numbers. -/
abbrev Network.Port (G : Network) : Type := Σ v : G.V, Fin (G.deg v)

/-- `u` and `v` are joined by an edge. -/
def Network.Adjacent (G : Network) (u v : G.V) : Prop :=
  ∃ p : G.Port, p.1 = u ∧ (G.link p).1 = v

/-- "A finite connected undirected Eulerian graph", "Throughout, we assume |E| ≥ 1" (§2, p.6):
every degree is even, there is at least one port (hence an edge), and any two nodes are joined by
a path. -/
def Network.IsEulerian (G : Network) : Prop :=
  (∀ v, Even (G.deg v)) ∧ Nonempty G.Port ∧ ∀ u v, Relation.ReflTransGen G.Adjacent u v

/-- `|E|`, the number of edges: half the number of ports. -/
def Network.edgeCount (G : Network) : ℕ := Fintype.card G.Port / 2

/-- `IDmax`, the largest identifier (§2, p.6): `max_u ids u`. -/
def IDmax (G : Network) (ids : G.V → ℕ) : ℕ := Finset.univ.sup ids

end EulerianLE


