-- Prove2me | Definitions.Def_PacketRouting_CongDil_Network
-- name    : PacketRouting_CongDil_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:44:29.265627+00:00
-- url     : https://prove2.me/theorems/ed48879f-75db-4e1d-afd9-14bca7c200b1
-- title:
--   §1, pp. 2–3, 7 — edge-simple paths, congestion and dilation of a set of packets
-- statement:
--   This module fixes the network model of Leighton, Maggs and Rao for store-and-forward packet routing.
--
--   A **network** is a directed multigraph: a type $V$ of nodes, a type $E$ of edges, and maps $\mathrm{src},\mathrm{tgt}:E\to V$ giving the tail and the head of each edge (antiparallel wires are two different edges, as in Figure 1). No finiteness, degree bound or topology is assumed. A **path** is a finite list of edges $e_0,e_1,\dots,e_{\ell-1}$ in which each edge starts where the previous one ends,
--   $$
--   \mathrm{tgt}(e_k)=\mathrm{src}(e_{k+1})\qquad(0\le k<\ell-1).
--   $$
--   The path is **edge-simple** if it uses no edge more than once (p. 7, footnote 1). The empty path is allowed: it is the path of a packet whose origin is its destination.
--
--   A set of packets is a finite set $P$, each packet $p$ carrying its path $\mathrm{path}(p)$. Following p. 3:
--
--   1. the paths have **congestion at most $c$** if every edge lies on the paths of at most $c$ packets;
--   2. the paths have **dilation at most $d$** if every path has at most $d$ edges.
--
--   The congestion $c$ and the dilation $d$ of the paper are the least such bounds; both are lower bounds on the length of any schedule, and they are the two parameters of the paper's main theorem.
--
--   **Formalization Note** Congestion and dilation are encoded as bound predicates (`CongestionLE path c`, `DilationLE path d`). Because every bound in the paper is monotone in $c$ and $d$, a statement quantified over all bounds is equivalent to the same statement at the exact values.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), pp. 2–3 (model, congestion, dilation) and p. 7, footnote 1 (edge-simple)

import Mathlib

namespace PacketRouting.CongDil

/-- A path in a directed network with edge type `E`, vertex type `V` and endpoint maps
`src tgt : E → V` (Leighton–Maggs–Rao, pp. 2–3, Figure 1) is **edge-simple** (p. 7, footnote 1:
"An edge-simple path uses no edge more than once") if it is a list of edges in which each edge
starts where the previous one ends, `tgt eₖ = src eₖ₊₁`, and no edge occurs twice.
The empty list is the path of a packet whose origin is its destination. -/
def IsEdgeSimplePath {V E : Type*} (src tgt : E → V) (l : List E) : Prop :=
  List.IsChain (fun e f => tgt e = src f) l ∧ l.Nodup

/-- The paths of a set of packets `P` have **congestion at most `c`** (p. 3: "the largest number
of packets that must traverse a single edge during the entire course of the routing"): for every
edge `e`, at most `c` packets have `e` on their path. -/
def CongestionLE {P E : Type*} [Fintype P] (path : P → List E) (c : ℕ) : Prop := by
  classical
  exact ∀ e : E, (Finset.univ.filter (fun p : P => e ∈ path p)).card ≤ c

/-- The paths of a set of packets have **dilation at most `d`** (p. 3: "the maximum distance,
`d`, traveled by any packet"): every path has at most `d` edges. -/
def DilationLE {P E : Type*} (path : P → List E) (d : ℕ) : Prop :=
  ∀ p : P, (path p).length ≤ d

end PacketRouting.CongDil


