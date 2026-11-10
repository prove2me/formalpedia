-- Prove2me | Definitions.Def_DistancePreserver934_Exact_Preservers
-- name    : DistancePreserver934_Exact_Preservers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:16.594432+00:00
-- url     : https://prove2.me/theorems/a208cb5c-b26e-4350-a11d-923b837c5b41
-- title:
--   §3 — graphs, distances, distance preservers, minimality, balls, diameters
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple undirected unweighted graph on a finite vertex type $V$, and a subgraph $H\le G$ keeps all vertices of $V$ (a spanning subgraph, $E_H\subseteq E$). The distance $\operatorname{dist}_H(u,v)\in\mathbb N\cup\{\infty\}$ is the length of a shortest $u$–$v$ walk in $H$, and $\infty$ if $u,v$ lie in different components. $|E(H)|$ counts unordered edges once.
--
--   1. A **demand set** (§3) is a finite set $R$ of unordered pairs $\{s,t\}$ with $s\neq t$ and $s,t$ connected in $G$ (the paper's standing assumption "demands are reachable between two distinct vertices").
--   2. $H$ is a **distance preserver** of $(G,R)$ if $H\le G$ and
--   $$\operatorname{dist}_H(s,t)=\operatorname{dist}_G(s,t)\qquad(\{s,t\}\in R).$$
--   3. A distance preserver $H$ is **minimal** if for every edge $e\in E_H$ the graph $(V,E_H\setminus\{e\})$ is not a distance preserver of $(G,R)$. This is inclusion-minimality, not minimum size.
--   4. For a real radius $a$, the closed ball is $B_H(x,a)=\{v:\operatorname{dist}_H(x,v)\le a\}$; it contains only vertices at finite distance from $x$, and contains $x$ when $a\ge0$.
--   5. $\operatorname{diam}_H(S)=\sup_{x,y\in S}\operatorname{dist}_H(x,y)\in\mathbb N\cup\{\infty\}$ (equal to $0$ for $|S|\le1$), and "$\operatorname{diam}_H(S)\le D$" for real $D$ means the diameter is finite and at most $D$.
--   6. $E_H^U$ is the set of edges of $H$ with both endpoints in $U$, the edge set of the induced subgraph $H[U]$.
--
--   These are the objects of §3 shared by every statement of the mission.
--
--   **Formalization Note** Distances are Mathlib's `SimpleGraph.edist` with values in $\mathbb N_\infty$, so an unreachable pair has distance $\infty$ rather than a default $0$. Demands are elements of `Sym2 V`; the ordered demands of the introduction are used only in Theorem 1.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, §3 Preliminaries (graphs, demand sets, minimal distance preservers, balls, diameters), printed p. 8 (PDF p. 9); and §1, printed p. 2 (PDF p. 3), definition of a distance preserver

import Mathlib

namespace DistancePreserver934.Exact

open Classical

variable {V : Type} [Fintype V]

/-- The edges of a graph `H` on the finite vertex type `V`, each unordered edge once. -/
noncomputable def edgesF (H : SimpleGraph V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => e ∈ H.edgeSet)

/-- `|E(H)|`, the number of (unordered) edges of `H`. -/
noncomputable def numEdges (H : SimpleGraph V) : ℕ := (edgesF H).card

/-- A demand set in the sense of §3: unordered pairs of distinct vertices that are reachable
in `G` (the paper's standing assumption "demands are reachable between two distinct
vertices"). -/
def IsDemandSet (G : SimpleGraph V) (R : Finset (Sym2 V)) : Prop :=
  ∀ s t : V, s(s, t) ∈ R → s ≠ t ∧ G.Reachable s t

/-- `H` is a distance preserver of `(G, R)`: a spanning subgraph of `G` (same vertex set) such
that `dist_H(s,t) = dist_G(s,t)` for every demand `{s,t} ∈ R`.  Distances are Mathlib's
`SimpleGraph.edist` (length of a shortest walk, `⊤` if unreachable). -/
def IsPreserver (G H : SimpleGraph V) (R : Finset (Sym2 V)) : Prop :=
  H ≤ G ∧ ∀ s t : V, s(s, t) ∈ R → H.edist s t = G.edist s t

/-- `H` is a minimal distance preserver of `(G, R)` (§3): a distance preserver such that deleting
any single edge of `H` yields a subgraph that is not a distance preserver of `(G, R)`.
(Inclusion-minimality, not minimum size.) -/
def IsMinimalPreserver (G H : SimpleGraph V) (R : Finset (Sym2 V)) : Prop :=
  IsPreserver G H R ∧ ∀ e ∈ H.edgeSet, ¬ IsPreserver G (H.deleteEdges {e}) R

/-- The closed ball `B_H(x, a) = {v : dist_H(x, v) ≤ a}` for a real radius `a`; only vertices at
finite distance from `x` belong to it. -/
noncomputable def ball (H : SimpleGraph V) (x : V) (a : ℝ) : Finset V :=
  Finset.univ.filter (fun v => ∃ k : ℕ, H.edist x v = (k : ℕ∞) ∧ (k : ℝ) ≤ a)

/-- The diameter `diam_H(S) = sup_{x,y ∈ S} dist_H(x,y)` in `ℕ∞` (`⊤` if two vertices of `S` are
not connected in `H`; `0` for empty or singleton `S`). -/
noncomputable def diam (H : SimpleGraph V) (S : Finset V) : ℕ∞ :=
  ⨆ x ∈ S, ⨆ y ∈ S, H.edist x y

/-- `diam_H(S) ≤ D` for a real bound `D`: the diameter is finite and at most `D`. -/
def DiamLE (H : SimpleGraph V) (S : Finset V) (D : ℝ) : Prop :=
  diam H S ≠ ⊤ ∧ ((diam H S).toNat : ℝ) ≤ D

/-- The edges of `H` with both endpoints in `U`, i.e. `E_H^U`, the edge set of `H[U]`. -/
noncomputable def inducedEdges (H : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) :=
  (edgesF H).filter (fun e => ∀ v ∈ e, v ∈ U)

end DistancePreserver934.Exact


