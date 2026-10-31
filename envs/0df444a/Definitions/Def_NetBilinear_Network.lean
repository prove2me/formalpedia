-- Prove2me | Definitions.Def_NetBilinear_Network
-- name    : NetBilinear_Network
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:10.611867+00:00
-- url     : https://prove2.me/theorems/ea955f6a-1013-4d99-ae01-526a1d00ef6c
-- title:
--   Networks $G=(V,A)$, the undirected variant $\bar G$, and the flow-balance rows $i^{\pm}$
-- statement:
--   A **network** $G=(V,A)$ consists of a node type $V$, an arc type $A$, and for every arc $k$ its tail $t(k)$ and head $h(k)$, with $t(k)\neq h(k)$ (no self-loops). Several arcs may join the same pair of nodes.
--
--   1. The **undirected variant** $\bar G$ is the graph on $V$ in which distinct nodes $u,v$ are adjacent when some arc goes from $u$ to $v$ or from $v$ to $u$.
--   2. The flow-balance constraint at node $i$ is split into the **positive** inequality $\sum_{k\in\delta^+(i)}x_k-\sum_{k\in\delta^-(i)}x_k\ge f_i$ (row $i^+$) and the **negative** inequality $-\sum_{k\in\delta^+(i)}x_k+\sum_{k\in\delta^-(i)}x_k\ge -f_i$ (row $i^-$). The coefficient of $x_k$ in row $i^s$ is
--   $$E_{i^s,k}=s\,\big([t(k)=i]-[h(k)=i]\big),\qquad s\in\{+1,-1\}.$$
--   3. For a sign $s$ and a node set $X$, $\{i^s\}_{i\in X}$ is the set of rows $i^s$, $i\in X$.
--
--   These are the rows of the augmented node-arc incidence matrix $E$ describing the network polytope $\Xi=\{x: Ex\ge f,\ 0\le x\le u\}$, and the objects in which Theorem 2's assignments are written.
--
--   **Formalization Note** Rows are pairs `V × Sign`; `Sign.toReal` maps $+\mapsto1$, $-\mapsto-1$, and `Sign.flip` is the opposite sign. $\bar G$ is a `SimpleGraph` (parallel arcs collapse to one edge). The supplies $f$ and capacities $u$ do not enter the EC&R conditions and are not part of the structure.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, §3, p.4 (augmented node-arc incidence matrix); §3.1, p.6 (network G = (V,A), t(k), h(k), positive/negative flow-balance inequalities i+, i−, undirected variant P̄)

import Mathlib

namespace NetBilinear

/-- **A network `G = (V, A)`: nodes, arcs, and the tail and head of each arc.**
Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, §3, p.4 ("Ξ represents a network polytope … E is an augmented node-arc
incidence matrix") and §3.1, p.6 ("Given a network G = (V,A) with a node set V and arc set A
… We define t(k) and h(k) to be the tail and head nodes of arc k ∈ A").

A network has a node type `V` and an arc type `A`; arc `k` goes from `tail k = t(k)` to
`head k = h(k)`.

**Formalization Note.** Arcs are elements of a type with tail and head maps, so several arcs
may join the same pair of nodes (parallel arcs are allowed, as the paper never excludes them).
Finiteness of `V` and `A` is assumed where it is used (`Fintype`), not bundled here. The field
`loopless` excludes self-loops: a node-arc incidence matrix (p.4) has no self-loop column, and
Theorem 2 fails for a self-loop (see the goal's Differences). The supplies `f`, capacities `u`
and the variables `z` do not enter the EC&R conditions and are not fields. -/
structure Network (V A : Type*) where
  /-- `t(k)`, the tail node of arc `k`. -/
  tail : A → V
  /-- `h(k)`, the head node of arc `k`. -/
  head : A → V
  /-- No arc is a self-loop. -/
  loopless : ∀ k, tail k ≠ head k

/-- **The sign `+` / `−` of a flow-balance inequality, and of a class `l±`.**
arXiv:2302.14151v2, §2, p.3, Step 1 ("a sign indicator + or − to indicate whether a weight 1
or −1 is used for the base equality") and §3.1, p.6 ("positive (resp. negative) flow-balance
inequality … its index … by i+ (resp. i−)"). -/
inductive Sign
  | pos
  | neg
  deriving DecidableEq

/-- `+ ↦ 1`, `− ↦ −1`. -/
def Sign.toReal : Sign → ℝ
  | .pos => 1
  | .neg => -1

/-- The opposite sign. -/
def Sign.flip : Sign → Sign
  | .pos => .neg
  | .neg => .pos

namespace Network

variable {V A : Type*}

/-- **`Ḡ`, the undirected variant of the network.**
arXiv:2302.14151v2, §3.1, p.6 ("we denote the undirected variant of a subnetwork P of G by P̄").
Two distinct nodes are adjacent in `Ḡ` when some arc joins them, in either direction.

**Formalization Note.** `Ḡ` is a `SimpleGraph`: parallel arcs (or two opposite arcs) between
`u` and `v` give one edge. A subgraph of the multigraph `Ḡ` on node set `Ĩ` is a tree iff some
tree on `Ĩ` exists in this simple collapse, so "a tree in `Ḡ` with node set `Ĩ`" has the same
instances. -/
def underlying (G : Network V A) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ k, G.tail k = u ∧ G.head k = v

/-- **The rows `E_{i±,·}` of the augmented node-arc incidence matrix.**
arXiv:2302.14151v2, §3, p.4 ("E is an augmented node-arc incidence matrix where each row is
duplicated with a negative sign") and §3.1, p.6: the positive flow-balance inequality at node
`i` is `Σ_{k∈δ⁺(i)} x_k − Σ_{k∈δ⁻(i)} x_k ≥ f_i` (index `i⁺`), the negative one is
`−Σ_{k∈δ⁺(i)} x_k + Σ_{k∈δ⁻(i)} x_k ≥ −f_i` (index `i⁻`).

`incRow G (i, s) k = s · ([t(k) = i] − [h(k) = i])` is the coefficient of `x_k` in the row
`i^s`, with `s = +` ↦ `1`, `s = −` ↦ `−1`.

**Formalization Note.** The rows (the non-bound constraints of `Ξ`, the index set `T` of p.3)
are the pairs `V × Sign`. -/
def incRow [DecidableEq V] (G : Network V A) (t : V × Sign) (k : A) : ℝ :=
  t.2.toReal * ((if G.tail k = t.1 then 1 else 0) - (if G.head k = t.1 then 1 else 0))

end Network

/-- **The row set `{i^s}_{i ∈ X}`.**
arXiv:2302.14151v2, Theorem 2, p.7: the assignments `[{i+}_{i∈Ĩ1}, {i−}_{i∈Ĩ2}]` and their
variants. `rowsWith s X` is the set of rows `(i, s)` for `i ∈ X`. -/
def rowsWith {V : Type*} [DecidableEq V] (s : Sign) (X : Finset V) : Finset (V × Sign) :=
  X.image fun i => (i, s)

end NetBilinear


