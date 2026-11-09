-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_HistoryTree
-- name    : AnonymousDirectedCounting_Exact_HistoryTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:51.127867+00:00
-- url     : https://prove2.me/theorems/ce194a93-c48b-4dc7-a131-d2cc1c44e2d7
-- title:
--   History-tree nodes, vista levels, fibers, flatness and the flow equations
-- statement:
--   A node of a history tree at level $t\ge0$ is written as the vista below it: at level $0$ its leader status; at level $t+1$ the triple of its black parent, the outdegree label $d_{t+1}$ on the edge from that parent, and the multiset of level-$t$ tails of its red edges, in which a tail $u$ occurs $\mu_{t+1}(u,v)$ times. Here $\mu_{t+1}(u,v)$ counts the incoming arcs from $A(u)$ to one agent of $A(v)$.
--
--   The level $\mathcal L_r$ of the vista with bottom node $s$ is the set of level-$r$ nodes from which $s$ is reachable along black and red edges. A level $\mathcal L_{r}$ with $r\ge1$ is flat when each node of $\mathcal L_{r-1}$ has exactly one child in it, and $\mathcal L_0$ is flat when it has one node. For $b$ on level $r\ge1$, the visible flow equations and the leader equation are
--   $$
--   \sum_{v\in\mathcal L_r}\mu_r(u,v)\,b(v)=\sum_{w\text{ child of }u\text{ in }\mathcal L_r}d_r(w)\,b(w)\quad(u\in\mathcal L_{r-1}),\qquad
--   \sum_{v\text{ leader node in }\mathcal L_r}b(v)=\ell.
--   $$
--   All of this is read from the vista alone. The remaining definitions are semantic and are never protocol inputs: the node of an agent in the all-active execution of a network, the fiber $A(v)$ of a node, its anonymity $a(v)=|A(v)|$, the level $\mathcal H_r$ of the whole history tree, the levels of the round-$t$ vista of an agent, and fullness $\mathcal L_r=\mathcal H_r$.
--
--   **Formalization Note** Two agents have the same node exactly when they lie in one class of the source's partition $P_r$, so these values are vistas up to isomorphism. Level $-1$ has no entry; it is the unique ancestor of every node and nothing reads it. Multisets are mathematical objects here; the cost clause concerns a separate binary encoding.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Section 2, printed pp. 4–6 (PDF pp. 6–8)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_NetworkModel

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

open scoped Classical

noncomputable section

/-- A level-`t` node of a history tree, written as the unfolded vista below it: at level 0 its
leader status, at level `t + 1` its black parent, the outdegree label on that black edge, and the
multiset of level-`t` tails of its red edges (a tail occurs `μ` times for a red edge of
multiplicity `μ`). Equal values are exactly isomorphic vistas (printed p. 4, PDF p. 6). -/
def History : ℕ → Type
  | 0 => Bool
  | t + 1 => History t × ℕ × Multiset (History t)

/-- The level-0 leader node. -/
def leaderRoot : History 0 := (true : Bool)

/-- The level-0 nonleader node. -/
def nonleaderRoot : History 0 := (false : Bool)

/-- The black parent of a node. -/
def parent {r : ℕ} (v : History (r + 1)) : History r :=
  let p : History r × ℕ × Multiset (History r) := v
  p.1

/-- The outdegree `d_{r+1}(v)` labelling the black edge into `v`. -/
def outLabel {r : ℕ} (v : History (r + 1)) : ℕ :=
  let p : History r × ℕ × Multiset (History r) := v
  p.2.1

/-- The multiset of tails of red edges into `v`. -/
def redTails {r : ℕ} (v : History (r + 1)) : Multiset (History r) :=
  let p : History r × ℕ × Multiset (History r) := v
  p.2.2

/-- The red multiplicity `μ_{r+1}(u, v)`: incoming arcs from `A(u)` to ONE agent of `A(v)`. -/
def redMult {r : ℕ} (u : History r) (v : History (r + 1)) : ℕ :=
  (redTails v).count u

/-- Leader status of a node, inherited from its level-0 ancestor. -/
def isLeaderNode : {r : ℕ} → History r → Bool
  | 0, v => (v : Bool)
  | _ + 1, v => isLeaderNode (parent v)

/-- The black ancestor of a level-`t` node at level `r`, itself when `r = t`, `none` when `r > t`. -/
def blackAncestor : (t : ℕ) → History t → (r : ℕ) → Option (History r)
  | 0, v, 0 => some v
  | 0, _, _ + 1 => none
  | t + 1, v, r =>
    if hr : r = t + 1 then some (hr.symm ▸ v) else blackAncestor t (parent v) r

/-- `L_r` of the vista with bottom node `s` at level `t`: the nodes at level `r` from which `s` is
reachable along black and red edges. Empty for `r > t`. Level -1 (the root) has no entry; it is
the unique ancestor of every node and carries no data the test reads. -/
def vistaLevel : (t : ℕ) → History t → (r : ℕ) → Finset (History r)
  | 0, v, 0 => {v}
  | 0, _, _ + 1 => ∅
  | t + 1, v, r =>
    if hr : r = t + 1 then {hr.symm ▸ v}
    else vistaLevel t (parent v) r ∪
      (redTails v).toFinset.biUnion (fun u => vistaLevel t u r)

/-- The children of `u` in `L_{i+1}`. -/
def childrenIn {t : ℕ} (s : History t) (i : ℕ) (u : History i) : Finset (History (i + 1)) :=
  (vistaLevel t s (i + 1)).filter (fun v => parent v = u)

/-- `L_r` is flat when every node of `L_{r-1}` has exactly one child in `L_r` (printed p. 6,
PDF p. 8). At `r = 0` the only node of `L_{-1}` is the root, whose children are all of `L_0`. -/
def IsFlatLevel {t : ℕ} (s : History t) : ℕ → Prop
  | 0 => (vistaLevel t s 0).card = 1
  | i + 1 => ∀ u ∈ vistaLevel t s i, (childrenIn s i u).card = 1

/-- The flow equations on `L_r` with both sums restricted to visible nodes; one equation for each
`u ∈ L_{r-1}`. They exist only for `r ≥ 1`. -/
def VisibleFlow (K : Type) [Semiring K] {t : ℕ} (s : History t) :
    (r : ℕ) → (History r → K) → Prop
  | 0, _ => True
  | i + 1, b => ∀ u ∈ vistaLevel t s i,
      ∑ v ∈ vistaLevel t s (i + 1), (redMult u v : K) * b v =
        ∑ w ∈ childrenIn s i u, (outLabel w : K) * b w

/-- The flow equations on `L_r` together with the leader equation `∑_{leader v} b(v) = ell`. -/
def FlowSystem (K : Type) [Semiring K] (ell : ℕ) {t : ℕ} (s : History t) (r : ℕ)
    (b : History r → K) : Prop :=
  VisibleFlow K s r b ∧
    ∑ v ∈ (vistaLevel t s r).filter (fun v => isLeaderNode v = true), b v = (ell : K)

/-- The node of an agent in the all-active history tree: its leader status, then its old node,
current outdegree, and the multiset of old nodes of its in-neighbours, one per arc. -/
def history {n : ℕ} (G : NetworkModel n) : (t : ℕ) → Fin n → History t
  | 0, x => (decide (x ∈ G.leaders) : Bool)
  | t + 1, x =>
    ((history G t x, outdegree G (t + 1) x,
      ∑ y : Fin n, Multiset.replicate (G.arcs (t + 1) y x) (history G t y)) :
        History t × ℕ × Multiset (History t))

/-- The fiber `A(v)`: the agents the node represents. -/
def fiberOf {n : ℕ} (G : NetworkModel n) (r : ℕ) (v : History r) : Finset (Fin n) :=
  Finset.univ.filter (fun y => history G r y = v)

/-- The anonymity `a(v) = |A(v)|`. -/
def anonymity {n : ℕ} (G : NetworkModel n) (r : ℕ) (v : History r) : ℕ :=
  (fiberOf G r v).card

/-- `H_r`, the level of the whole history tree: one node per indistinguishability class. -/
def historyLevel {n : ℕ} (G : NetworkModel n) (r : ℕ) : Finset (History r) :=
  Finset.univ.image (history G r)

/-- `L_r` of the round-`t` vista of agent `x`. -/
def agentLevel {n : ℕ} (G : NetworkModel n) (t : ℕ) (x : Fin n) (r : ℕ) : Finset (History r) :=
  vistaLevel t (history G t x) r

/-- The union of the fibers of a set of level-`r` nodes. -/
def unionFibers {n : ℕ} (G : NetworkModel n) (r : ℕ) (A : Finset (History r)) : Finset (Fin n) :=
  A.biUnion (fiberOf G r)

/-- `L_r` is full: it contains every history-tree node of level `r`. -/
def IsFull {n : ℕ} (G : NetworkModel n) (t : ℕ) (x : Fin n) (r : ℕ) : Prop :=
  agentLevel G t x r = historyLevel G r

end

end AnonymousDirectedCounting.Exact


