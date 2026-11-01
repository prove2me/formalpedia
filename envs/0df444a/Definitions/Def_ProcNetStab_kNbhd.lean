-- Prove2me | Definitions.Def_ProcNetStab_kNbhd
-- name    : ProcNetStab_kNbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:08.385495+00:00
-- url     : https://prove2.me/theorems/41989767-7b01-413b-8c1f-4123e62f34d6
-- title:
--   $k$-neighborhood $N^k_i(h)$ of an agent
-- statement:
--   Let $h$ be a network on the node set $V$, $i \in V$ and $k \in \mathbb N$. The **$k$-ball** of $i$ in $h$ is the set of agents no more than $k$ links away from $i$,
--   $$
--   B^k_i(h) = \{ v \in V : d_h(i, v) \le k \},
--   $$
--   where $d_h(i, v) \in \mathbb N \cup \{\infty\}$ is the length of a shortest path from $i$ to $v$ in $h$ ($\infty$ if there is none). The **$k$-neighborhood** $N^k_i(h)$ is the subgraph of $h$ induced on $B^k_i(h)$: its nodes are the agents of the ball, and its links are all links of $h$ between them.
--
--   The $k$-neighborhood is the local network structure that an agent is assumed to care about.
--
--   **Formalization Note** The distance is Mathlib's extended distance `SimpleGraph.edist` (valued in `ℕ∞`), so nodes in other components are never in the ball. The neighborhood is `h.induce (ball h k i)`. The module also records the structural fact that $i$ lies in its own ball.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definition 3.6, p.9

import Mathlib

namespace ProcNetStab

/-- The set of agents no more than `k` links away from agent `i` in the network `h`
(Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript, 2025), Definition 3.6, p.9).

**Formalization Note** The distance is the extended graph distance `SimpleGraph.edist`, which is
`⊤` between nodes in different components; so the ball contains exactly the nodes joined to `i`
by a path of at most `k` links. (`SimpleGraph.dist` would be `0` between unreachable nodes and
is not used.) -/
def ball {V : Type*} (h : SimpleGraph V) (k : ℕ) (i : V) : Set V :=
  {v | h.edist i v ≤ (k : ℕ∞)}

/-- The **`k`-neighborhood** `N^k_i(h)` of agent `i` in network `h` (Chiong, Qi, *Stability of
Procurement Networks* (authors' manuscript, 2025), Definition 3.6, p.9): the subgraph of `h`
consisting of all agents no more than `k` links away from `i`, and all links of `h` between them.

**Formalization Note** It is the induced subgraph `h.induce (ball h k i)`, a simple graph on the
subtype `ball h k i`. -/
def kNbhd {V : Type*} (h : SimpleGraph V) (k : ℕ) (i : V) : SimpleGraph (ball h k i) :=
  h.induce (ball h k i)

/-- The root `i` lies in its own `k`-ball. -/
theorem mem_ball_self {V : Type*} (h : SimpleGraph V) (k : ℕ) (i : V) : i ∈ ball h k i := by
  simp [ball]

end ProcNetStab


