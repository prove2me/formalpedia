-- Prove2me | Definitions.Def_FordFulkerson58_ArcChain_Labeling
-- name    : FordFulkerson58_ArcChain_Labeling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:15:13.384445+00:00
-- url     : https://prove2.me/theorems/89dcd189-a17f-4f92-9e2f-0f2242b2df2b
-- title:
--   §3, p. 1780 — chain lengths, the labeling process (initial labels 0/∞, improving-arc replacements), terminal labelings, shortest-chain lengths
-- statement:
--   Let $N$ be a network with arc lengths $l_e \in \mathbb{R}$, and let $S$ be a set of nodes. The **length** of a set of arcs $C$ is $\sum_{e\in C} l_e$.
--
--   The **labeling process** of §3 assigns to each node $P_i$ a label $\pi_i \in \mathbb{R}\cup\{\infty\}$. Initially
--   $$\pi_i = \begin{cases} 0 & \text{for } P_i \in S,\\ \infty & \text{otherwise.}\end{cases}$$
--   A **step** finds an arc $e$ that can be traversed from $P_i$ to $P_j$ with $\pi_i + l_e < \pi_j$ and replaces $\pi_j$ by $\pi_i + l_e$. A labeling is **terminal** when no such arc exists, i.e. $\pi_j \le \pi_i + l_e$ for every arc $e$ traversable from $P_i$ to $P_j$.
--
--   The **shortest-chain length** from $S$ to a node $v$ is the minimum of the lengths of all chains from $S$ to $v$, and $\infty$ if there is none; the shortest-chain length from $S$ to a set $T$ is the minimum over all chains from $S$ to a node of $T$.
--
--   These are the objects of Ford's shortest chain algorithm, which §3 uses to price the columns of the arc-chain program.
--
--   **Formalization Note** Labels take values in `WithTop ℝ`, with `⊤` for $\infty$, so $\infty + l = \infty$ and no step starts from an unlabeled node. The process scans arcs, not node pairs (`Traverses N e u v`): an undirected arc gives both traversals with the same length, which is the page's $l_{ij} = l_{ji}$, and parallel arcs are handled because the best one wins. The page's labels $\pi_i$ are called `lab` in Lean. Shortest-chain lengths are `Finset.inf` over the finite set of arc sets, so no real infimum of an empty or unbounded set occurs.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), p. 1780, §3, the labeling process

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network

namespace FordFulkerson58.ArcChain

variable {V E ι : Type*}

/-- The length of a set of arcs `C` under the arc lengths `l`: `∑_{e ∈ C} l e`. -/
def chainLength (l : E → ℝ) (C : Finset E) : ℝ :=
  ∑ e ∈ C, l e

/-- The initial labels of the labeling process (§3, p. 1780): `0` on the source set `S`, `∞` (`⊤`)
elsewhere. -/
def initLabel [DecidableEq V] (S : Finset V) : V → WithTop ℝ :=
  fun v => if v ∈ S then 0 else ⊤

/-- One step of the labeling process (§3, p. 1780): an arc `e` traversable from `u` to `v` with
`lab u + l e < lab v` is found, and the label of `v` is replaced by `lab u + l e`. -/
def RelaxStep [DecidableEq V] (N : Network V E ι) (l : E → ℝ) (lab lab' : V → WithTop ℝ) : Prop :=
  ∃ (e : E) (u v : V), Traverses N e u v ∧ lab u + (l e : WithTop ℝ) < lab v ∧
    lab' = Function.update lab v (lab u + (l e : WithTop ℝ))

/-- A labeling is terminal when no arc can improve it: for every arc `e` traversable from `u` to `v`,
`lab v ≤ lab u + l e`. -/
def IsTerminal (N : Network V E ι) (l : E → ℝ) (lab : V → WithTop ℝ) : Prop :=
  ∀ (e : E) (u v : V), Traverses N e u v → lab v ≤ lab u + (l e : WithTop ℝ)

/-- The length of a shortest chain from the set `S` to the node `v`: the minimum of `chainLength l C`
over all chains `C` from `S` to `v`, and `⊤` (∞) if there is none. -/
noncomputable def shortestChainLength [Fintype E] [DecidableEq E] (N : Network V E ι) (l : E → ℝ) (S : Finset V)
    (v : V) : WithTop ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset E)).filter (fun C => IsChainFrom N S v C)).inf
    (fun C => ((chainLength l C : ℝ) : WithTop ℝ))

/-- The length of a shortest chain from the set `S` to the set `T`: the minimum of `chainLength l C`
over all chains `C` from `S` to some node of `T`, and `⊤` (∞) if there is none. -/
noncomputable def shortestChainLengthTo [Fintype E] [DecidableEq E] (N : Network V E ι) (l : E → ℝ)
    (S T : Finset V) : WithTop ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset E)).filter (fun C => ∃ t ∈ T, IsChainFrom N S t C)).inf
    (fun C => ((chainLength l C : ℝ) : WithTop ℝ))

end FordFulkerson58.ArcChain


