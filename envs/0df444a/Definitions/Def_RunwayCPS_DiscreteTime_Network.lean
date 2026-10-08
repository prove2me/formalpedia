-- Prove2me | Definitions.Def_RunwayCPS_DiscreteTime_Network
-- name    : RunwayCPS_DiscreteTime_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:13.870206+00:00
-- url     : https://prove2.me/theorems/507bb2d2-aaed-4947-93ef-286ed85d748f
-- title:
--   §3, §3.1, §6.1.1: the CPS network, its precedence pruning G, source-sink paths, final and penultimate aircraft, and Γ(i)
-- statement:
--   This file defines the CPS network of §3 and its precedence-pruned version $G$ of §3.1.
--
--   **Nodes.** The network has stages $p=1,\dots,n$, one per position of the final sequence. A node of stage $p$ is a sequence of $\min\{2k+1,p\}$ pairwise distinct aircraft that occupies positions $p-\min\{2k+1,p\}+1,\dots,p$, each aircraft being within $k$ of its FCFS position at the position it occupies. The last aircraft of a node $i$ is its **final aircraft** $\mathrm{fin}(i)$; the second-to-last is its **penultimate aircraft**.
--
--   **Arcs.** An arc goes from a stage-$p$ node $i$ to a stage-$(p+1)$ node $j$ when the first $\min\{2k,p\}$ aircraft of $j$ are the last $\min\{2k,p\}$ aircraft of $i$. A **source-sink path** chooses one node per stage $1,\dots,n$ with arcs between consecutive stages; its sequence puts $\mathrm{fin}$ of the stage-$p$ node in position $p$.
--
--   **Precedence pruning.** For a precedence pair $(x,y)$ ($x$ before $y$), a node violates the pair if $y$ appears in it before $x$, or if it has $y$ at a position less than $x-k$, or $x$ at a position greater than $y+k$. The network $G$ keeps the nodes that violate no pair.
--
--   **Feasible times.** For a node $i$,
--   $$
--   \Gamma(i)=\{t\in\mathbb N : e_{\mathrm{fin}(i)}\le t\le l_{\mathrm{fin}(i)}\},
--   $$
--   the landing periods allowed by the time window of its final aircraft.
--
--   The network $G$ is the base of both discrete-time networks of the mission.
--
--   **Formalization Note** Stages are $1$-based; aircraft and positions $0$-based, so the position-rule thresholds $x-k$, $y+k$ are translation invariant. The pruning rule is the printed "i.e." clause of §3.1 (p. 1654), which is one weaker than the constraints stated just before it ($b-k+1$, $a+k-1$); both versions give the same source-sink paths. Nodes not reachable from the source or the sink are not removed (this does not change the set of source-sink paths). $\Gamma(i)$ is the full window, not the narrower set of §6.1.3, which relies on nondecreasing costs. `final` and `penult` are total functions with a default value that is used only on lists shorter than every node they are applied to (instance `NeZero n`).
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1652–1654, §3 and §3.1 (Cases I and II); p. 1657, §6.1.1 (the set of feasible times of node i)

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_Model
import Definitions.Def_RunwayCPS_Makespan_Network

namespace RunwayCPS.DiscreteTime

variable {n : ℕ}

/-- `w` is a node of stage `p` of the precedence-pruned CPS network `G` (§3, §3.1): a
stage-`p` node, with `1 ≤ p ≤ n`, that violates no precedence pair of the instance. -/
def IsGNode (I : Instance n) (p : ℕ) (w : List (Fin n)) : Prop :=
  1 ≤ p ∧ p ≤ n ∧ RunwayCPS.Makespan.IsStageNode I.k p w ∧ ∀ xy ∈ I.prec, ¬ RunwayCPS.Makespan.Violates I.k p xy.1 xy.2 w

instance (I : Instance n) (p : ℕ) : DecidablePred (IsGNode I p) := by
  intro w; unfold IsGNode; infer_instance

/-- A source-sink path in `G`: an assignment `v p` of a stage-`p` node of `G` to every stage
`p = 1, …, n`, with an arc of `G` between consecutive stages (values of `v` outside
`1, …, n` are irrelevant). The source and sink arcs always exist. -/
def IsGPath (I : Instance n) (v : ℕ → List (Fin n)) : Prop :=
  (∀ p, 1 ≤ p → p ≤ n → IsGNode I p (v p)) ∧
  ∀ p, 1 ≤ p → p < n → RunwayCPS.Makespan.IsArc I.k p (v p) (v (p + 1))

/-- The penultimate aircraft of a node: its second-to-last entry. Every node of stage `p ≥ 2`
has at least two entries when `k ≥ 1`, so the default value is never used on such a node. -/
def penult [NeZero n] (w : List (Fin n)) : Fin n :=
  w.dropLast.getLastD default

/-- `Γ(i)` (§6.1.1): the set of feasible landing periods of the final aircraft of node `i`,
generated from its time window, `{t ∈ ℕ | e_{fin(i)} ≤ t ≤ l_{fin(i)}}`. -/
def Gamma [NeZero n] (I : Instance n) (i : List (Fin n)) : Finset ℕ :=
  Finset.Icc (I.e (RunwayCPS.Makespan.final i)) (I.l (RunwayCPS.Makespan.final i))

end RunwayCPS.DiscreteTime


