-- Prove2me | Definitions.Def_RunwayCPS_DiscreteTime_DTNetwork
-- name    : RunwayCPS_DiscreteTime_DTNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:32.977934+00:00
-- url     : https://prove2.me/theorems/80b0148f-58af-4f31-9d21-ffde2d6cbf78
-- title:
--   §6.1.2: the discrete-time CPS network of pairs (i, t) (Figure 3)
-- statement:
--   This file defines the discrete-time CPS network of §6.1.2 (Figure 3), used when separations satisfy the triangle inequality.
--
--   A node of stage $p$ is a pair $(i,t)$ with $i$ a stage-$p$ node of $G$ and $t\in\Gamma(i)$: node $i$ copied into layer $t$. There is an arc from $(i,t')$ at stage $p$ to $(j,t'')$ at stage $p+1$ when $(i,j)$ is an arc of $G$ and
--   $$
--   t''-t'\;\ge\;\delta_{\mathrm{fin}(i)\,\mathrm{fin}(j)} ,
--   $$
--   the minimum separation between the final aircraft of $i$ and of $j$. A source-sink path chooses one node per stage $1,\dots,n$ with arcs between consecutive stages.
--
--   Only consecutive aircraft are checked in this network, which suffices when the triangle inequality holds.
--
--   **Formalization Note** The separation condition is written $t'+\delta\le t''$ in $\mathbb N$.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1657, §6.1.2

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_Network

namespace RunwayCPS.DiscreteTime

variable {n : ℕ}

/-- A node `(i, t)` of the discrete-time CPS network of §6.1.2 (Figure 3): node `i` of `G` in
layer `t`. -/
structure TNode (n : ℕ) where
  node : List (Fin n)
  t : ℕ

/-- `(i, t)` is a node of stage `p` of the discrete-time CPS network (§6.1.2): `i` is a
stage-`p` node of `G` and `t ∈ Γ(i)`. -/
def IsTNode [NeZero n] (I : Instance n) (p : ℕ) (v : TNode n) : Prop :=
  IsGNode I p v.node ∧ v.t ∈ Gamma I v.node

/-- An arc from `(i, t')` at stage `p` to `(j, t'')` at stage `p + 1` (§6.1.2): `(i, j)` is an
arc of `G` and `t'' − t' ≥ δ_i(j)`, the minimum separation between `fin(i)` and `fin(j)`. -/
def IsTArc [NeZero n] (I : Instance n) (p : ℕ) (u v : TNode n) : Prop :=
  RunwayCPS.Makespan.IsArc I.k p u.node v.node ∧ u.t + I.δ (RunwayCPS.Makespan.final u.node) (RunwayCPS.Makespan.final v.node) ≤ v.t

/-- A source-sink path in the discrete-time CPS network: a node `P p` of stage `p` for every
`p = 1, …, n`, with an arc between consecutive stages (values outside `1, …, n` are
irrelevant). -/
def IsTPath [NeZero n] (I : Instance n) (P : ℕ → TNode n) : Prop :=
  (∀ p, 1 ≤ p → p ≤ n → IsTNode I p (P p)) ∧
  ∀ p, 1 ≤ p → p < n → IsTArc I p (P p) (P (p + 1))

end RunwayCPS.DiscreteTime


